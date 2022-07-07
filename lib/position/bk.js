"use strict";

var _ = require("../lodash"),
    util = require("../util");

/*
 * This module provides coordinate assignment based on Brandes and Köpf, "Fast
 * and Simple Horizontal Coordinate Assignment."
 */

module.exports = {
  positionX: positionX,
  findType1Conflicts: findType1Conflicts,
  findType2Conflicts: findType2Conflicts,
  addConflict: addConflict,
  hasConflict: hasConflict,
  verticalAlignment: verticalAlignment,
  horizontalCompaction: horizontalCompaction,
  alignCoordinates: alignCoordinates,
  findSmallestWidthAlignment: findSmallestWidthAlignment,
  balance: balance
};

/*
 * Marks all edges in the graph with a type-1 conflict with the "type1Conflict"
 * property. A type-1 conflict is one where a non-inner segment crosses an
 * inner segment. An inner segment is an edge with both incident nodes marked
 * with the "dummy" property.
 *
 * This algorithm scans layer by layer, starting with the second, for type-1
 * conflicts between the current layer and the previous layer. For each layer
 * it scans the nodes from left to right until it reaches one that is incident
 * on an inner segment. It then scans predecessors to determine if they have
 * edges that cross that inner segment. At the end a final scan is done for all
 * nodes on the current rank to see if they cross the last visited inner
 * segment.
 *
 * This algorithm (safely) assumes that a dummy node will only be incident on a
 * single node in the layers being scanned.
 */
function findType1Conflicts(g, layering) {
  var conflicts = {};

  function visitLayer(prevLayer, layer) {
    var
      // last visited node in the previous layer that is incident on an inner
      // segment.
      k0 = 0,
      // Tracks the last node in this layer scanned for crossings with a type-1
      // segment.
      scanPos = 0,
      prevLayerLength = prevLayer.length,
      lastNode = _.last(layer);

    _.each(layer, function(v, i) {
      var w = findOtherInnerSegmentNode(g, v),
          k1 = w ? g.node(w).order : prevLayerLength;

      if (w || v === lastNode) {
        _.each(layer.slice(scanPos, i +1), function(scanNode) {
          _.each(g.predecessors(scanNode), function(u) {
            var uLabel = g.node(u),
                uPos = uLabel.order;
            if ((uPos < k0 || k1 < uPos) &&
                !(uLabel.dummy && g.node(scanNode).dummy)) {
              addConflict(conflicts, u, scanNode);
            }
          });
        });
        scanPos = i + 1;
        k0 = k1;
      }
    });

    return layer;
  }

  _.reduce(layering, visitLayer);
  return conflicts;
}

function findType2Conflicts(g, layering) {
  var conflicts = {};

  function scan(south, southPos, southEnd, prevNorthBorder, nextNorthBorder) {
    var v;
    _.each(_.range(southPos, southEnd), function(i) {
      v = south[i];
      if (g.node(v).dummy) {
        _.each(g.predecessors(v), function(u) {
          var uNode = g.node(u);
          if (uNode.dummy &&
              (uNode.order < prevNorthBorder || uNode.order > nextNorthBorder)) {
            addConflict(conflicts, u, v);
          }
        });
      }
    });
  }


  function visitLayer(north, south) {
    var prevNorthPos = -1,
        nextNorthPos,
        southPos = 0;

    _.each(south, function(v, southLookahead) {
      if (g.node(v).dummy === "border") {
        var predecessors = g.predecessors(v);
        if (predecessors.length) {
          nextNorthPos = g.node(predecessors[0]).order;
          scan(south, southPos, southLookahead, prevNorthPos, nextNorthPos);
          southPos = southLookahead;
          prevNorthPos = nextNorthPos;
        }
      }
      scan(south, southPos, south.length, nextNorthPos, north.length);
    });

    return south;
  }

  _.reduce(layering, visitLayer);
  return conflicts;
}

function findOtherInnerSegmentNode(g, v) {
  if (g.node(v).dummy) {
    return _.find(g.predecessors(v), function(u) {
      return g.node(u).dummy;
    });
  }
}

function addConflict(conflicts, v, w) {
  if (v > w) {
    var tmp = v;
    v = w;
    w = tmp;
  }

  var conflictsV = conflicts[v];
  if (!conflictsV) {
    conflicts[v] = conflictsV = {};
  }
  conflictsV[w] = true;
}

function hasConflict(conflicts, v, w) {
  if (v > w) {
    var tmp = v;
    v = w;
    w = tmp;
  }
  return _.has(conflicts[v], w);
}

/*
 * Try to align nodes into vertical "blocks" where possible. This algorithm
 * attempts to align a node with one of its median neighbors. If the edge
 * connecting a neighbor is a type-1 conflict then we ignore that possibility.
 * If a previous node has already formed a block with a node after the node
 * we're trying to form a block with, we also ignore that possibility - our
 * blocks would be split in that scenario.
 */
function verticalAlignment(g, layering, conflicts, neighborFn) {
  var root = {},
      align = {},
      pos = {};

  // We cache the position here based on the layering because the graph and
  // layering may be out of sync. The layering matrix is manipulated to
  // generate different extreme alignments.
  _.each(layering, function(layer) {
    _.each(layer, function(v, order) {
      root[v] = v;
      align[v] = v;
      pos[v] = order;
    });
  });

  _.each(layering, function(layer) {
    var prevIdx = -1;
    _.each(layer, function(v) {
      var ws = neighborFn(v);
      if (ws.length) {
        ws = _.sortBy(ws, function(w) { return pos[w]; });
        var mp = (ws.length - 1) / 2;
        for (var i = Math.floor(mp), il = Math.ceil(mp); i <= il; ++i) {
          var w = ws[i];
          if (align[v] === v &&
              prevIdx < pos[w] &&
              !hasConflict(conflicts, v, w)) {
            align[w] = v;
            align[v] = root[v] = root[w];
            prevIdx = pos[w];
          }
        }
      }
    });
  });

  return { root: root, align: align };
}

function horizontalCompaction(g, layering, root, align, reverseSep) {
  // We use local variables for these parameters instead of manipulating the
  // graph because it becomes more verbose to access them in a chained manner.
  var shift = {},
      shiftNeighbor = {},
      sink = {},
      xs = {},
      pred = {},
      graphLabel = g.graph(),
      sepFn = sep(graphLabel.nodesep, graphLabel.edgesep, reverseSep);

  _.each(layering, function(layer) {
    _.each(layer, function(v, order) {
      sink[v] = v;
      shift[v] = Number.POSITIVE_INFINITY;
      pred[v] = layer[order - 1];
    });
  });

  _.each(g.nodes(), function(v) {
    if (root[v] === v) {
      placeBlock(g, layering, sepFn, root, align, shift, shiftNeighbor, sink, pred, xs, v);
    }
  });

  _.each(layering, function(layer) {
    _.each(layer, function(v) {
      xs[v] = xs[root[v]];
      // This line differs from the source paper. See
      // http://www.inf.uni-konstanz.de/~brandes/publications/ for details.
      if (v === root[v] && shift[sink[root[v]]] < Number.POSITIVE_INFINITY) {
        xs[v] += shift[sink[root[v]]];

        // Cascade shifts as necessary
        var w = shiftNeighbor[sink[root[v]]];
        if (w && shift[w] !== Number.POSITIVE_INFINITY) {
          xs[v] += shift[w];
        }
      }
    });
  });

  return xs;
}

function placeBlock(g, layering, sepFn, root, align, shift, shiftNeighbor, sink, pred, xs, v) {
  if (_.has(xs, v)) return;
  xs[v] = 0;

  var w = v,
      u;
  do {
    if (pred[w]) {
      u = root[pred[w]];
      placeBlock(g, layering, sepFn, root, align, shift, shiftNeighbor, sink, pred, xs, u);
      if (sink[v] === v) {
        sink[v] = sink[u];
      }

      var delta = sepFn(g, w, pred[w]);
      if (sink[v] !== sink[u]) {
        shift[sink[u]] = Math.min(shift[sink[u]], xs[v] - xs[u] - delta);
        shiftNeighbor[sink[u]] = sink[v];
      } else {
        xs[v] = Math.max(xs[v], xs[u] + delta);
      }
    }
    w = align[w];
  } while (w !== v);
}

/*
 * Returns the alignment that has the smallest width of the given alignments.
 */
function findSmallestWidthAlignment(g, xss) {
  return _.min(xss, function(xs) {
    var min = _.min(xs, function(x, v) { return x - width(g, v) / 2; }),
        max = _.max(xs, function(x, v) { return x + width(g, v) / 2; });
    return max - min;
  });
}

/*
 * Align the coordinates of each of the layout alignments such that
 * left-biased alignments have their minimum coordinate at the same point as
 * the minimum coordinate of the smallest width alignment and right-biased
 * alignments have their maximum coordinate at the same point as the maximum
 * coordinate of the smallest width alignment.
 */
function alignCoordinates(xss, alignTo) {
  var alignToMin = _.min(alignTo),
      alignToMax = _.max(alignTo);

  _.each(["u", "d"], function(vert) {
    _.each(["l", "r"], function(horiz) {
      var alignment = vert + horiz,
          xs = xss[alignment],
          delta;
      if (xs === alignTo) return;

      delta = horiz === "l" ? alignToMin - _.min(xs) : alignToMax - _.max(xs);

      if (delta) {
        xss[alignment] = _.mapValues(xs, function(x) { return x + delta; });
      }
    });
  });
}

function balance(xss, align, layering, g) {
  const originalBalanced = _.mapValues(xss.ul, function(ignore, v) {
    if (align) {
      return xss[align.toLowerCase()][v];
    } else {
      var xs = _.sortBy(Object.values(xss).map(dir => dir[v]));
      return (xs[1] + xs[2]) / 2;
    }
  });

  //
  // BEGIN Knotend overrides
  //

  // Transform positions into discrete values for knotend
  const balanced = Object.fromEntries(
    Object.entries(originalBalanced).map(([nodeId, position]) => {
      return [nodeId, Math.floor(position)];
    })
  );

  // Node overlap detection and correction
  // Note that this was not part of the original bk.js defined by dagre, Scott added this
  // to overcome issues with collision like: https://github.com/dagrejs/dagre/issues/158 
  //
  // The approach here is to look at one rank at a time and
  // see if within that rank there are nodes that have equal order (position in 'balanced').
  // If there are, we need to change their position. To do this we iteratively move nodes
  // further away in the opposite direction of the avg position for that order. This essentially
  // gives more space by spreading the nodes out further away from the avg.
  //
  layering.forEach((rank, rankIndex) => {
    if (rank.length == 0) return;
    const rankPosSum = rank.reduce((acc, order) => acc + balanced[order], 0);
    // This average position is what we'll move nodes away from
    const rankPosAvg = rankPosSum / rank.length;
    rank.forEach((nodeId) => {
        const position = balanced[nodeId];
        const otherPositions = [];
        rank.forEach((otherNodeId) => {
            if (nodeId != otherNodeId) {
                otherPositions.push(balanced[otherNodeId]);
            };
        });
        // Find a new spot for this node if it conflicts with other ones
        while (otherPositions.includes(balanced[nodeId])) {
            const moveBy = position > rankPosAvg ? -1 : 1;
            balanced[nodeId] += moveBy;
        }
    });
  });

  return balanced;
}

// This makessome adjustments to node positions to solve for a fairly specific
// case that dagre does not handle well. Dagre often times places sibling nodes far apart
// from each other, especially when they are leaf nodes in a tree like structure. I think it does
// this because it doesn't try to optimize for this compactness at all.
//
// The adjustment that we do here looks for tree structures in the graph, eg a set
// of siblings that a) only have one predecessor (the same parent), and b) have no successors. We
// also do the other way (only have one successor, has no predecessors) so we adjust trees that appear
// at the beginning (siblings are sources) or end (siblings are sinks) of the main graph.
//
// NOTE It would be nice to handle other more complex cases, for example where a set of siblings
//      have a single predecessor and a single successor that are equal, but we're just starting simple now.
//
// TODO The two algorithms don't currently cache which nodes have been visited, so we potentially do duplicate work.
//      I tried implementing a cache and check but for some reason this introduced a bug causing us to not reposition
//      some nodes.
function adjustTreeStructures(g, layering, balanced) {
    const layerIndexByNodeId = {};
    layering.forEach((layer, layerIndex) => {
        layer.forEach((nodeId) => {
            layerIndexByNodeId[nodeId] = layerIndex;
        });
    });
    var balanced = adjustRightTreeStructures(g, layering, balanced, layerIndexByNodeId);
    balanced     = adjustLeftTreeStructures(g, layering, balanced, layerIndexByNodeId);
    return balanced;
}

// See adjustTreeStructures. This adjusts tree structures that has siblings which are sinks
// in the overall graph.
function adjustRightTreeStructures(g, layering, balanced, layerIndexByNodeId) {
    // Loop over each sink and see if we need to adjust it (and its siblings)
    g.sinks().forEach((sinkNodeId) => {
        if (g.predecessors(sinkNodeId).length != 1) {
            return;
        }
        if (g.successors(sinkNodeId).length != 0) {
            return;
        }
        // If the node has a single (real) predecessor, return that node id
        function findFirstPredecessor(nodeId) {
            function tryNodes(nodeIds) {
                if (nodeIds.length == 1) {
                    if (g.node(nodeIds[0]).dummy != undefined) {
                        return tryNodes(g.predecessors(nodeIds[0]));
                    } else {
                        return nodeIds[0];
                    }
                }
                return undefined;
            }
            return tryNodes(g.predecessors(nodeId));
        }
        // Find all direct successors of the node (not dummies)
        function findSuccessors(nodeId) {
            const successorNodeIds = [];
            function tryNodes(nodeIds) {
                nodeIds.forEach((nodeId) => {
                    if (g.node(nodeId).dummy == undefined) {
                        successorNodeIds.push(nodeId);
                    } else {
                        tryNodes(g.successors(nodeId));
                    }
                });
            }
            tryNodes(g.successors(nodeId));
            return successorNodeIds;
        }

        const predecessorNodeId = findFirstPredecessor(sinkNodeId);
        if (!predecessorNodeId) {
            // There's no root node
            return;
        }

        const siblings = findSuccessors(predecessorNodeId);
        if (siblings.length == 1) {
            // If there's only one sibling in this tree then there's no gap to adjust
            return;
        }

        // Valid siblings are siblings that form a tree structure
        const validSiblings = [];
        siblings.forEach((siblingId) => {
            if (g.predecessors(siblingId).length != 1) {
                return;
            }
            if (g.successors(siblingId).length != 0) {
                return;
            }
            if (layerIndexByNodeId[siblingId] != layerIndexByNodeId[sinkNodeId]) {
                return;
            }
            validSiblings.push(siblingId);
        });
        if (validSiblings.length == 1) {
            // Nothing to adjust
            return;
        }

        const predecessorNodePosition = balanced[predecessorNodeId];

        // See if there are any spaces between these siblings that
        // we could potentially remove
        const siblingPositions = validSiblings
            .map(id => [id, balanced[id]])
            .sort((a,b) => a[1] - b[1]);
        let hasGap = false;
        for (let positionIndex = 0; positionIndex < siblingPositions.length; positionIndex++) {
            const previousPositionIndex = positionIndex - 1;
            if (previousPositionIndex >= 0) {
                const position = siblingPositions[positionIndex][1];
                const previousPosition = siblingPositions[previousPositionIndex][1];
                if (Math.abs(position - previousPosition) > 1) {
                    hasGap = true;
                    break;
                }
            }
        }
        if (!hasGap) {
            return;
        }

        // We've figured out there is a gap, now we want to try to remove it by repositioning nodes
        // closer together, and trying to keep them clustered around the position of their predecessor.
        // Only move a node in a direction if there are no other nodes (in the whole graph) currently occupying that position.
        // We'll order the sibling nodes by nearest to the current predecessor and move them in that order so that we don't have
        // to move any node twice, because moving nodes first that are closest to the predecessor means we'll make more space for the
        // siblings that are further away so we can move them next.

        // Extract position info for nodes in the current layer
        const currentLayerIndex = layerIndexByNodeId[sinkNodeId];
        const allNodeIdsInLayer = layering[currentLayerIndex];
        let allPositionsInLayer;
        function recomputeLayerPositions() {
            allPositionsInLayer = [];
            allNodeIdsInLayer.forEach((nodeId) => {
                allPositionsInLayer.push(balanced[nodeId]);
            });
        }
        recomputeLayerPositions();

        // Sort siblings by distance from predecessor ascending
        const siblingIdsSorted = validSiblings.sort((aNodeId, bNodeId) => {
            return Math.abs(predecessorNodePosition - balanced[aNodeId]) - Math.abs(predecessorNodePosition - balanced[aNodeId])
        });

        // For each node try to walk it closer to the predecessor node id
        siblingIdsSorted.forEach((siblingNodeId) => {
            recomputeLayerPositions();
            const currentPosition = balanced[siblingNodeId];
            if (currentPosition == predecessorNodePosition) {
                return;
            }
            const deltaToAdd = predecessorNodePosition > currentPosition ? 1 : -1;
            let bestPosition;
            while (true) {
                const nextPosition = (bestPosition != undefined) ? bestPosition + deltaToAdd : currentPosition + deltaToAdd;
                if (deltaToAdd == 1 && nextPosition >= predecessorNodePosition) {
                    break;
                }
                if (deltaToAdd == -1 && nextPosition <= predecessorNodePosition) {
                    break;
                }
                if (!allPositionsInLayer.includes(nextPosition)) {
                    bestPosition = nextPosition;
                } else {
                    break;
                }
            }
            if (bestPosition != undefined) {
                balanced[siblingNodeId] = bestPosition;
            }
        });
    });
 
    return balanced;
}

// See adjustTreeStructures. This adjusts tree structures that has siblings which are sources
// in the overall graph.
function adjustLeftTreeStructures(g, layering, balanced, layerIndexByNodeId) {
    // Loop over each source and see if we need to adjust it (and its siblings)
    g.sources().forEach((sourceNodeId) => {
        if (g.successors(sourceNodeId).length != 1) {
            return;
        }
        if (g.predecessors(sourceNodeId).length != 0) {
            return;
        }
        // If the node has a single (real) successor, return that node id
        function findFirstSuccessor(nodeId) {
            function tryNodes(nodeIds) {
                if (nodeIds.length == 1) {
                    if (g.node(nodeIds[0]).dummy != undefined) {
                        return tryNodes(g.successors(nodeIds[0]));
                    } else {
                        return nodeIds[0];
                    }
                }
                return undefined;
            }
            return tryNodes(g.successors(nodeId));
        }
        // Find all direct predecessors of the node (not dummies)
        function findPredecessors(nodeId) {
            const predecessorNodeIds = [];
            function tryNodes(nodeIds) {
                nodeIds.forEach((nodeId) => {
                    if (g.node(nodeId).dummy == undefined) {
                        predecessorNodeIds.push(nodeId);
                    } else {
                        tryNodes(g.predecessors(nodeId));
                    }
                });
            }
            tryNodes(g.predecessors(nodeId));
            return predecessorNodeIds;
        }
        const successorNodeId = findFirstSuccessor(sourceNodeId);
        if (!successorNodeId) {
            return;
        }
        const siblings = findPredecessors(successorNodeId);
        if (siblings.length == 1) {
            // If there's only one sibling in this tree then there's no gap to adjust
            return;
        }

        // Valid siblings will be an array of siblings that form a simple tree
        const validSiblings = [];
        siblings.forEach((siblingId) => {
            if (g.successors(siblingId).length != 1) {
                return;
            }
            if (g.predecessors(siblingId).length != 0) {
                return;
            }
            if (layerIndexByNodeId[siblingId] != layerIndexByNodeId[sourceNodeId]) {
                return;
            }
            validSiblings.push(siblingId);
        });
        if (validSiblings.length == 1) {
            // Nothing to adjust
            return;
        }

        // The position of the root of the tree
        const successorNodePosition = balanced[successorNodeId];

        // See if there are any spaces between these siblings that
        // we could potentially remove
        const siblingPositions = validSiblings
            .map(id => [id, balanced[id]])
            .sort((a,b) => a[1] - b[1]);
        let hasGap = false;
        for (let positionIndex = 0; positionIndex < siblingPositions.length; positionIndex++) {
            const previousPositionIndex = positionIndex - 1;
            if (previousPositionIndex >= 0) {
                const position = siblingPositions[positionIndex][1];
                const previousPosition = siblingPositions[previousPositionIndex][1];
                if (Math.abs(position - previousPosition) > 1) {
                    hasGap = true;
                    break;
                }
            }
        }
        if (!hasGap) {
            return;
        }

        // We've figured out there is a gap, now we want to try to remove it by repositioning nodes
        // closer together, and trying to keep them clustered around the position of their common successor (the root of this tree).
        // Only move a node in a direction if there are no other nodes (in the whole graph) currently occupying that position.
        // We'll order the sibling nodes by nearest to the common successor and move them in that order so that we don't have
        // to move any node twice, because moving nodes first that are closest to the successor means we'll make more space for the
        // siblings that are further away so we can move them next.

        // Extract position info for nodes in the current layer
        const currentLayerIndex = layerIndexByNodeId[sourceNodeId];
        const allNodeIdsInLayer = layering[currentLayerIndex];
        let allPositionsInLayer;
        function recomputeLayerPositions() {
            allPositionsInLayer = [];
            allNodeIdsInLayer.forEach((nodeId) => {
                allPositionsInLayer.push(balanced[nodeId]);
            });
        }
        recomputeLayerPositions();

        // Sort siblings by distance from successor ascending
        const siblingIdsSorted = validSiblings.sort((aNodeId, bNodeId) => {
            return Math.abs(successorNodePosition - balanced[aNodeId]) - Math.abs(successorNodePosition - balanced[aNodeId])
        });

        // For each node try to walk it closer to the root
        siblingIdsSorted.forEach((siblingNodeId) => {
            recomputeLayerPositions();
            const currentPosition = balanced[siblingNodeId];
            if (currentPosition == successorNodePosition) {
                return;
            }
            const deltaToAdd = successorNodePosition > currentPosition ? 1 : -1;
            let bestPosition;
            while (true) {
                const nextPosition = (bestPosition != undefined) ? bestPosition + deltaToAdd : currentPosition + deltaToAdd;
                if (deltaToAdd == 1 && nextPosition >= successorNodePosition) {
                    break;
                }
                if (deltaToAdd == -1 && nextPosition <= successorNodePosition) {
                    break;
                }
                if (!allPositionsInLayer.includes(nextPosition)) {
                    bestPosition = nextPosition;
                } else {
                    break;
                }
            }
            if (bestPosition != undefined) {
                balanced[siblingNodeId] = bestPosition;
            }
        });
    });
 
    return balanced;
}
function positionX(g) {
  var layering = util.buildLayerMatrix(g),
      conflicts = _.merge(findType1Conflicts(g, layering),
                          findType2Conflicts(g, layering));

  var xss = {},
      adjustedLayering;
  _.each(["u", "d"], function(vert) {
    adjustedLayering = vert === "u" ? layering : _.values(layering).reverse();
    _.each(["l", "r"], function(horiz) {
      if (horiz === "r") {
        adjustedLayering = _.map(adjustedLayering, function(inner) {
          return _.values(inner).reverse();
        });
      }

      var neighborFn = vert === "u" ? g.predecessors.bind(g) : g.successors.bind(g);
      var align = verticalAlignment(g, adjustedLayering, conflicts, neighborFn);
      var xs = horizontalCompaction(g, adjustedLayering,
                                    align.root, align.align,
                                    horiz === "r");
      if (horiz === "r") {
        xs = _.mapValues(xs, function(x) { return -x; });
      }
      xss[vert + horiz] = xs;
    });
  });

  var smallestWidth = findSmallestWidthAlignment(g, xss);
  alignCoordinates(xss, smallestWidth);
  var balanced = balance(xss, g.graph().align, layering, g);
  balanced = adjustTreeStructures(g, layering, balanced);
  return balanced;
}

function sep(nodeSep, edgeSep, reverseSep) {
  return function(g, v, w) {
    var vLabel = g.node(v),
        wLabel = g.node(w),
        sum = 0,
        delta;

    sum += vLabel.width / 2;
    if (_.has(vLabel, "labelpos")) {
      switch (vLabel.labelpos.toLowerCase()) {
        case "l": delta = -vLabel.width / 2; break;
        case "r": delta = vLabel.width / 2; break;
      }
    }
    if (delta) {
      sum += reverseSep ? delta : -delta;
    }
    delta = 0;

    sum += (vLabel.dummy ? edgeSep : nodeSep) / 2;
    sum += (wLabel.dummy ? edgeSep : nodeSep) / 2;

    sum += wLabel.width / 2;
    if (_.has(wLabel, "labelpos")) {
      switch (wLabel.labelpos.toLowerCase()) {
        case "l": delta = wLabel.width / 2; break;
        case "r": delta = -wLabel.width / 2; break;
      }
    }
    if (delta) {
      sum += reverseSep ? delta : -delta;
    }
    delta = 0;

    return sum;
  };
}

function width(g, v) {
  return g.node(v).width;
}
