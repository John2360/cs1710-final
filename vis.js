const d3 = require("d3");
d3.selectAll("svg > *").remove();

/*
  Visualizer for the in-class tic-tac-toe model. This is written in "raw" 
  D3, rather than using our helper libraries. If you're familiar with 
  visualization in JavaScript using this popular library, this is how you 
  would use it with Forge.

  Note that if you _aren't_ familiar, that's OK; we'll show more examples 
  and give more guidance in the near future. The helper library also makes 
  things rather easier. 

  TN 2024

  Note: if you're using this style, the require for d3 needs to come before anything 
  else, even comments.
*/


const cellWidth = 20
const cellHeight = 28


function printValue(row, col, yoffset, value, xoffset) {
    const xwidth = 20
    const yheight = 28

  let fillColor = "transparent"
  if (value == 'T') {
    fillColor = "red"
  } else if (value == 'F') {
    fillColor = "gray"
  } else if (value == 'S') {
    fillColor = "green" 
    // var battleship = svg.append('image')
    //   .attr('xlink:href', './assets/battleship.svg')
    //   .attr('width', 200)
    //   .attr('height', 200)
    // value = battleship
  } else {
    fillColor = "lightblue"
  }
  
  
  d3.select(svg)
    .append("rect")
    .style("fill", fillColor)
    .style("stroke", "black")
    .attr("x", (row) * xwidth + xoffset + 10)
    .attr("y", (col) * yheight + yoffset)
    .attr("width", xwidth)
    .attr("height", yheight);


  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .style("text-anchor", "middle")
    .style("alignment-baseline", "after-edge")

    .attr("x", (row + 1) * xwidth + xoffset)
    .attr("y", (col + 1) * yheight + yoffset)
    .text(value);

  
}

function printPlayer1Shots(stateAtom, yoffset) {
  for (r = 0; r <= 7; r++) {
    for (c = 0; c <= 7; c++) {
      printValue(
        r,
        c,
        yoffset,
        stateAtom.player1.shots[r][c].toString().substring(0, 1),
        0
      );
    }
  }

  // d3.select(svg)
  //   .append("rect")
  //   .attr("x", 5)
  //   .attr("y", yoffset + 1)
  //   .attr("width", 90)
  //   .attr("height", 120)
  //   .attr("stroke-width", 2)
  //   .attr("stroke", "black")
  //   .attr("fill", "transparent");
}

function printPlayer2Shots(stateAtom, yoffset) {
  xoffset = cellWidth * 18;
  for (r = 0; r <= 7; r++) {
    for (c = 0; c <= 7; c++) {
      printValue(
        r,
        c,
        yoffset,
        stateAtom.player2.shots[r][c].toString().substring(0, 1),
        xoffset
      );
    }
  }

  // d3.select(svg)
  //   .append("rect")
  //   .attr("x", xoffset + 5)
  //   .attr("y", yoffset + 1)
  //   .attr("width", 90)
  //   .attr("height", 120)
  //   .attr("stroke-width", 2)
  //   .attr("stroke", "black")
  //   .attr("fill", "transparent");
}

function printPlayer1Ships(stateAtom, yoffset) {
  xoffset = cellWidth * 9;
  for (r = 0; r <= 7; r++) {
    for (c = 0; c <= 7; c++) {
      if (
        stateAtom.player1.ships[r][c] != null &&
        stateAtom.player1.ships[r][c].toString().substring(0, 1) != "F"
      )
        printValue(
          r,
          c,
          yoffset,
          stateAtom.player1.ships[r][c].toString().substring(0, 1),
          xoffset
        );
    }
  }

  // d3.select(svg)
  //   .append("rect")
  //   .attr("x", xoffset)
  //   .attr("y", yoffset + 1)
  //   .attr("width", 90)
  //   .attr("height", 120)
  //   .attr("stroke-width", 2)
  //   .attr("stroke", "black")
  //   .attr("fill", "transparent");
}

function printPlayer2Ships(stateAtom, yoffset) {
  xoffset = cellWidth * 27;
  for (r = 0; r <= 7; r++) {
    for (c = 0; c <= 7; c++) {
      if (
        stateAtom.player2.ships[r][c] != null &&
        stateAtom.player2.ships[r][c].toString().substring(0, 1) != "F"
      ) 
        printValue(
          r,
          c,
          yoffset,
          stateAtom.player2.ships[r][c].toString().substring(0, 1),
          xoffset
        );
    }
  }

  // d3.select(svg)
  //   .append("rect")
  //   .attr("x", xoffset)
  //   .attr("y", yoffset + 1)
  //   .attr("width", 90)
  //   .attr("height", 120)
  //   .attr("stroke-width", 2)
  //   .attr("stroke", "black")
  //   .attr("fill", "transparent");
}

var offset = 0;
for (b = 0; b <= 10; b++) {
  if (BoardState.atom("BoardState" + b) != null) {

    printPlayer1Shots(BoardState.atom("BoardState" + b), offset);
    printPlayer1Ships(BoardState.atom("BoardState" + b), offset);
    printPlayer2Shots(BoardState.atom("BoardState" + b), offset);
    printPlayer2Ships(BoardState.atom("BoardState" + b), offset);
  }
  offset = offset + (cellHeight*9);
}







// const d3 = require("d3");
// d3.selectAll("svg > *").remove();

// /*
//   Visualizer for the in-class tic-tac-toe model. This is written in "raw" 
//   D3, rather than using our helper libraries. If you're familiar with 
//   visualization in JavaScript using this popular library, this is how you 
//   would use it with Forge.

//   Note that if you _aren't_ familiar, that's OK; we'll show more examples 
//   and give more guidance in the near future. The helper library also makes 
//   things rather easier. 

//   TN 2024

//   Note: if you're using this style, the require for d3 needs to come before anything 
//   else, even comments.
// */

// function printValue(row, col, yoffset, value, xoffset) {
//   d3.select(svg)
//     .append("text")
//     .style("fill", "black")
//     .attr("x", (row + 1) * 10 + xoffset)
//     .attr("y", (col + 1) * 14 + yoffset)
//     .text(value);
// }

// function printPlayer1Shots(stateAtom, yoffset) {
//   for (r = 0; r <= 7; r++) {
//     for (c = 0; c <= 7; c++) {
//       printValue(
//         r,
//         c,
//         yoffset,
//         stateAtom.player1.shots[r][c].toString().substring(0, 1),
//         0
//       );
//     }
//   }

//   d3.select(svg)
//     .append("rect")
//     .attr("x", 5)
//     .attr("y", yoffset + 1)
//     .attr("width", 90)
//     .attr("height", 120)
//     .attr("stroke-width", 2)
//     .attr("stroke", "black")
//     .attr("fill", "transparent");
// }

// function printPlayer2Shots(stateAtom, yoffset) {
//   xoffset = 200;
//   for (r = 0; r <= 7; r++) {
//     for (c = 0; c <= 7; c++) {
//       printValue(
//         r,
//         c,
//         yoffset,
//         stateAtom.player2.shots[r][c].toString().substring(0, 1),
//         xoffset
//       );
//     }
//   }

//   d3.select(svg)
//     .append("rect")
//     .attr("x", xoffset + 5)
//     .attr("y", yoffset + 1)
//     .attr("width", 90)
//     .attr("height", 120)
//     .attr("stroke-width", 2)
//     .attr("stroke", "black")
//     .attr("fill", "transparent");
// }

// function printPlayer1Ships(stateAtom, yoffset) {
//   xoffset = 95;
//   for (r = 0; r <= 7; r++) {
//     for (c = 0; c <= 7; c++) {
//       if (
//         stateAtom.player1.ships[r][c] != null &&
//         stateAtom.player1.ships[r][c].toString().substring(0, 1) != "F"
//       )
//         printValue(
//           r,
//           c,
//           yoffset,
//           stateAtom.player1.ships[r][c].toString().substring(0, 1),
//           xoffset
//         );
//     }
//   }

//   d3.select(svg)
//     .append("rect")
//     .attr("x", xoffset)
//     .attr("y", yoffset + 1)
//     .attr("width", 90)
//     .attr("height", 120)
//     .attr("stroke-width", 2)
//     .attr("stroke", "black")
//     .attr("fill", "transparent");
// }

// function printPlayer2Ships(stateAtom, yoffset) {
//   xoffset = 295;
//   for (r = 0; r <= 7; r++) {
//     for (c = 0; c <= 7; c++) {
//       if (
//         stateAtom.player2.ships[r][c] != null &&
//         stateAtom.player2.ships[r][c].toString().substring(0, 1) != "F"
//       )
//         printValue(
//           r,
//           c,
//           yoffset,
//           stateAtom.player2.ships[r][c].toString().substring(0, 1),
//           xoffset
//         );
//     }
//   }

//   d3.select(svg)
//     .append("rect")
//     .attr("x", xoffset)
//     .attr("y", yoffset + 1)
//     .attr("width", 90)
//     .attr("height", 120)
//     .attr("stroke-width", 2)
//     .attr("stroke", "black")
//     .attr("fill", "transparent");
// }

// var offset = 0;
// for (b = 0; b <= 10; b++) {
//   if (BoardState.atom("BoardState" + b) != null) {
//     printPlayer1Shots(BoardState.atom("BoardState" + b), offset);
//     printPlayer1Ships(BoardState.atom("BoardState" + b), offset);
//     printPlayer2Shots(BoardState.atom("BoardState" + b), offset);
//     printPlayer2Ships(BoardState.atom("BoardState" + b), offset);
//   }
//   offset = offset + 120;
// }
