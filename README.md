# BrickCornerWangTiling
Verification of A Brick Corner Wang Tiling Algorithm ~

- To extract functions e_nm and e'_nm.~
  coqc TilingProgram.v ~
  You have an Ocaml file "TilingProgam.ml". ~
  It contains some examples of boundary colorings such as boundary44a and boundary44c. ~
- To execute rendering example file.
  ocamlc TilingProgram.ml Tilingrender.ml -o TilingRender ~
  You have rendered images such as "b44a.svg" and "b44c.svg". ~
- You may use some external program such as 'rsvg-convert' to convert the image format from ".svg" to ".png". ~
  eg. svg-convert b44a.svg > b44a.png


