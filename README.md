# BrickCornerWangTiling
Verification of A Brick Corner Wang Tiling Algorithm

- To extract functions e_nm and e'_nm.  
       coqc TilingProgram.v  
  You have an Ocaml file "TilingProgam.ml".  
  It contains some examples of boundary colorings such as boundary44a and boundary44c.  
- To execute rendering example file.  
       ocamlc TilingProgram.ml Tilingrender.ml -o TilingRender  
       ./TilingRender  
  You have rendered images such as "b44a.svg" and "b44c.svg".  
- You may use some external program such as 'rsvg-convert' to convert the image format from ".svg" to ".png" or ".pdf".  
     eg.  rsvg-convert b44a.svg > b44a.png  
          rsvg-convert -f pdf -o b44a.pdf b44a.svg

<img src="https://github.com/KyushuUniversityMathematics/BrickCornerWangTiling/raw/master/images/b44a.png"/>

Please look at the following paper for details:
* "Verification of a brick Wang tiling algorithm" by T.Matsushima, Y.Mizoguchi, A.D.-Jourdan in Proc. 7th International Symposium on Symbolic Computation in Software Science (SCSS2016), EPiC Series in Computing, Vol.39, pp.107-116, 2016, http://easychair.org/publications/paper/Verification_of_a_brick_Wang_tiling_algorithm 
