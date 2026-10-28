module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.GroupTheory.PrimeCyclicCoverage
/-!
# Normalizing the order-three generator of the concrete J₁ model

The certified order has 3-part three, so Sylow conjugacy carries every
order-three element to a power of `b`. A word in the actual ATLAS matrix
generators conjugates `b²` to `b`. Its successive matrix products are checked
by kernel reduction. Thus any automorphism can be composed with an inner
automorphism to fix `b`.

This is one reduction for the `Out(J₁) = 1` entry of GLS3, Table 5.3f, used
on Aschbacher–Smith printed pp.504 and 510. The matrices and their source
are documented in `Theory.SpecificGroups.Janko1.Model.Basic`.
The untrusted word search is preserved in `Source/GenerateData.g`.
-/

namespace Janko1.OuterCertificate
open OrderCertificate
set_option maxRecDepth 10000
private def reverse0 : Model := 1
private theorem image_reverse0 : matrixValue reverse0 = 1 := rfl
private def reverse1 : Model := reverse0 * a
private def reverseMatrix1 : Mat := !![0, 7, 9, 9, 10, 7, 9;
    7, 0, 1, 4, 3, 3, 4;
    9, 1, 2, 8, 3, 6, 2;
    9, 4, 8, 10, 1, 6, 0;
    10, 3, 3, 1, 8, 9, 1;
    7, 3, 6, 6, 9, 1, 3;
    9, 4, 2, 0, 1, 3, 0]
private theorem image_reverse1 : matrixValue reverse1 = reverseMatrix1 := by
  rw [reverse1, map_mul, image_reverse0]
  change 1 * matrixA = reverseMatrix1
  decide +kernel
private def reverse2 : Model := reverse1 * b
private def reverseMatrix2 : Mat := !![9, 9, 2, 1, 3, 8, 6;
    2, 5, 5, 9, 2, 2, 1;
    5, 9, 9, 9, 8, 10, 3;
    5, 5, 7, 10, 9, 2, 5;
    7, 1, 5, 3, 5, 8, 2;
    6, 9, 10, 1, 10, 2, 3;
    1, 9, 6, 5, 9, 5, 4]
private theorem image_reverse2 : matrixValue reverse2 = reverseMatrix2 := by
  rw [reverse2, map_mul, image_reverse1]
  change reverseMatrix1 * matrixB = reverseMatrix2
  decide +kernel
private def reverse3 : Model := reverse2 * a
private def reverseMatrix3 : Mat := !![10, 5, 6, 7, 6, 7, 5;
    6, 5, 4, 6, 6, 4, 1;
    6, 3, 3, 3, 6, 8, 5;
    7, 3, 6, 0, 4, 8, 6;
    5, 3, 0, 3, 7, 5, 7;
    6, 5, 7, 4, 10, 5, 5;
    4, 3, 3, 6, 5, 0, 4]
private theorem image_reverse3 : matrixValue reverse3 = reverseMatrix3 := by
  rw [reverse3, map_mul, image_reverse2]
  change reverseMatrix2 * matrixA = reverseMatrix3
  decide +kernel
private def reverse4 : Model := reverse3 * b
private def reverseMatrix4 : Mat := !![2, 3, 10, 0, 10, 6, 7;
    4, 8, 8, 8, 0, 9, 3;
    8, 0, 5, 9, 1, 1, 4;
    0, 2, 10, 3, 6, 10, 7;
    3, 3, 4, 3, 4, 4, 5;
    3, 7, 0, 3, 2, 3, 8;
    3, 3, 2, 7, 3, 0, 8]
private theorem image_reverse4 : matrixValue reverse4 = reverseMatrix4 := by
  rw [reverse4, map_mul, image_reverse3]
  change reverseMatrix3 * matrixB = reverseMatrix4
  decide +kernel
private def reverse5 : Model := reverse4 * a
private def reverseMatrix5 : Mat := !![8, 1, 0, 2, 2, 2, 1;
    4, 8, 8, 2, 4, 1, 1;
    3, 9, 6, 0, 4, 8, 9;
    5, 10, 6, 8, 8, 4, 9;
    10, 4, 9, 8, 6, 6, 8;
    2, 3, 10, 6, 6, 6, 0;
    6, 4, 5, 7, 7, 3, 2]
private theorem image_reverse5 : matrixValue reverse5 = reverseMatrix5 := by
  rw [reverse5, map_mul, image_reverse4]
  change reverseMatrix4 * matrixA = reverseMatrix5
  decide +kernel
private def reverse6 : Model := reverse5 * b
private def reverseMatrix6 : Mat := !![0, 8, 8, 3, 1, 7, 1;
    2, 10, 9, 10, 6, 1, 3;
    5, 10, 9, 2, 9, 8, 8;
    2, 10, 7, 3, 7, 4, 7;
    4, 2, 3, 5, 3, 9, 0;
    8, 2, 7, 2, 8, 7, 8;
    8, 5, 8, 2, 5, 7, 1]
private theorem image_reverse6 : matrixValue reverse6 = reverseMatrix6 := by
  rw [reverse6, map_mul, image_reverse5]
  change reverseMatrix5 * matrixB = reverseMatrix6
  decide +kernel
private def reverse7 : Model := reverse6 * b
private def reverseMatrix7 : Mat := !![3, 5, 9, 2, 2, 1, 3;
    9, 10, 2, 6, 5, 9, 2;
    10, 3, 6, 9, 2, 2, 3;
    2, 5, 6, 5, 4, 1, 2;
    3, 9, 7, 10, 5, 3, 5;
    2, 3, 5, 9, 1, 10, 1;
    6, 7, 1, 2, 6, 5, 9]
private theorem image_reverse7 : matrixValue reverse7 = reverseMatrix7 := by
  rw [reverse7, map_mul, image_reverse6]
  change reverseMatrix6 * matrixB = reverseMatrix7
  decide +kernel
private def reverse8 : Model := reverse7 * a
private def reverseMatrix8 : Mat := !![1, 4, 7, 4, 3, 9, 4;
    9, 7, 7, 3, 2, 3, 3;
    8, 4, 3, 1, 8, 0, 1;
    1, 8, 9, 3, 2, 6, 2;
    2, 2, 8, 0, 6, 4, 3;
    5, 4, 3, 1, 9, 8, 5;
    10, 10, 2, 3, 1, 2, 6]
private theorem image_reverse8 : matrixValue reverse8 = reverseMatrix8 := by
  rw [reverse8, map_mul, image_reverse7]
  change reverseMatrix7 * matrixA = reverseMatrix8
  decide +kernel
private def reverse9 : Model := reverse8 * b
private def reverseMatrix9 : Mat := !![5, 5, 10, 6, 2, 7, 2;
    1, 8, 2, 2, 8, 5, 2;
    2, 9, 2, 6, 2, 1, 5;
    9, 10, 6, 9, 3, 8, 2;
    1, 9, 5, 4, 9, 5, 5;
    8, 3, 7, 6, 5, 2, 1;
    10, 9, 6, 1, 10, 3, 9]
private theorem image_reverse9 : matrixValue reverse9 = reverseMatrix9 := by
  rw [reverse9, map_mul, image_reverse8]
  change reverseMatrix8 * matrixB = reverseMatrix9
  decide +kernel
private def reverse10 : Model := reverse9 * a
private def reverseMatrix10 : Mat := !![2, 5, 5, 7, 6, 1, 9;
    5, 9, 7, 5, 10, 6, 2;
    9, 3, 2, 6, 1, 2, 8;
    1, 3, 5, 2, 3, 4, 6;
    6, 2, 6, 10, 2, 2, 2;
    2, 2, 1, 8, 10, 6, 10;
    9, 1, 9, 3, 9, 6, 3]
private theorem image_reverse10 : matrixValue reverse10 = reverseMatrix10 := by
  rw [reverse10, map_mul, image_reverse9]
  change reverseMatrix9 * matrixA = reverseMatrix10
  decide +kernel
private def reverse11 : Model := reverse10 * b
private def reverseMatrix11 : Mat := !![6, 9, 6, 3, 4, 4, 7;
    1, 5, 0, 7, 7, 0, 3;
    2, 2, 5, 6, 5, 10, 7;
    5, 4, 6, 6, 3, 0, 0;
    5, 9, 3, 4, 6, 4, 4;
    4, 3, 0, 4, 7, 3, 1;
    9, 4, 7, 2, 2, 5, 3]
private theorem image_reverse11 : matrixValue reverse11 = reverseMatrix11 := by
  rw [reverse11, map_mul, image_reverse10]
  change reverseMatrix10 * matrixB = reverseMatrix11
  decide +kernel
private def reverse12 : Model := reverse11 * b
private def reverseMatrix12 : Mat := !![8, 7, 4, 0, 1, 7, 3;
    6, 0, 9, 7, 3, 10, 10;
    10, 8, 4, 3, 6, 5, 9;
    7, 9, 0, 4, 2, 9, 1;
    6, 2, 9, 10, 9, 8, 8;
    9, 1, 10, 8, 8, 1, 3;
    8, 0, 2, 4, 2, 0, 1]
private theorem image_reverse12 : matrixValue reverse12 = reverseMatrix12 := by
  rw [reverse12, map_mul, image_reverse11]
  change reverseMatrix11 * matrixB = reverseMatrix12
  decide +kernel
private def reverse13 : Model := reverse12 * a
private def reverseMatrix13 : Mat := !![6, 8, 6, 10, 0, 5, 9;
    4, 4, 8, 6, 9, 7, 6;
    9, 1, 9, 0, 10, 2, 8;
    4, 3, 1, 8, 1, 9, 7;
    7, 9, 3, 5, 2, 0, 3;
    8, 1, 4, 6, 9, 3, 6;
    6, 7, 6, 9, 8, 3, 1]
private theorem image_reverse13 : matrixValue reverse13 = reverseMatrix13 := by
  rw [reverse13, map_mul, image_reverse12]
  change reverseMatrix12 * matrixA = reverseMatrix13
  decide +kernel
private def reverse14 : Model := reverse13 * b
private def reverseMatrix14 : Mat := !![4, 3, 4, 0, 7, 1, 3;
    5, 1, 9, 6, 6, 4, 9;
    2, 5, 9, 7, 2, 3, 4;
    5, 0, 6, 5, 8, 0, 7;
    8, 7, 5, 5, 7, 4, 2;
    7, 7, 6, 8, 5, 7, 2;
    7, 0, 1, 0, 7, 3, 5]
private theorem image_reverse14 : matrixValue reverse14 = reverseMatrix14 := by
  rw [reverse14, map_mul, image_reverse13]
  change reverseMatrix13 * matrixB = reverseMatrix14
  decide +kernel
private def reverse15 : Model := reverse14 * b
private def reverseMatrix15 : Mat := !![10, 8, 3, 7, 0, 3, 1;
    8, 1, 9, 3, 5, 9, 2;
    0, 9, 6, 2, 4, 3, 8;
    10, 5, 2, 7, 3, 3, 5;
    3, 1, 1, 10, 2, 9, 5;
    4, 10, 3, 4, 9, 4, 7;
    3, 2, 2, 7, 3, 4, 8]
private theorem image_reverse15 : matrixValue reverse15 = reverseMatrix15 := by
  rw [reverse15, map_mul, image_reverse14]
  change reverseMatrix14 * matrixB = reverseMatrix15
  decide +kernel
private def reverse16 : Model := reverse15 * a
private def reverseMatrix16 : Mat := !![0, 4, 4, 3, 3, 6, 5;
    4, 6, 1, 6, 5, 4, 5;
    4, 1, 6, 5, 4, 6, 6;
    3, 6, 5, 8, 8, 8, 5;
    3, 5, 4, 8, 5, 0, 7;
    6, 4, 6, 8, 0, 8, 4;
    5, 5, 6, 5, 7, 4, 10]
private theorem image_reverse16 : matrixValue reverse16 = reverseMatrix16 := by
  rw [reverse16, map_mul, image_reverse15]
  change reverseMatrix15 * matrixA = reverseMatrix16
  decide +kernel
private def reverse17 : Model := reverse16 * b
private def reverseMatrix17 : Mat := !![10, 8, 7, 0, 7, 8, 4;
    5, 2, 8, 8, 5, 10, 4;
    2, 3, 2, 1, 8, 6, 9;
    2, 1, 0, 4, 0, 3, 9;
    3, 10, 0, 7, 1, 5, 2;
    9, 10, 9, 7, 9, 7, 0;
    8, 3, 10, 8, 10, 2, 1]
private theorem image_reverse17 : matrixValue reverse17 = reverseMatrix17 := by
  rw [reverse17, map_mul, image_reverse16]
  change reverseMatrix16 * matrixB = reverseMatrix17
  decide +kernel
private def reverse18 : Model := reverse17 * a
private def reverseMatrix18 : Mat := !![6, 6, 2, 2, 2, 10, 2;
    6, 4, 1, 9, 2, 6, 5;
    9, 10, 1, 1, 9, 3, 5;
    2, 9, 10, 3, 8, 5, 9;
    9, 9, 9, 3, 1, 3, 6;
    1, 5, 3, 6, 3, 2, 4;
    9, 6, 5, 2, 6, 4, 10]
private theorem image_reverse18 : matrixValue reverse18 = reverseMatrix18 := by
  rw [reverse18, map_mul, image_reverse17]
  change reverseMatrix17 * matrixA = reverseMatrix18
  decide +kernel
private def reverse19 : Model := reverse18 * b
private def reverseMatrix19 : Mat := !![0, 0, 9, 7, 0, 5, 0;
    8, 1, 0, 0, 8, 0, 9;
    8, 1, 0, 0, 9, 0, 8;
    1, 8, 0, 0, 1, 0, 1;
    0, 0, 7, 5, 0, 9, 0;
    0, 0, 5, 9, 0, 7, 0;
    9, 1, 0, 0, 8, 0, 8]
private theorem image_reverse19 : matrixValue reverse19 = reverseMatrix19 := by
  rw [reverse19, map_mul, image_reverse18]
  change reverseMatrix18 * matrixB = reverseMatrix19
  decide +kernel
private def reverse20 : Model := reverse19 * b
private def reverseMatrix20 : Mat := !![8, 2, 5, 0, 4, 3, 9;
    1, 7, 2, 8, 6, 5, 8;
    5, 7, 6, 7, 7, 8, 2;
    7, 3, 3, 2, 4, 10, 1;
    6, 1, 5, 8, 8, 7, 9;
    9, 8, 1, 6, 6, 5, 0;
    3, 10, 0, 2, 2, 9, 1]
private theorem image_reverse20 : matrixValue reverse20 = reverseMatrix20 := by
  rw [reverse20, map_mul, image_reverse19]
  change reverseMatrix19 * matrixB = reverseMatrix20
  decide +kernel
private def reverse21 : Model := reverse20 * a
private def reverseMatrix21 : Mat := !![3, 8, 0, 10, 4, 4, 4;
    9, 7, 5, 4, 3, 6, 7;
    2, 1, 6, 4, 6, 2, 6;
    9, 7, 8, 7, 4, 5, 5;
    4, 6, 4, 8, 2, 9, 9;
    5, 0, 0, 8, 7, 1, 4;
    4, 0, 5, 0, 6, 5, 8]
private theorem image_reverse21 : matrixValue reverse21 = reverseMatrix21 := by
  rw [reverse21, map_mul, image_reverse20]
  change reverseMatrix20 * matrixA = reverseMatrix21
  decide +kernel
private def reverse22 : Model := reverse21 * b
private def reverseMatrix22 : Mat := !![2, 8, 10, 10, 1, 3, 8;
    10, 5, 8, 5, 4, 2, 8;
    3, 2, 0, 0, 9, 1, 4;
    7, 9, 9, 9, 0, 10, 7;
    8, 10, 7, 7, 4, 8, 0;
    6, 2, 2, 8, 9, 3, 1;
    5, 3, 0, 1, 2, 10, 7]
private theorem image_reverse22 : matrixValue reverse22 = reverseMatrix22 := by
  rw [reverse22, map_mul, image_reverse21]
  change reverseMatrix21 * matrixB = reverseMatrix22
  decide +kernel
private def reverse23 : Model := reverse22 * a
private def reverseMatrix23 : Mat := !![9, 9, 9, 7, 6, 7, 3;
    3, 5, 4, 9, 4, 5, 4;
    4, 1, 4, 6, 0, 0, 3;
    6, 9, 5, 2, 10, 6, 4;
    6, 6, 3, 4, 0, 5, 0;
    4, 6, 6, 9, 4, 8, 7;
    7, 4, 4, 8, 8, 0, 1]
private theorem image_reverse23 : matrixValue reverse23 = reverseMatrix23 := by
  rw [reverse23, map_mul, image_reverse22]
  change reverseMatrix22 * matrixA = reverseMatrix23
  decide +kernel
private def reverse24 : Model := reverse23 * b
private def reverseMatrix24 : Mat := !![2, 1, 1, 2, 2, 8, 0;
    4, 9, 9, 0, 8, 3, 6;
    5, 3, 7, 3, 5, 1, 2;
    7, 2, 4, 7, 3, 6, 5;
    7, 10, 3, 9, 10, 7, 3;
    3, 2, 1, 3, 7, 6, 5;
    5, 0, 8, 5, 5, 9, 1]
private theorem image_reverse24 : matrixValue reverse24 = reverseMatrix24 := by
  rw [reverse24, map_mul, image_reverse23]
  change reverseMatrix23 * matrixB = reverseMatrix24
  decide +kernel
private def reverse25 : Model := reverse24 * a
private def reverseMatrix25 : Mat := !![0, 9, 3, 1, 6, 6, 6;
    2, 6, 7, 5, 4, 4, 8;
    10, 3, 1, 0, 2, 2, 2;
    10, 7, 8, 3, 2, 4, 1;
    2, 8, 9, 5, 0, 4, 8;
    9, 5, 1, 6, 3, 3, 7;
    8, 10, 7, 9, 3, 5, 5]
private theorem image_reverse25 : matrixValue reverse25 = reverseMatrix25 := by
  rw [reverse25, map_mul, image_reverse24]
  change reverseMatrix24 * matrixA = reverseMatrix25
  decide +kernel
private def reverse26 : Model := reverse25 * b
private def reverseMatrix26 : Mat := !![9, 6, 1, 10, 3, 9, 10;
    3, 9, 9, 3, 6, 9, 10;
    1, 5, 2, 8, 3, 9, 2;
    8, 4, 5, 6, 9, 10, 3;
    5, 10, 6, 2, 7, 2, 5;
    9, 2, 6, 2, 1, 5, 2;
    2, 6, 7, 2, 6, 6, 10]
private theorem image_reverse26 : matrixValue reverse26 = reverseMatrix26 := by
  rw [reverse26, map_mul, image_reverse25]
  change reverseMatrix25 * matrixB = reverseMatrix26
  decide +kernel
private def reverse27 : Model := reverse26 * b
private def reverseMatrix27 : Mat := !![10, 7, 4, 4, 3, 2, 4;
    2, 4, 4, 3, 2, 8, 3;
    3, 7, 8, 1, 8, 0, 1;
    10, 3, 2, 3, 2, 5, 2;
    9, 9, 3, 0, 6, 7, 3;
    6, 7, 8, 1, 9, 3, 5;
    1, 1, 9, 3, 1, 9, 6]
private theorem image_reverse27 : matrixValue reverse27 = reverseMatrix27 := by
  rw [reverse27, map_mul, image_reverse26]
  change reverseMatrix26 * matrixB = reverseMatrix27
  decide +kernel
private def reverse28 : Model := reverse27 * a
private def reverseMatrix28 : Mat := !![3, 0, 1, 7, 7, 4, 3;
    7, 6, 4, 3, 6, 4, 2;
    10, 6, 7, 5, 9, 6, 2;
    7, 3, 7, 4, 5, 6, 2;
    6, 7, 8, 2, 9, 2, 7;
    0, 0, 8, 7, 1, 7, 6;
    0, 5, 0, 5, 6, 8, 4]
private theorem image_reverse28 : matrixValue reverse28 = reverseMatrix28 := by
  rw [reverse28, map_mul, image_reverse27]
  change reverseMatrix27 * matrixA = reverseMatrix28
  decide +kernel
private def reverse29 : Model := reverse28 * b
private def reverseMatrix29 : Mat := !![5, 7, 2, 4, 7, 3, 6;
    5, 3, 2, 1, 3, 7, 6;
    0, 2, 1, 1, 2, 2, 8;
    2, 5, 3, 7, 3, 5, 1;
    3, 7, 10, 3, 9, 10, 7;
    1, 5, 0, 8, 5, 5, 9;
    6, 4, 9, 9, 0, 8, 3]
private theorem image_reverse29 : matrixValue reverse29 = reverseMatrix29 := by
  rw [reverse29, map_mul, image_reverse28]
  change reverseMatrix28 * matrixB = reverseMatrix29
  decide +kernel
private def reverse30 : Model := reverse29 * a
private def reverseMatrix30 : Mat := !![6, 8, 7, 0, 5, 0, 5;
    5, 7, 2, 7, 5, 4, 8;
    6, 5, 2, 7, 8, 7, 7;
    1, 7, 5, 0, 0, 3, 7;
    4, 7, 3, 3, 0, 1, 4;
    9, 6, 9, 1, 6, 4, 5;
    9, 2, 4, 5, 7, 3, 2]
private theorem image_reverse30 : matrixValue reverse30 = reverseMatrix30 := by
  rw [reverse30, map_mul, image_reverse29]
  change reverseMatrix29 * matrixA = reverseMatrix30
  decide +kernel
private def reverse31 : Model := reverse30 * b
private def reverseMatrix31 : Mat := !![8, 8, 5, 4, 2, 9, 0;
    3, 5, 6, 7, 9, 4, 7;
    4, 6, 5, 8, 2, 10, 8;
    9, 8, 0, 9, 1, 10, 9;
    5, 10, 9, 5, 8, 7, 3;
    1, 7, 3, 4, 10, 8, 2;
    5, 2, 10, 5, 0, 8, 5]
private theorem image_reverse31 : matrixValue reverse31 = reverseMatrix31 := by
  rw [reverse31, map_mul, image_reverse30]
  change reverseMatrix30 * matrixB = reverseMatrix31
  decide +kernel
private def reverse32 : Model := reverse31 * b
private def reverseMatrix32 : Mat := !![7, 8, 0, 8, 1, 4, 7;
    7, 2, 8, 10, 6, 3, 5;
    2, 3, 1, 6, 9, 9, 8;
    9, 10, 7, 8, 2, 0, 0;
    2, 1, 4, 6, 3, 0, 10;
    0, 10, 7, 7, 2, 2, 9;
    1, 8, 3, 9, 8, 10, 1]
private theorem image_reverse32 : matrixValue reverse32 = reverseMatrix32 := by
  rw [reverse32, map_mul, image_reverse31]
  change reverseMatrix31 * matrixB = reverseMatrix32
  decide +kernel
private def reverse33 : Model := reverse32 * a
private def reverseMatrix33 : Mat := !![9, 3, 0, 2, 10, 1, 9;
    5, 1, 9, 6, 3, 4, 3;
    1, 4, 3, 7, 1, 3, 2;
    5, 9, 10, 6, 0, 3, 5;
    8, 3, 5, 7, 9, 2, 0;
    3, 6, 6, 4, 2, 7, 7;
    4, 5, 5, 3, 9, 1, 8]
private theorem image_reverse33 : matrixValue reverse33 = reverseMatrix33 := by
  rw [reverse33, map_mul, image_reverse32]
  change reverseMatrix32 * matrixA = reverseMatrix33
  decide +kernel
private def reverse34 : Model := reverse33 * b
private def reverseMatrix34 : Mat := !![3, 1, 10, 3, 8, 7, 0;
    2, 9, 3, 1, 9, 8, 5;
    8, 3, 0, 9, 6, 9, 4;
    3, 5, 10, 6, 9, 7, 8;
    2, 6, 8, 1, 1, 1, 2;
    4, 7, 4, 1, 8, 4, 2;
    4, 8, 3, 9, 9, 7, 8]
private theorem image_reverse34 : matrixValue reverse34 = reverseMatrix34 := by
  rw [reverse34, map_mul, image_reverse33]
  change reverseMatrix33 * matrixB = reverseMatrix34
  decide +kernel
private def reverse35 : Model := reverse34 * b
private def reverseMatrix35 : Mat := !![4, 9, 4, 0, 4, 9, 0;
    10, 2, 10, 4, 5, 4, 2;
    4, 7, 9, 2, 7, 0, 0;
    4, 4, 7, 0, 2, 0, 2;
    7, 10, 10, 7, 1, 4, 7;
    10, 10, 6, 2, 9, 7, 7;
    10, 6, 2, 7, 1, 9, 4]
private theorem image_reverse35 : matrixValue reverse35 = reverseMatrix35 := by
  rw [reverse35, map_mul, image_reverse34]
  change reverseMatrix34 * matrixB = reverseMatrix35
  decide +kernel
private def reverse36 : Model := reverse35 * a
private def reverseMatrix36 : Mat := !![4, 5, 9, 8, 5, 3, 1;
    5, 10, 0, 5, 9, 6, 3;
    9, 0, 10, 9, 3, 2, 1;
    8, 5, 9, 0, 3, 7, 2;
    5, 9, 3, 3, 1, 6, 4;
    3, 6, 2, 7, 6, 4, 7;
    1, 3, 1, 2, 4, 7, 3]
private theorem image_reverse36 : matrixValue reverse36 = reverseMatrix36 := by
  rw [reverse36, map_mul, image_reverse35]
  change reverseMatrix35 * matrixA = reverseMatrix36
  decide +kernel
private def reverse37 : Model := reverse36 * b
private def reverseMatrix37 : Mat := !![2, 4, 1, 10, 7, 8, 3;
    5, 5, 5, 0, 2, 8, 10;
    0, 4, 8, 2, 8, 9, 5;
    7, 7, 3, 9, 5, 4, 6;
    8, 8, 4, 2, 6, 10, 5;
    9, 9, 9, 1, 8, 10, 0;
    3, 5, 5, 8, 10, 7, 9]
private theorem image_reverse37 : matrixValue reverse37 = reverseMatrix37 := by
  rw [reverse37, map_mul, image_reverse36]
  change reverseMatrix36 * matrixB = reverseMatrix37
  decide +kernel
private def reverse38 : Model := reverse37 * a
private def reverseMatrix38 : Mat := !![5, 2, 3, 10, 0, 7, 1;
    4, 0, 2, 1, 2, 4, 2;
    9, 10, 3, 8, 1, 3, 1;
    3, 7, 1, 3, 4, 0, 4;
    10, 4, 5, 2, 8, 8, 5;
    6, 9, 2, 3, 2, 1, 8;
    8, 2, 9, 10, 0, 7, 0]
private theorem image_reverse38 : matrixValue reverse38 = reverseMatrix38 := by
  rw [reverse38, map_mul, image_reverse37]
  change reverseMatrix37 * matrixA = reverseMatrix38
  decide +kernel
private def reverse39 : Model := reverse38 * b
private def reverseMatrix39 : Mat := !![5, 5, 5, 4, 1, 9, 9;
    9, 4, 10, 5, 3, 6, 8;
    8, 5, 2, 10, 1, 1, 2;
    4, 1, 9, 5, 6, 9, 6;
    5, 2, 2, 2, 1, 8, 8;
    1, 2, 5, 6, 2, 2, 9;
    3, 5, 9, 2, 2, 8, 1]
private theorem image_reverse39 : matrixValue reverse39 = reverseMatrix39 := by
  rw [reverse39, map_mul, image_reverse38]
  change reverseMatrix38 * matrixB = reverseMatrix39
  decide +kernel
private def reverse40 : Model := reverse39 * b
private def reverseMatrix40 : Mat := !![4, 7, 9, 9, 4, 0, 0;
    10, 6, 2, 4, 10, 9, 7;
    4, 4, 7, 0, 9, 0, 9;
    7, 2, 7, 0, 4, 2, 0;
    4, 1, 1, 7, 1, 7, 7;
    10, 2, 10, 7, 6, 4, 9;
    1, 1, 5, 2, 9, 4, 7]
private theorem image_reverse40 : matrixValue reverse40 = reverseMatrix40 := by
  rw [reverse40, map_mul, image_reverse39]
  change reverseMatrix39 * matrixB = reverseMatrix40
  decide +kernel
private def reverse41 : Model := reverse40 * a
private def reverseMatrix41 : Mat := !![9, 8, 2, 10, 8, 6, 9;
    3, 8, 10, 3, 10, 2, 1;
    9, 10, 0, 7, 0, 3, 9;
    10, 8, 4, 0, 4, 3, 7;
    3, 10, 0, 7, 10, 6, 9;
    6, 9, 8, 3, 5, 10, 4;
    9, 10, 2, 7, 2, 4, 0]
private theorem image_reverse41 : matrixValue reverse41 = reverseMatrix41 := by
  rw [reverse41, map_mul, image_reverse40]
  change reverseMatrix40 * matrixA = reverseMatrix41
  decide +kernel
private def reverse42 : Model := reverse41 * b
private def reverseMatrix42 : Mat := !![3, 3, 9, 8, 1, 10, 1;
    10, 4, 3, 9, 0, 0, 2;
    8, 0, 3, 10, 4, 7, 4;
    10, 4, 6, 3, 0, 1, 2;
    2, 3, 1, 5, 3, 5, 4;
    1, 7, 7, 2, 9, 2, 0;
    8, 1, 6, 9, 2, 3, 2]
private theorem image_reverse42 : matrixValue reverse42 = reverseMatrix42 := by
  rw [reverse42, map_mul, image_reverse41]
  change reverseMatrix41 * matrixB = reverseMatrix42
  decide +kernel
private def reverse43 : Model := reverse42 * a
private def reverseMatrix43 : Mat := !![10, 0, 1, 10, 8, 0, 0;
    0, 7, 0, 0, 0, 6, 2;
    0, 5, 0, 0, 0, 2, 4;
    2, 0, 8, 3, 1, 0, 0;
    0, 9, 0, 0, 0, 4, 6;
    3, 0, 8, 2, 1, 0, 0;
    3, 0, 9, 3, 1, 0, 0]
private theorem image_reverse43 : matrixValue reverse43 = reverseMatrix43 := by
  rw [reverse43, map_mul, image_reverse42]
  change reverseMatrix42 * matrixA = reverseMatrix43
  decide +kernel
private def reverse44 : Model := reverse43 * b
private def reverseMatrix44 : Mat := !![10, 10, 5, 0, 9, 4, 3;
    6, 2, 10, 8, 7, 3, 5;
    2, 10, 7, 9, 0, 4, 9;
    8, 8, 5, 9, 9, 1, 9;
    10, 8, 9, 1, 1, 8, 3;
    0, 1, 3, 0, 2, 7, 2;
    7, 3, 3, 4, 4, 0, 1]
private theorem image_reverse44 : matrixValue reverse44 = reverseMatrix44 := by
  rw [reverse44, map_mul, image_reverse43]
  change reverseMatrix43 * matrixB = reverseMatrix44
  decide +kernel
private def reverse45 : Model := reverse44 * a
private def reverseMatrix45 : Mat := !![7, 5, 2, 5, 3, 4, 7;
    4, 2, 2, 5, 5, 6, 10;
    4, 6, 2, 8, 4, 6, 7;
    8, 9, 4, 7, 9, 9, 5;
    8, 1, 5, 0, 4, 4, 0;
    0, 5, 4, 6, 5, 8, 0;
    1, 7, 8, 0, 4, 7, 8]
private theorem image_reverse45 : matrixValue reverse45 = reverseMatrix45 := by
  rw [reverse45, map_mul, image_reverse44]
  change reverseMatrix44 * matrixA = reverseMatrix45
  decide +kernel
private theorem reverse_b_square : reverse45 * b ^ 2 * reverse45⁻¹ = b := by
  have he : reverse45 * b ^ 2 = b * reverse45 := by
    apply matrixValue_injective
    simp only [map_mul, map_pow, image_reverse45]
    change reverseMatrix45 * matrixB ^ 2 = matrixB * reverseMatrix45
    decide +kernel
  rw [he, mul_inv_cancel_right]

/-- Every order-three element of the actual model is conjugate to `b`. -/
public theorem order_three_fusion (x : Model) (hx : orderOf x = 3) :
    ∃ g : Model, g * x * g⁻¹ = b := by
  obtain ⟨k, g, hg⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 3) (by rw [card_model]; decide : ¬ 3 ^ 2 ∣ Nat.card Model)
    orderOf_b hx
  rw [← pow_mod_orderOf b k, orderOf_b] at hg
  have hk : k % 3 < 3 := Nat.mod_lt _ (by decide)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, pow_zero, mul_one, mul_inv_cancel] at hg
    rw [hg, orderOf_one] at hx
    contradiction
  · refine ⟨g⁻¹, ?_⟩
    rw [hg, h1, pow_one]
    simp [mul_assoc]
  · refine ⟨reverse45 * g⁻¹, ?_⟩
    rw [hg, h2]
    simpa [mul_assoc] using reverse_b_square
end Janko1.OuterCertificate
