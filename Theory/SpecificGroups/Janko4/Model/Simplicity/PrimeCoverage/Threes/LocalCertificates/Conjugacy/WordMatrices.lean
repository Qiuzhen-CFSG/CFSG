module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.WordProducts

/-!
# Evaluation of the local conjugator words

The shared subword expressions are evaluated using the kernel-checked packed
products. Only the matrices of the two input elements are required.
See `Conjugacy.Rows` for the ATLAS source attribution.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
open Janko4.GeneratorCertificates

private theorem mul_matrix {g h : Model} {xs ys zs : Vector Nat 112}
    (hg : toMatrix g = decodeRows xs) (hh : toMatrix h = decodeRows ys)
    (hp : packedMul xs ys = zs) : toMatrix (g * h) = decodeRows zs := by
  rw [map_mul, hg, hh, ← decode_packedMul, hp]

variable (x y : Model)
    (hx : toMatrix x = decodeRows programFstRows)
    (hy : toMatrix y = decodeRows programSndRows)

include hx hy

theorem conj01_matrix : toMatrix (conj01 x y) = decodeRows conj01Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hx hy word01

theorem conj10_matrix : toMatrix (conj10 x y) = decodeRows conj10Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hy hx word10

theorem conj11_matrix : toMatrix (conj11 x y) = decodeRows conj11Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hy hy word11

theorem conj010_matrix : toMatrix (conj010 x y) = decodeRows conj010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hx (conj10_matrix x y hx hy) word010

theorem conj011_matrix : toMatrix (conj011 x y) = decodeRows conj011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hx (conj11_matrix x y hx hy) word011

theorem conj101_matrix : toMatrix (conj101 x y) = decodeRows conj101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hy (conj01_matrix x y hx hy) word101

theorem conj110_matrix : toMatrix (conj110 x y) = decodeRows conj110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hy (conj10_matrix x y hx hy) word110

theorem conj111_matrix : toMatrix (conj111 x y) = decodeRows conj111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix hy (conj11_matrix x y hx hy) word111

theorem conj0101_matrix : toMatrix (conj0101 x y) = decodeRows conj0101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj01_matrix x y hx hy) (conj01_matrix x y hx hy) word0101

theorem conj0110_matrix : toMatrix (conj0110 x y) = decodeRows conj0110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj01_matrix x y hx hy) (conj10_matrix x y hx hy) word0110

theorem conj0111_matrix : toMatrix (conj0111 x y) = decodeRows conj0111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj01_matrix x y hx hy) (conj11_matrix x y hx hy) word0111

theorem conj1010_matrix : toMatrix (conj1010 x y) = decodeRows conj1010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj10_matrix x y hx hy) (conj10_matrix x y hx hy) word1010

theorem conj1011_matrix : toMatrix (conj1011 x y) = decodeRows conj1011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj10_matrix x y hx hy) (conj11_matrix x y hx hy) word1011

theorem conj1101_matrix : toMatrix (conj1101 x y) = decodeRows conj1101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11_matrix x y hx hy) (conj01_matrix x y hx hy) word1101

theorem conj1110_matrix : toMatrix (conj1110 x y) = decodeRows conj1110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11_matrix x y hx hy) (conj10_matrix x y hx hy) word1110

theorem conj1111_matrix : toMatrix (conj1111 x y) = decodeRows conj1111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11_matrix x y hx hy) (conj11_matrix x y hx hy) word1111

theorem conj01101_matrix : toMatrix (conj01101 x y) = decodeRows conj01101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj01_matrix x y hx hy) (conj101_matrix x y hx hy) word01101

theorem conj11010_matrix : toMatrix (conj11010 x y) = decodeRows conj11010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11_matrix x y hx hy) (conj010_matrix x y hx hy) word11010

theorem conj11011_matrix : toMatrix (conj11011 x y) = decodeRows conj11011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11_matrix x y hx hy) (conj011_matrix x y hx hy) word11011

theorem conj11101_matrix : toMatrix (conj11101 x y) = decodeRows conj11101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11_matrix x y hx hy) (conj101_matrix x y hx hy) word11101

theorem conj011010_matrix : toMatrix (conj011010 x y) = decodeRows conj011010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011_matrix x y hx hy) (conj010_matrix x y hx hy) word011010

theorem conj011011_matrix : toMatrix (conj011011 x y) = decodeRows conj011011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011_matrix x y hx hy) (conj011_matrix x y hx hy) word011011

theorem conj011101_matrix : toMatrix (conj011101 x y) = decodeRows conj011101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011_matrix x y hx hy) (conj101_matrix x y hx hy) word011101

theorem conj011110_matrix : toMatrix (conj011110 x y) = decodeRows conj011110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011_matrix x y hx hy) (conj110_matrix x y hx hy) word011110

theorem conj101011_matrix : toMatrix (conj101011 x y) = decodeRows conj101011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj101_matrix x y hx hy) (conj011_matrix x y hx hy) word101011

theorem conj101111_matrix : toMatrix (conj101111 x y) = decodeRows conj101111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj101_matrix x y hx hy) (conj111_matrix x y hx hy) word101111

theorem conj110101_matrix : toMatrix (conj110101 x y) = decodeRows conj110101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj110_matrix x y hx hy) (conj101_matrix x y hx hy) word110101

theorem conj110111_matrix : toMatrix (conj110111 x y) = decodeRows conj110111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj110_matrix x y hx hy) (conj111_matrix x y hx hy) word110111

theorem conj111010_matrix : toMatrix (conj111010 x y) = decodeRows conj111010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj111_matrix x y hx hy) (conj010_matrix x y hx hy) word111010

theorem conj111101_matrix : toMatrix (conj111101 x y) = decodeRows conj111101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj111_matrix x y hx hy) (conj101_matrix x y hx hy) word111101

theorem conj0110101_matrix : toMatrix (conj0110101 x y) = decodeRows conj0110101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011_matrix x y hx hy) (conj0101_matrix x y hx hy) word0110101

theorem conj0111010_matrix : toMatrix (conj0111010 x y) = decodeRows conj0111010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011_matrix x y hx hy) (conj1010_matrix x y hx hy) word0111010

theorem conj1011110_matrix : toMatrix (conj1011110 x y) = decodeRows conj1011110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj101_matrix x y hx hy) (conj1110_matrix x y hx hy) word1011110

theorem conj1101010_matrix : toMatrix (conj1101010 x y) = decodeRows conj1101010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj110_matrix x y hx hy) (conj1010_matrix x y hx hy) word1101010

theorem conj1101011_matrix : toMatrix (conj1101011 x y) = decodeRows conj1101011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj110_matrix x y hx hy) (conj1011_matrix x y hx hy) word1101011

theorem conj1101101_matrix : toMatrix (conj1101101 x y) = decodeRows conj1101101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj110_matrix x y hx hy) (conj1101_matrix x y hx hy) word1101101

theorem conj1110101_matrix : toMatrix (conj1110101 x y) = decodeRows conj1110101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj111_matrix x y hx hy) (conj0101_matrix x y hx hy) word1110101

theorem conj1110110_matrix : toMatrix (conj1110110 x y) = decodeRows conj1110110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj111_matrix x y hx hy) (conj0110_matrix x y hx hy) word1110110

theorem conj1110111_matrix : toMatrix (conj1110111 x y) = decodeRows conj1110111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj111_matrix x y hx hy) (conj0111_matrix x y hx hy) word1110111

theorem conj01101101_matrix : toMatrix (conj01101101 x y) = decodeRows conj01101101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj0110_matrix x y hx hy) (conj1101_matrix x y hx hy) word01101101

theorem conj10101010_matrix : toMatrix (conj10101010 x y) = decodeRows conj10101010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1010_matrix x y hx hy) (conj1010_matrix x y hx hy) word10101010

theorem conj11010101_matrix : toMatrix (conj11010101 x y) = decodeRows conj11010101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1101_matrix x y hx hy) (conj0101_matrix x y hx hy) word11010101

theorem conj11011010_matrix : toMatrix (conj11011010 x y) = decodeRows conj11011010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1101_matrix x y hx hy) (conj1010_matrix x y hx hy) word11011010

theorem conj11011011_matrix : toMatrix (conj11011011 x y) = decodeRows conj11011011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1101_matrix x y hx hy) (conj1011_matrix x y hx hy) word11011011

theorem conj11101011_matrix : toMatrix (conj11101011 x y) = decodeRows conj11101011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1110_matrix x y hx hy) (conj1011_matrix x y hx hy) word11101011

theorem conj11101101_matrix : toMatrix (conj11101101 x y) = decodeRows conj11101101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1110_matrix x y hx hy) (conj1101_matrix x y hx hy) word11101101

theorem conj11110110_matrix : toMatrix (conj11110110 x y) = decodeRows conj11110110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1111_matrix x y hx hy) (conj0110_matrix x y hx hy) word11110110

theorem conj11111011_matrix : toMatrix (conj11111011 x y) = decodeRows conj11111011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1111_matrix x y hx hy) (conj1011_matrix x y hx hy) word11111011

theorem conj011011010_matrix : toMatrix (conj011011010 x y) = decodeRows conj011011010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj0110_matrix x y hx hy) (conj11010_matrix x y hx hy) word011011010

theorem conj1101111101_matrix : toMatrix (conj1101111101 x y) = decodeRows conj1101111101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11011_matrix x y hx hy) (conj11101_matrix x y hx hy) word1101111101

theorem conj01101111101_matrix : toMatrix (conj01101111101 x y) = decodeRows conj01101111101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj01101_matrix x y hx hy) (conj111101_matrix x y hx hy) word01101111101

theorem conj11011101111_matrix : toMatrix (conj11011101111 x y) = decodeRows conj11011101111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11011_matrix x y hx hy) (conj101111_matrix x y hx hy) word11011101111

theorem conj011011101111_matrix : toMatrix (conj011011101111 x y) = decodeRows conj011011101111Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011011_matrix x y hx hy) (conj101111_matrix x y hx hy) word011011101111

theorem conj110101101011_matrix : toMatrix (conj110101101011 x y) = decodeRows conj110101101011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj110101_matrix x y hx hy) (conj101011_matrix x y hx hy) word110101101011

theorem conj110111011110_matrix : toMatrix (conj110111011110 x y) = decodeRows conj110111011110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj110111_matrix x y hx hy) (conj011110_matrix x y hx hy) word110111011110

theorem conj111010110101_matrix : toMatrix (conj111010110101 x y) = decodeRows conj111010110101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj111010_matrix x y hx hy) (conj110101_matrix x y hx hy) word111010110101

theorem conj0110101101011_matrix : toMatrix (conj0110101101011 x y) = decodeRows conj0110101101011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011010_matrix x y hx hy) (conj1101011_matrix x y hx hy) word0110101101011

theorem conj0110111011110_matrix : toMatrix (conj0110111011110 x y) = decodeRows conj0110111011110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011011_matrix x y hx hy) (conj1011110_matrix x y hx hy) word0110111011110

theorem conj0111010110101_matrix : toMatrix (conj0111010110101 x y) = decodeRows conj0111010110101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj011101_matrix x y hx hy) (conj0110101_matrix x y hx hy) word0111010110101

theorem conj1110101101010_matrix : toMatrix (conj1110101101010 x y) = decodeRows conj1110101101010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj111010_matrix x y hx hy) (conj1101010_matrix x y hx hy) word1110101101010

theorem conj01110101101010_matrix : toMatrix (conj01110101101010 x y) = decodeRows conj01110101101010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj0111010_matrix x y hx hy) (conj1101010_matrix x y hx hy) word01110101101010

theorem conj110101011101011_matrix : toMatrix (conj110101011101011 x y) = decodeRows conj110101011101011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1101010_matrix x y hx hy) (conj11101011_matrix x y hx hy) word110101011101011

theorem conj111010111010101_matrix : toMatrix (conj111010111010101 x y) = decodeRows conj111010111010101Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1110101_matrix x y hx hy) (conj11010101_matrix x y hx hy) word111010111010101

theorem conj111011011111011_matrix : toMatrix (conj111011011111011 x y) = decodeRows conj111011011111011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1110110_matrix x y hx hy) (conj11111011_matrix x y hx hy) word111011011111011

theorem conj111011111011011_matrix : toMatrix (conj111011111011011 x y) = decodeRows conj111011111011011Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj1110111_matrix x y hx hy) (conj11011011_matrix x y hx hy) word111011111011011

theorem conj1110101110101010_matrix : toMatrix (conj1110101110101010 x y) = decodeRows conj1110101110101010Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11101011_matrix x y hx hy) (conj10101010_matrix x y hx hy) word1110101110101010

theorem conj1110110111110110_matrix : toMatrix (conj1110110111110110 x y) = decodeRows conj1110110111110110Rows := by
  have _ := hx
  have _ := hy
  exact mul_matrix (conj11101101_matrix x y hx hy) (conj11110110_matrix x y hx hy) word1110110111110110

end Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
