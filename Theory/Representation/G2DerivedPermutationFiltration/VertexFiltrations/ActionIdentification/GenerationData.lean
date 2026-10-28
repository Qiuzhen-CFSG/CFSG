module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Generators

/-!
# Byte certificates for binary G₂ generation

The four byte maps are the two published octonion automorphisms and their
inverses, checked on all 256 binary vectors. Word evaluation therefore
computes their actual action. Sixteen Schreier words rewrite multiplication
by the eight root/Weyl generators using the two representatives 1 and F(1).
Checking these identities on the eight basis vectors proves them in the
literal full octonion automorphism group.

These tables were computed from Coordinates' attributed root words and
matrices (ATLAS revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917,
LICENSES/ATLAS.txt); every identity below is kernel checked.
This supports Aschbacher–Smith G.7.2(3), printed p.348.
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
namespace G2DerivedPermutationFiltration.VertexCoordinates.ActionGeneration
set_option maxRecDepth 10000

def decode (n : Fin 256) : Carrier (ZMod 2) :=
  fun i => if n.val.testBit i.val then 1 else 0

def signedGenerator (a : Fin 2 × Bool) : FullGroup :=
  if a.2 then ambientGenerator a.1 else (ambientGenerator a.1)⁻¹

def generatorOnBytes : Fin 2 → Fin 2 → Fin 256 → Fin 256 :=
  ![![![0, 35, 188, 159, 190, 157, 2, 33, 11, 40, 183, 148, 181, 150, 9, 42, 19, 48, 175, 140, 173, 142, 17, 50, 24, 59, 164, 135, 166, 133, 26, 57, 95, 124, 227, 192, 225, 194, 93, 126, 84, 119, 232, 203, 234, 201, 86, 117, 76, 111, 240, 211, 242, 209, 78, 109, 71, 100, 251, 216, 249, 218, 69, 102, 94, 125, 226, 193, 224, 195, 92, 127, 85, 118, 233, 202, 235, 200, 87, 116, 77, 110, 241, 210, 243, 208, 79, 108, 70, 101, 250, 217, 248, 219, 68, 103, 1, 34, 189, 158, 191, 156, 3, 32, 10, 41, 182, 149, 180, 151, 8, 43, 18, 49, 174, 141, 172, 143, 16, 51, 25, 58, 165, 134, 167, 132, 27, 56, 5, 38, 185, 154, 187, 152, 7, 36, 14, 45, 178, 145, 176, 147, 12, 47, 22, 53, 170, 137, 168, 139, 20, 55, 29, 62, 161, 130, 163, 128, 31, 60, 90, 121, 230, 197, 228, 199, 88, 123, 81, 114, 237, 206, 239, 204, 83, 112, 73, 106, 245, 214, 247, 212, 75, 104, 66, 97, 254, 221, 252, 223, 64, 99, 91, 120, 231, 196, 229, 198, 89, 122, 80, 115, 236, 207, 238, 205, 82, 113, 72, 107, 244, 215, 246, 213, 74, 105, 67, 96, 255, 220, 253, 222, 65, 98, 4, 39, 184, 155, 186, 153, 6, 37, 15, 44, 179, 144, 177, 146, 13, 46, 23, 52, 171, 136, 169, 138, 21, 54, 28, 63, 160, 131, 162, 129, 30, 61], ![0, 96, 6, 102, 224, 128, 230, 134, 110, 14, 104, 8, 142, 238, 136, 232, 118, 22, 112, 16, 150, 246, 144, 240, 24, 120, 30, 126, 248, 152, 254, 158, 103, 7, 97, 1, 135, 231, 129, 225, 9, 105, 15, 111, 233, 137, 239, 143, 17, 113, 23, 119, 241, 145, 247, 151, 127, 31, 121, 25, 159, 255, 153, 249, 190, 222, 184, 216, 94, 62, 88, 56, 208, 176, 214, 182, 48, 80, 54, 86, 200, 168, 206, 174, 40, 72, 46, 78, 166, 198, 160, 192, 70, 38, 64, 32, 217, 185, 223, 191, 57, 89, 63, 95, 183, 215, 177, 209, 87, 55, 81, 49, 175, 207, 169, 201, 79, 47, 73, 41, 193, 161, 199, 167, 33, 65, 39, 71, 157, 253, 155, 251, 125, 29, 123, 27, 243, 147, 245, 149, 19, 115, 21, 117, 235, 139, 237, 141, 11, 107, 13, 109, 133, 229, 131, 227, 101, 5, 99, 3, 250, 154, 252, 156, 26, 122, 28, 124, 148, 244, 146, 242, 116, 20, 114, 18, 140, 236, 138, 234, 108, 12, 106, 10, 226, 130, 228, 132, 2, 98, 4, 100, 35, 67, 37, 69, 195, 163, 197, 165, 77, 45, 75, 43, 173, 205, 171, 203, 85, 53, 83, 51, 181, 213, 179, 211, 59, 91, 61, 93, 219, 187, 221, 189, 68, 36, 66, 34, 164, 196, 162, 194, 42, 74, 44, 76, 202, 170, 204, 172, 50, 82, 52, 84, 210, 178, 212, 180, 92, 60, 90, 58, 188, 220, 186, 218]], ![![0, 249, 196, 61, 91, 162, 159, 102, 76, 181, 136, 113, 23, 238, 211, 42, 84, 173, 144, 105, 15, 246, 203, 50, 24, 225, 220, 37, 67, 186, 135, 126, 185, 64, 125, 132, 226, 27, 38, 223, 245, 12, 49, 200, 174, 87, 106, 147, 237, 20, 41, 208, 182, 79, 114, 139, 161, 88, 101, 156, 250, 3, 62, 199, 5, 252, 193, 56, 94, 167, 154, 99, 73, 176, 141, 116, 18, 235, 214, 47, 81, 168, 149, 108, 10, 243, 206, 55, 29, 228, 217, 32, 70, 191, 130, 123, 188, 69, 120, 129, 231, 30, 35, 218, 240, 9, 52, 205, 171, 82, 111, 150, 232, 17, 44, 213, 179, 74, 119, 142, 164, 93, 96, 153, 255, 6, 59, 194, 95, 166, 155, 98, 4, 253, 192, 57, 19, 234, 215, 46, 72, 177, 140, 117, 11, 242, 207, 54, 80, 169, 148, 109, 71, 190, 131, 122, 28, 229, 216, 33, 230, 31, 34, 219, 189, 68, 121, 128, 170, 83, 110, 151, 241, 8, 53, 204, 178, 75, 118, 143, 233, 16, 45, 212, 254, 7, 58, 195, 165, 92, 97, 152, 90, 163, 158, 103, 1, 248, 197, 60, 22, 239, 210, 43, 77, 180, 137, 112, 14, 247, 202, 51, 85, 172, 145, 104, 66, 187, 134, 127, 25, 224, 221, 36, 227, 26, 39, 222, 184, 65, 124, 133, 175, 86, 107, 146, 244, 13, 48, 201, 183, 78, 115, 138, 236, 21, 40, 209, 251, 2, 63, 198, 160, 89, 100, 157], ![0, 196, 249, 61, 132, 64, 125, 185, 173, 105, 84, 144, 41, 237, 208, 20, 181, 113, 76, 136, 49, 245, 200, 12, 24, 220, 225, 37, 156, 88, 101, 161, 91, 159, 162, 102, 223, 27, 38, 226, 246, 50, 15, 203, 114, 182, 139, 79, 238, 42, 23, 211, 106, 174, 147, 87, 67, 135, 186, 126, 199, 3, 62, 250, 33, 229, 216, 28, 165, 97, 92, 152, 140, 72, 117, 177, 8, 204, 241, 53, 148, 80, 109, 169, 16, 212, 233, 45, 57, 253, 192, 4, 189, 121, 68, 128, 122, 190, 131, 71, 254, 58, 7, 195, 215, 19, 46, 234, 83, 151, 170, 110, 207, 11, 54, 242, 75, 143, 178, 118, 98, 166, 155, 95, 230, 34, 31, 219, 167, 99, 94, 154, 35, 231, 218, 30, 10, 206, 243, 55, 142, 74, 119, 179, 18, 214, 235, 47, 150, 82, 111, 171, 191, 123, 70, 130, 59, 255, 194, 6, 252, 56, 5, 193, 120, 188, 129, 69, 81, 149, 168, 108, 213, 17, 44, 232, 73, 141, 176, 116, 205, 9, 52, 240, 228, 32, 29, 217, 96, 164, 153, 93, 134, 66, 127, 187, 2, 198, 251, 63, 43, 239, 210, 22, 175, 107, 86, 146, 51, 247, 202, 14, 183, 115, 78, 138, 158, 90, 103, 163, 26, 222, 227, 39, 221, 25, 36, 224, 89, 157, 160, 100, 112, 180, 137, 77, 244, 48, 13, 201, 104, 172, 145, 85, 236, 40, 21, 209, 197, 1, 60, 248, 65, 133, 184, 124]]]

def signedOnBytes (a : Fin 2 × Bool) : Fin 256 → Fin 256 :=
  generatorOnBytes a.1 (if a.2 then 1 else 0)

set_option maxHeartbeats 4000000 in
theorem signed_generator_bytes : ∀ (j : Fin 2) (b : Bool) (x : Fin 256),
    (signedGenerator (j,b)).val (decode x) = decode (signedOnBytes (j,b) x) := by
  decide +kernel

def evalSigned (w : List (Fin 2 × Bool)) : FullGroup :=
  (w.map signedGenerator).prod

def evalBytes (w : List (Fin 2 × Bool)) (x : Fin 256) : Fin 256 :=
  w.foldr signedOnBytes x

theorem evalSigned_action (w : List (Fin 2 × Bool)) (x : Fin 256) :
    (evalSigned w).val (decode x) = decode (evalBytes w x) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (signedGenerator a).val ((evalSigned w).val (decode x)) = _
    rw [ih, signed_generator_bytes]
    rfl

def basisByte (k : Fin 8) : Fin 256 :=
  ![1,2,4,8,16,32,64,128] k

set_option maxHeartbeats 4000000 in
theorem decode_basis : ∀ k : Fin 8, decode (basisByte k) = Pi.single k 1 := by
  decide +kernel

def rootParity : Fin 8 → Fin 2 := ![0,0,1,1,0,1,0,1]

def schreierWord : Fin 2 → Fin 8 → List (Fin 2 × Bool) :=
  ![![[(0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (1, false), (0, true)], [(1, true), (0, true), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false), (1, false)], [(0, true), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, false)], [(1, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, true), (0, false)], [(1, false), (0, true), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true)], [], [(0, false), (1, false), (0, true), (0, true), (0, true), (1, true), (0, true)], [(1, false), (0, true), (1, false), (1, false), (0, true), (1, false)]], ![[(0, true), (1, true), (0, false), (0, false), (1, true), (0, false), (1, false), (0, true)], [(1, true), (0, true), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false), (1, false)], [(0, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false), (0, false)], [(0, true), (1, false), (0, true), (0, true), (1, false), (0, true), (1, false), (1, false)], [(0, true), (0, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, false), (1, true)], [], [(0, false), (1, false), (0, false), (1, true), (1, true), (1, true), (0, false), (1, false)], [(1, true), (0, false), (1, true), (1, true), (0, false), (1, true)]]]

def schreierElement (b : Fin 2) (i : Fin 8) : FullGroup :=
  (rootF 1)^b.val * rootGenerator i * ((rootF 1)^((b + rootParity i).val))⁻¹

set_option maxHeartbeats 4000000 in
theorem schreier_coordinates : ∀ (b : Fin 2) (i k : Fin 8),
    (schreierElement b i).val (decode (basisByte k)) =
      decode (evalBytes (schreierWord b i) (basisByte k)) := by
  decide +kernel

theorem schreier_identity (b : Fin 2) (i : Fin 8) :
    schreierElement b i = evalSigned (schreierWord b i) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
  intro k
  simp only [Pi.basisFun_apply]
  change (schreierElement b i).val (Pi.single k 1) =
    (evalSigned (schreierWord b i)).val (Pi.single k 1)
  rw [← decode_basis, evalSigned_action, schreier_coordinates]

end G2DerivedPermutationFiltration.VertexCoordinates.ActionGeneration
