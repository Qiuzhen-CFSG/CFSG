module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Generators
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Normalizes
/-!
# Literal words for the native eight automizer

Three short words in N(F), conjugated by one explicit native element,
realize the finite automizer action. Membership in the actual conjugate F-normalizer is proved
here from the native words; their eight-dimensional actions are separate checked
matrix equations. Source: KW (1988), Corollary 2.3.6.
-/
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Subgroup
attribute [local irreducible] modelGroup matrixA matrixB
def sourceX : Model := Cardinality.localX matrixA_mul_self matrixB_pow_four
def sourceY : Model := Cardinality.localY matrixA_mul_self matrixB_pow_four
def xy : Model := sourceX * sourceY
def xyy : Model := xy * sourceY
def p2 : Model := xyy * xyy
def p4 : Model := p2 * p2
def cx : Model := p4 * sourceX
def cxy : Model := cx * sourceY
def cxyx : Model := cxy * sourceX
def c : Model := cxyx * (ElementaryEightGeometry.Loewy.nativeGenerator 0)
def ci : Model := c⁻¹
def n0i : Model := LinearFive.NativeNormalizer.n0⁻¹
def n1i : Model := LinearFive.NativeNormalizer.n1⁻¹
def cu0 : Model := c * LinearFive.NativeNormalizer.n0
def actor0 : Model := cu0 * ci
def u1_0 : Model := n1i * n1i
def u1_1 : Model := u1_0 * n1i
def u1_2 : Model := u1_1 * LinearFive.NativeNormalizer.n0
def u1_3 : Model := u1_2 * LinearFive.NativeNormalizer.n1
def u1_4 : Model := u1_3 * LinearFive.NativeNormalizer.n1
def u1_5 : Model := u1_4 * LinearFive.NativeNormalizer.n1
def cu1 : Model := c * u1_5
def actor1 : Model := cu1 * ci
def u2_0 : Model := n1i * n0i
def u2_1 : Model := u2_0 * n1i
def u2_2 : Model := u2_1 * n0i
def u2_3 : Model := u2_2 * LinearFive.NativeNormalizer.n1
def u2_4 : Model := u2_3 * LinearFive.NativeNormalizer.n0
def u2_5 : Model := u2_4 * LinearFive.NativeNormalizer.n1
def u2_6 : Model := u2_5 * LinearFive.NativeNormalizer.n0
def u2_7 : Model := u2_6 * LinearFive.NativeNormalizer.n1
def cu2 : Model := c * u2_7
def actor2 : Model := cu2 * ci
def ag : Model := Janko4.a * (ElementaryEightGeometry.Loewy.nativeGenerator 6)
def ag2 : Model := ag * ag
def ag4 : Model := ag2 * ag2
def ag8 : Model := ag4 * ag4
def ag10 : Model := ag8 * ag2

def actor : Fin 3 → Model := ![actor0,actor1,actor2]
def target : Subgroup Model :=
  (normalizer (LinearFive.F : Set Model)).map (MulAut.conj c).toMonoidHom

private theorem n0_mem : LinearFive.NativeNormalizer.n0 ∈ normalizer (LinearFive.F : Set Model) :=
  LinearFive.NativeNormalizer.element_mem_normalizer 0
private theorem n1_mem : LinearFive.NativeNormalizer.n1 ∈ normalizer (LinearFive.F : Set Model) :=
  LinearFive.NativeNormalizer.element_mem_normalizer 1
private theorem n0i_mem : n0i ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).inv_mem n0_mem
private theorem n1i_mem : n1i ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).inv_mem n1_mem
private theorem u1_0_mem : u1_0 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem n1i_mem n1i_mem
private theorem u1_1_mem : u1_1 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u1_0_mem n1i_mem
private theorem u1_2_mem : u1_2 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u1_1_mem n0_mem
private theorem u1_3_mem : u1_3 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u1_2_mem n1_mem
private theorem u1_4_mem : u1_4 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u1_3_mem n1_mem
private theorem u1_5_mem : u1_5 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u1_4_mem n1_mem
private theorem u2_0_mem : u2_0 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem n1i_mem n0i_mem
private theorem u2_1_mem : u2_1 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u2_0_mem n1i_mem
private theorem u2_2_mem : u2_2 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u2_1_mem n0i_mem
private theorem u2_3_mem : u2_3 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u2_2_mem n1_mem
private theorem u2_4_mem : u2_4 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u2_3_mem n0_mem
private theorem u2_5_mem : u2_5 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u2_4_mem n1_mem
private theorem u2_6_mem : u2_6 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u2_5_mem n0_mem
private theorem u2_7_mem : u2_7 ∈ normalizer (LinearFive.F : Set Model) :=
  (normalizer _).mul_mem u2_6_mem n1_mem

theorem actor_mem_target (i : Fin 3) : actor i ∈ target := by
  fin_cases i
  · exact Subgroup.mem_map.mpr ⟨LinearFive.NativeNormalizer.n0, n0_mem, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨u1_5, u1_5_mem, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨u2_7, u2_7_mem, rfl⟩
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
