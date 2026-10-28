/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechSextetSigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSextetVectors

/-!
The action of Golay sign changes on sextet crosses.
Code orthogonality makes tetrad sign parity independent of the chosen part and determines the new cross parity.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def tetradSignParity (c : BinaryWord) (T : Finset Omega) : Bit := ∑ i : T, c i

theorem tetradSignParity_dot (c : BinaryWord) (T : Finset Omega) :
    binaryDot c (supportWord T) = tetradSignParity c T := by
  simp only [binaryDot_apply,supportWord,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  exact (Finset.sum_coe_sort T c).symm

theorem sextetSignParity_independent (S : UnorderedSextet) (c : golay)
    (T U : {T // T ∈ S.val}) : tetradSignParity c.val T.val = tetradSignParity c.val U.val := by
  have ho := golay_selfOrthogonal (sextet_support_difference_mem S T U) c.val c.prop
  change binaryDot c.val (supportWord T.val - supportWord U.val) = 0 at ho
  rw [map_sub,tetradSignParity_dot,tetradSignParity_dot] at ho
  exact sub_eq_zero.mp ho

theorem signChange_tetradFour (c : BinaryWord) (T : Finset Omega) (s : T → Bit) :
    signChange c (tetradFourVector T s) = tetradFourVector T (fun i => s i + c i) := by
  ext i
  simp only [signChange,LinearMap.coe_mk,AddHom.coe_mk,tetradFourVector_apply,signedSupport]
  by_cases hi : i ∈ T
  · simp only [dif_pos hi]
    rcases bit_cases (s ⟨i,hi⟩) with hs | hs <;> rcases bit_cases (c i) with hc | hc <;> simp [hs,hc]
  · simp [hi]

theorem sextetCross_sign_action (S : UnorderedSextet) (b : Bit) (c : golay)
    (T : {T // T ∈ S.val}) :
    crossAction (signIsometry c) (sextetCross S b) = sextetCross S (b + tetradSignParity c.val T.val) := by
  let p := sextetBaseParameter S b
  let d := b + tetradSignParity c.val T.val
  let t : ParitySigns p.1.val d := ⟨fun i => p.2.val i + c.val i,by
    rw [Finset.sum_add_distrib,p.2.prop]
    exact congrArg (b + ·) (sextetSignParity_independent S c p.1 T)⟩
  let r : SextetVectorParameters S d := ⟨p.1,t⟩
  have hv : (signIsometry c).val (sextetLatticeVector S b p) = sextetLatticeVector S d r := by
    apply Subtype.ext
    exact signChange_tetradFour c.val p.1.val p.2.val
  apply Subtype.ext
  change leechModTwoRepresentation (signIsometry c) (leechReduction (sextetLatticeVector S b p)) = _
  rw [leechModTwoRepresentation_reduce,hv]
  exact sextetVector_class S d r (sextetBaseParameter S d)

end Atlas.Lattices
