module
public import Theory.SpecificGroups.Rudvalis.SylowAutomorphismSolvability.InvolutionFibers.Quotient
public import Theory.GroupTheory.FrattiniInvolutionPoints
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Nilpotent

/-!
# Solvable automorphisms of the actual Rudvalis Sylow candidate

Exactly three nonidentity Frattini cosets have square-one representatives.
They generate the quotient, so the intrinsic action on these points has
the same kernel as the full Frattini action. The point permutation group
is S₃, and the Burnside basis-kernel theorem makes the kernel a two-group.
Solvability follows by extension, with no profile-count or realization premise.

Source: the original Rudvalis Sylow word certificates and Frattini quotient
in the imported modules. The source consumer is Aschbacher--Smith A.3.9,
pp.45--46; only solvability of this actual Sylow automorphism group is needed.
-/

namespace Rudvalis.SylowAutomorphismSolvability.InvolutionFibers
open Subgroup FrattiniCoordinates
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

@[expose] public def coordinateBasis (i : Fin 3) : Coordinate :=
  coordinateGenerator (i.castLE (by decide))

private theorem basis_zero : coordinateBasis 0 = coordinateGenerator 0 := by decide +kernel
private theorem basis_one : coordinateBasis 1 = coordinateGenerator 1 := by decide +kernel
private theorem basis_two : coordinateBasis 2 = coordinateGenerator 2 := by decide +kernel

private theorem basis_ne_one : ∀ i, coordinateBasis i ≠ 1 := by decide +kernel
private theorem basis_injective : Function.Injective coordinateBasis := by
  change ∀ i j, coordinateBasis i = coordinateBasis j → i = j
  decide +kernel
private theorem basis_word : ∀ v : Coordinate,
    (coordinateBasis 0 * coordinateBasis 2) ^ (v.toAdd 0).val *
      coordinateBasis 1 ^ (v.toAdd 1).val * coordinateBasis 0 ^ (v.toAdd 2).val = v := by
  decide +kernel

public theorem coordinateBasis_generates : closure (Set.range coordinateBasis) = ⊤ := by
  apply top_unique
  intro v _
  rw [← basis_word v]
  have h (i : Fin 3) : coordinateBasis i ∈ closure (Set.range coordinateBasis) :=
    subset_closure ⟨i, rfl⟩
  exact mul_mem (mul_mem (pow_mem (mul_mem (h 0) (h 2)) _) (pow_mem (h 1) _))
    (pow_mem (h 0) _)

/-- The intrinsic nonidentity involution cosets are three generating points. -/
public theorem frattini_involution_points_card_and_generate :
    Nat.card (frattiniInvolutionPoints Representative) = 3 ∧
      closure (frattiniInvolutionPoints Representative) = ⊤ := by
  classical
  obtain ⟨f, hf, hker, hgen⟩ := exists_frattini_coordinate
  let e : (Representative ⧸ frattini Representative) ≃* Coordinate :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he (x : Representative) : e (QuotientGroup.mk' (frattini Representative) x) = f x := rfl
  have hpoints (v : Representative ⧸ frattini Representative) :
      v ∈ frattiniInvolutionPoints Representative ↔ e v ∈ Set.range coordinateBasis := by
    rw [mem_frattiniInvolutionPoints]
    constructor
    · rintro ⟨hne, x, hx, rfl⟩
      have hne' : f x ≠ 1 := by rw [← he]; exact fun h => hne (e.map_eq_one_iff.mp h)
      have hv := (involution_fiber_iff f hgen (f x) hne').mp ⟨x, rfl, hx⟩
      rcases hv with h | h | h
      · exact ⟨0, by rw [basis_zero, he]; exact h.symm⟩
      · exact ⟨1, by rw [basis_one, he]; exact h.symm⟩
      · exact ⟨2, by rw [basis_two, he]; exact h.symm⟩
    · rintro ⟨i, hi⟩
      have hn : e v ≠ 1 := hi ▸ basis_ne_one i
      refine ⟨fun h => hn (h ▸ e.map_one), ?_⟩
      have hv : e v = coordinateGenerator 0 ∨ e v = coordinateGenerator 1 ∨
          e v = coordinateGenerator 2 := by
        fin_cases i
        · exact Or.inl hi.symm
        · exact Or.inr (Or.inl hi.symm)
        · exact Or.inr (Or.inr hi.symm)
      obtain ⟨x, hx, hx2⟩ := (involution_fiber_iff f hgen (e v) hn).mpr hv
      exact ⟨x, hx2, e.injective ((he x).trans hx)⟩
  let b : Fin 3 → frattiniInvolutionPoints Representative := fun i =>
    ⟨e.symm (coordinateBasis i), (hpoints _).mpr ⟨i, (e.apply_symm_apply _).symm⟩⟩
  have hb : Function.Bijective b := by
    constructor
    · intro i j hij
      apply basis_injective
      have h := congrArg (fun v : frattiniInvolutionPoints Representative => e v.val) hij
      simpa only [b, e.apply_symm_apply] using h
    · intro v
      obtain ⟨i, hi⟩ := (hpoints v).mp v.property
      refine ⟨i, Subtype.ext ?_⟩
      apply e.injective
      simpa only [b, e.apply_symm_apply] using hi
  constructor
  · rw [← Nat.card_congr (Equiv.ofBijective b hb)]
    exact Nat.card_fin 3
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
    have himage : e '' frattiniInvolutionPoints Representative = Set.range coordinateBasis := by
      ext v
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (hpoints q).mp hq
      · intro hv
        exact ⟨e.symm v, (hpoints _).mpr (by simpa only [e.apply_symm_apply] using hv),
          e.apply_symm_apply v⟩
    change closure (e '' frattiniInvolutionPoints Representative) = ⊤
    rw [himage, coordinateBasis_generates]

/-- The actual automorphism action on the three involution points has precisely
its Frattini-action kernel. -/
public theorem exists_three_point_action :
    ∃ ρ : MulAut Representative →* Equiv.Perm (Fin 3),
      ρ.ker = (quotientAut (frattini Representative)).ker := by
  obtain ⟨hc, hg⟩ := frattini_involution_points_card_and_generate
  let action := frattiniInvolutionPointAction (MonoidHom.id (MulAut Representative))
  let e := Finite.equivFinOfCardEq hc
  refine ⟨e.permCongrHom.toMonoidHom.comp action, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective]
  simpa only [MonoidHom.comp_id] using
    frattiniInvolutionPointAction_kernel (MonoidHom.id (MulAut Representative)) hg

private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide +kernel)
  apply Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

/-- The full automorphism group of the original Rudvalis Sylow candidate is
solvable, by its three-point image and two-group Frattini kernel. -/
public theorem candidate_mulAut_isSolvable : Group.IsSolvable (MulAut Representative) := by
  obtain ⟨ρ, hρ⟩ := exists_three_point_action
  have hk : IsPGroup 2 ρ.ker := by
    rw [hρ]
    exact isPGroup_quotientAut_frattini_kernel candidate_isTwoGroup
  let := hk.isNilpotent
  let := symmetric_three_solvable
  apply Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ
  rw [Subgroup.range_subtype]

end Rudvalis.SylowAutomorphismSolvability.InvolutionFibers
