module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import Theory.Frattini.NormalImage
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The Frattini factors in the first local quotient

Point stabilizers show that symmetric groups have trivial Frattini subgroup;
the two projections give this for S₃ × S₃. Consequently an actual isomorphism
H/O₂(H) ≃ S₃ × S₃ also identifies the quotient by O₂,Φ(H).
For the extraspecial alternative, its center has prime order, contains the
Frattini subgroup and cannot have trivial intersection with it. This retains
the central factor until the Frattini quotient is taken.

Source: Aschbacher–Smith, 15.3.7 and 15.3.11(5i), printed pp.1122–1124.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

/-- Point stabilizers and the two projections separate every nonidentity element. -/
theorem symmetricThreeSquare_frattini : frattini (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = ⊥ := by
  have h : frattini (Equiv.Perm (Fin 3)) = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    apply Equiv.ext
    intro a
    exact frattini_le_coatom
      (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (Equiv.Perm (Fin 3)) a) hg
  apply le_antisymm _ bot_le
  intro g hg
  apply Prod.ext
  · have hf := frattini_le_comap_frattini_of_surjective
      (φ := MonoidHom.fst (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))) Prod.fst_surjective hg
    change g.1 ∈ frattini (Equiv.Perm (Fin 3)) at hf
    simpa only [h, mem_bot, Prod.fst_one, Prod.snd_one] using hf
  · have hf := frattini_le_comap_frattini_of_surjective
      (φ := MonoidHom.snd (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))) Prod.snd_surjective hg
    change g.2 ∈ frattini (Equiv.Perm (Fin 3)) at hf
    simpa only [h, mem_bot, Prod.fst_one, Prod.snd_one] using hf

/-- An actual S₃ × S₃ two-core quotient has no further Frattini factor. -/
theorem coreFrattini_eq_twoCore_of_equiv {H : Type*} [Group H]
    (e : (H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    coreFrattiniSubgroup H = pCore 2 H := by
  have hf := symmetricThreeSquare_frattini
  have he : frattini (H ⧸ pCore 2 H) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    apply e.injective
    have ht := frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective hx
    simpa [hf] using ht
  change (frattini (H ⧸ pCore 2 H)).comap _ = _
  rw [he]
  exact QuotientGroup.ker_mk' _

/-- The intrinsic conversion also used by the second-choice extraspecial branch. -/
noncomputable def coreFrattiniQuotientEquivOfTwoCore {H : Type*} [Group H]
    (e : (H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    (H ⧸ coreFrattiniSubgroup H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (QuotientGroup.quotientMulEquivOfEq (coreFrattini_eq_twoCore_of_equiv e)).trans e


/-- Existence form of the intrinsic conversion, for either local choice. -/
theorem coreFrattini_quotient_of_twoCore {H : Type*} [Group H]
    (h : Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty ((H ⧸ coreFrattiniSubgroup H) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨e⟩ := h
  exact ⟨coreFrattiniQuotientEquivOfTwoCore e⟩

/-- The central order-three factor is retained inside the Frattini kernel. -/
theorem extraspecial27_center_le_frattini {E : Type*} [Group E] [Finite E] (hE : IsExtraspecial 3 E)
    (hc : Nat.card E = 27) : center E ≤ frattini E := by
  let := hE
  let : Fact (IsPGroup 3 E) := ⟨IsExtraspecial.isPGroup 3 E⟩
  let := IsExtraspecial.quotient_elementary_abelian 3 E
  let : Fact (IsPGroup 3 (E ⧸ center E)) := ⟨IsExtraspecial.quotient_isPGroup 3 E⟩
  have hle : frattini E ≤ center E := by
    have h := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective (center E))
    rw [frattini_eq_bot_of_isElementaryAbelian (R := E ⧸ center E) (p := 3)] at h
    exact h.trans_eq (QuotientGroup.ker_mk' _)
  have hne : frattini E ≠ ⊥ := by
    intro he
    let := (frattini_eq_bot_iff_isElementaryAbelian (p := 3)).mp he
    have hz := IsExtraspecial.center_order_p 3 E
    rw [center_eq_top, Nat.card_congr (topEquiv (G := E)).toEquiv, hc] at hz
    norm_num at hz
  let : Fact (Nat.Prime (Nat.card (center E))) := ⟨by
    rw [IsExtraspecial.center_order_p 3 E]
    decide⟩
  rcases ((frattini E).subgroupOf (center E)).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have := congrArg (fun U : Subgroup (center E) => U.map (center E).subtype) hb
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at this
    exact False.elim (hne this)
  · have := congrArg (fun U : Subgroup (center E) => U.map (center E).subtype) ht
    rw [map_subgroupOf_eq_of_le hle, ← MonoidHom.range_eq_map, range_subtype] at this
    exact this.ge

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
end
