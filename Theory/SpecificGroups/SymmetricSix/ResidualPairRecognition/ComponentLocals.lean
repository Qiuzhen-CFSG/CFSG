module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition

/-!
# Local centralizers in the surviving A₆/S₆ model

For both standard index-three Sylow overgroups in S₆, the two-residual is
an embedded A₄. Its centralizer is the odd central involution of the parabolic:
(01) for the duad and (01)(23)(45) for the syntheme. In particular this
centralizer has order two, lies in the common Sylow subgroup, centralizes the
whole parabolic, and meets A₆ trivially.

The even parabolics are actual copies of S₄. The duad model is the established
sign-coupled action on 2+4 letters. For the syntheme we extend the existing
A₄ edge action to the full tetrahedral S₄ action; injectivity and order give
the equivalence. All finite action checks use kernel reduction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.4.18, printed p.1163, and I.5.
The literal factor `Z ∩ L` printed in that local calculation is not correct
in the S₆ model. `printed_factor_obstruction` exhibits the double
transposition (23)(45) in that factor which does not centralize the residual.
The useful central line is `C_Z(Y)`. This obstruction concerns the local
calculation, not the theorem: its full mixed configuration is contradictory.
-/

@[expose] public section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local instance : Fintype S6 := fintypePerm
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance : Fintype A := Subtype.fintype _

def duadFlip : S6 := Equiv.swap 0 1
def synthemeFlip : S6 := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

private theorem duad_centralizer_test : ∀ g : S6,
    (∀ a : A, duadHom a * g = g * duadHom a) ↔ g = 1 ∨ g = duadFlip := by
  decide +kernel

private theorem syntheme_centralizer_test : ∀ g : S6,
    (∀ a : A, synthemeHom a * g = g * synthemeHom a) ↔ g = 1 ∨ g = synthemeFlip := by
  decide +kernel

private theorem mem_centralizer_range_iff {D : Type*} [Group D] (f : D →* S6) (g : S6) :
    g ∈ centralizer (f.range : Set S6) ↔ ∀ a : D, f a * g = g * f a := by
  rw [mem_centralizer_iff]
  constructor
  · intro h a
    exact h _ ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    exact h a

private theorem mem_zpowers_two {G : Type*} [Group G] [Finite G] {x g : G}
    (hx : orderOf x = 2) : g ∈ zpowers x ↔ g = 1 ∨ g = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, h⟩
    have he : n = 0 ∨ n = 1 := by omega
    rcases he with rfl | rfl <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, pow_zero x⟩
    · exact ⟨1, by omega, pow_one _⟩

theorem duadFlip_order : orderOf duadFlip = 2 := by
  exact orderOf_eq_prime (by decide) (by decide)
theorem synthemeFlip_order : orderOf synthemeFlip = 2 := by
  exact orderOf_eq_prime (by decide) (by decide)

theorem centralizer_duad : centralizer (duadHom.range : Set S6) = zpowers duadFlip := by
  ext g
  rw [mem_centralizer_range_iff, duad_centralizer_test, mem_zpowers_two duadFlip_order]

theorem centralizer_syntheme : centralizer (synthemeHom.range : Set S6) = zpowers synthemeFlip := by
  ext g
  rw [mem_centralizer_range_iff, syntheme_centralizer_test, mem_zpowers_two synthemeFlip_order]

private theorem duad_flip_central : ∀ g : duadStabilizer,
    (g : S6) * duadFlip = duadFlip * g := by decide +kernel
private theorem syntheme_flip_central : ∀ g : synthemeStabilizer,
    (g : S6) * synthemeFlip = synthemeFlip * g := by decide +kernel

theorem duad_centralizer_le_center : centralizer (duadHom.range : Set S6) ≤
    centralizer (duadStabilizer : Set S6) := by
  rw [centralizer_duad]
  apply zpowers_le.mpr
  exact mem_centralizer_iff.mpr fun g hg => duad_flip_central ⟨g, hg⟩

theorem syntheme_centralizer_le_center : centralizer (synthemeHom.range : Set S6) ≤
    centralizer (synthemeStabilizer : Set S6) := by
  rw [centralizer_syntheme]
  apply zpowers_le.mpr
  exact mem_centralizer_iff.mpr fun g hg => syntheme_flip_central ⟨g, hg⟩

theorem duad_centralizer_le_borel : centralizer (duadHom.range : Set S6) ≤ borel := by
  rw [centralizer_duad]
  exact zpowers_le.mpr (by decide)

theorem syntheme_centralizer_le_borel : centralizer (synthemeHom.range : Set S6) ≤ borel := by
  rw [centralizer_syntheme]
  exact zpowers_le.mpr (by decide)

theorem duad_centralizer_disjoint_alternating :
    Disjoint (centralizer (duadHom.range : Set S6)) A6 := by
  apply disjoint_iff_inf_le.mpr
  intro g hg
  rw [centralizer_duad, mem_inf, mem_zpowers_two duadFlip_order] at hg
  rcases hg.1 with rfl | rfl
  · exact one_mem _
  · exact (show duadFlip ∉ A6 by decide) hg.2 |>.elim

theorem syntheme_centralizer_disjoint_alternating :
    Disjoint (centralizer (synthemeHom.range : Set S6)) A6 := by
  apply disjoint_iff_inf_le.mpr
  intro g hg
  rw [centralizer_syntheme, mem_inf, mem_zpowers_two synthemeFlip_order] at hg
  rcases hg.1 with rfl | rfl
  · exact one_mem _
  · exact (show synthemeFlip ∉ A6 by decide) hg.2 |>.elim

/-- The full tetrahedral edge action, extending the residual A₄ action. -/
def edgeHom : Equiv.Perm (Fin 4) →* S6 where
  toFun (a : Equiv.Perm (Fin 4)) := {
    toFun i := edgeIndex ((edge i).image a)
    invFun i := edgeIndex ((edge i).image (a⁻¹ : Equiv.Perm (Fin 4)))
    left_inv := by revert a; decide +kernel
    right_inv := by revert a; decide +kernel }
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem edgeHom_on_alternating (a : A) : edgeHom a.val = synthemeHom a := rfl

theorem edgeHom_injective : Function.Injective edgeHom := by decide +kernel

theorem edgeHom_even : ∀ a, edgeHom a ∈ A6 := by
  change ∀ a, (edgeHom a).sign = 1
  decide +kernel

theorem edgeHom_mem : ∀ a, edgeHom a ∈ synthemeStabilizer := by decide +kernel

def edgeToAlternatingParabolic : Equiv.Perm (Fin 4) →* a6SynthemeStabilizer :=
  (edgeHom.codRestrict A6 edgeHom_even).codRestrict _ edgeHom_mem

theorem a6Syntheme_card : Nat.card a6SynthemeStabilizer = 24 := by
  have h := a6SynthemeStabilizer.card_mul_index
  rw [a6SynthemeStabilizer_index, a6_order] at h
  omega

noncomputable def edgeEquiv : Equiv.Perm (Fin 4) ≃* a6SynthemeStabilizer :=
  MulEquiv.ofBijective edgeToAlternatingParabolic
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h =>
      edgeHom_injective (congrArg (fun x : a6SynthemeStabilizer => x.val.val) h), by
        rw [a6Syntheme_card, Nat.card_eq_fintype_card]
        decide⟩)

private noncomputable def parabolicInfEquiv (H : Subgroup S6) : H.comap A6.subtype ≃* ↥(H ⊓ A6) :=
  ((H.subgroupOf A6).equivMapOfInjective A6.subtype A6.subtype_injective).trans
    (MulEquiv.subgroupCongr (subgroupOf_map_subtype H A6))

theorem duad_alternating_equiv : Nonempty (↥(duadStabilizer ⊓ A6) ≃* Equiv.Perm (Fin 4)) :=
  ⟨(parabolicInfEquiv duadStabilizer).symm.trans a6DuadModelEquiv.symm⟩

theorem syntheme_alternating_equiv : Nonempty (↥(synthemeStabilizer ⊓ A6) ≃* Equiv.Perm (Fin 4)) :=
  ⟨(parabolicInfEquiv synthemeStabilizer).symm.trans edgeEquiv.symm⟩

/-- The centralizer of either canonical residual is the odd central line,
not the line obtained by intersecting the Sylow center with A₆. -/
theorem canonical_local_structure (H : Subgroup S6)
    (h : H = duadStabilizer ∨ H = synthemeStabilizer) :
    let Y := (pResidual 2 H).map H.subtype
    Nonempty (Y ≃* A) ∧ Nat.card (centralizer (Y : Set S6)) = 2 ∧
      centralizer (Y : Set S6) ≤ borel ∧
      centralizer (Y : Set S6) ≤ centralizer (H : Set S6) ∧
      Disjoint (centralizer (Y : Set S6)) A6 ∧
      Nonempty (↥(H ⊓ A6) ≃* Equiv.Perm (Fin 4)) := by
  dsimp only
  rcases h with rfl | rfl
  · rw [residual_duad]
    exact ⟨⟨(MonoidHom.ofInjective duadHom_injective).symm⟩,
      by rw [centralizer_duad, Nat.card_zpowers, duadFlip_order],
      duad_centralizer_le_borel, duad_centralizer_le_center,
      duad_centralizer_disjoint_alternating, duad_alternating_equiv⟩
  · rw [residual_syntheme]
    exact ⟨⟨(MonoidHom.ofInjective synthemeHom_injective).symm⟩,
      by rw [centralizer_syntheme, Nat.card_zpowers, synthemeFlip_order],
      syntheme_centralizer_le_borel, syntheme_centralizer_le_center,
      syntheme_centralizer_disjoint_alternating, syntheme_alternating_equiv⟩

/-- The literal factor `Z ∩ A₆` in the printed local calculation fails
already in the standard duad model. This does not refute 15.4.18: its full
mixed configuration is a contradiction hypothesis. -/
theorem printed_factor_obstruction :
    borel ⊓ centralizer (duadHom.range : Set S6) ≠
      (borel ⊓ centralizer (A6 : Set S6)) ⊔
        ((borel ⊓ centralizer (borel : Set S6)) ⊓ A6) := by
  let w : S6 := Equiv.swap 2 3 * Equiv.swap 4 5
  have hwB : w ∈ borel := by decide
  have hwC : w ∈ centralizer (borel : Set S6) := by
    apply mem_centralizer_iff.mpr
    intro b hb
    exact (show ∀ b : borel, (b : S6) * w = w * b by decide +kernel) ⟨b, hb⟩
  have hwA : w ∈ A6 := by decide
  have hwN : w ∉ centralizer (duadHom.range : Set S6) := by
    rw [centralizer_duad, mem_zpowers_two duadFlip_order]
    decide
  intro h
  have hw := (show ((borel ⊓ centralizer (borel : Set S6)) ⊓ A6) ≤
      (borel ⊓ centralizer (A6 : Set S6)) ⊔
        ((borel ⊓ centralizer (borel : Set S6)) ⊓ A6) from le_sup_right)
      (show w ∈ ((borel ⊓ centralizer (borel : Set S6)) ⊓ A6) from ⟨⟨hwB, hwC⟩, hwA⟩)
  rw [← h] at hw
  exact hwN hw.2

end Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
