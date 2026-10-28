module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.ModelExclusions
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.Noncentral
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The noncentral-omega source recognition needed in 15.4.15

When both characteristic-two vertices of a core-free Goldschmidt triple move
the omega-center of their common Sylow subgroup, Stellmacher (8.2) identifies
each vertex with S₄ or C₂ × S₄. A Sylow subgroup of S₄ is dihedral of order
eight, with center of order two. Consequently an omega-center of order four
excludes S₄ and gives both actual C₂ × S₄ identifications directly.

This uses the source noncentrality available in Chapter 15 and does not assume
the universal F.6.5 enumeration. Source: Aschbacher–Smith 15.4.14–15, printed
pp.1161–1162; Stellmacher, Journal of Algebra 190 (1997), (7.5) and (8.2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A Sylow omega-center of order four rules out the actual symmetric-four group. -/
theorem not_symmetric_four_of_omega_center_card (T : Sylow 2 G)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    ¬ Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  rintro ⟨e⟩
  let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let eT : T ≃* S := (T : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  obtain ⟨eS⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four S
  have hc : Nat.card (center T) = 2 :=
    DihedralGroup.center_card_of_equiv (n := 2) (by decide) (eT.trans eS)
  have hb := omega_center_card_le_center (T : Subgroup G)
  rw [hZ, hc] at hb
  omega

private def cyclicTwoEquiv : Multiplicative (ZMod 2) ≃* Equiv.Perm (Fin 2) :=
  mulEquivOfPrimeCardEq (p := 2) (by exact Nat.card_zmod 2)
    (by norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])

/-- Both noncentral vertices are identified without the general Goldschmidt
classification; their actual overlap retains its omega-center of order four. -/
theorem goldschmidt_identification_of_noncentral_omega {A B : Subgroup G}
    (h : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hmoveA : ⁅A, omegaOneCenterAmbient (A ⊓ B)⁆ ≠ ⊥)
    (hmoveB : ⁅B, omegaOneCenterAmbient (A ⊓ B)⁆ ≠ ⊥)
    (hZ : Nat.card (omegaOneCenterAmbient (A ⊓ B)) = 4) :
    Nonempty (A ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) ∧
      Nonempty (B ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) := by
  obtain ⟨hmA, hmB⟩ := h.local_models_of_noncentral_omega hcore hA hB hmoveA hmoveB
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have convert_model (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
      (hm : Later.IsModel P Later.S4 ∨ Later.IsModel P (Later.C2 × Later.S4)) :
      Nonempty (P ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := (show Nonempty (P ≃* Later.S4) from hm)
      have hz : Nat.card (omegaOneCenterAmbient
          (T.subtype hTP : Subgroup P)) = 4 := by
        rw [show (T.subtype hTP : Subgroup P) = (T : Subgroup G).subgroupOf P from rfl,
          omega_center_card_subgroupOf hTP, ← hT]
        exact hZ
      exact (not_symmetric_four_of_omega_center_card (T.subtype hTP) hz ⟨e⟩).elim
    · obtain ⟨e⟩ := (show Nonempty (P ≃* Later.C2 × Later.S4) from hm)
      exact ⟨e.trans (cyclicTwoEquiv.prodCongr (MulEquiv.refl _))⟩
  exact ⟨convert_model A (hT.symm.le.trans inf_le_left) hmA,
    convert_model B (hT.symm.le.trans inf_le_right) hmB⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
