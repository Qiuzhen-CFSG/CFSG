module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.QuotientGeometry

/-!
# An exceptional local candidate from the actual quotient

The exceptional quotient has fixed dimension one and total dimension
three, forcing the original moved dimension to be two and the cyclic
actor order to be three. Two noncommuting actor conjugates generate the
pointwise fixer of order twenty-one, so it lies in their normal closure.
Odd-order averaging supplies its actual fixed/moved splitting.

The resulting `ExceptionalCandidate` contains every exceptional local
clause of `FactorSeed` except global cross-fixation. This module does not
assert existence of a full seed. Its explicit exceptional-quotient premise
is discharged by the higher-layer odd-terminal route when the transitive
geometry branch is available.

Source: the maximal-intersection reduction for Aschbacher–Smith E.6.24,
printed p.255, and the exceptional conclusion of GLS Number 2 C.14.2,
printed pp.85–89. The original Aschbacher 1981 10.4 proof is not asserted
to have been audited.
-/

public section

open Module Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- A local exceptional candidate. Unlike FactorSeed, this does not assert
compatibility with the moved spaces of distinct ambient conjugates. -/
structure ExceptionalCandidate (ρ : Representation (ZMod 2) A W) (C B : Subgroup A) : Prop where
  contained : C ≤ B
  in_normalClosure : B ≤ normalClosure (C : Set A)
  split : IsCompl (fixedSpace ρ B) (displacementSpan ρ B ⊤)
  cyclic_card : Nat.card C = 3
  factor_card : Nat.card B = 21
  nonabelian : ¬ ∀ x y : B, x * y = y * x
  moved_dimension : finrank (ZMod 2) (displacementSpan ρ B ⊤) = 3

namespace FactorConstruction

/-- Two noncommuting subgroups, one of order three, generate an overgroup
of order twenty-one. -/
theorem sup_eq_of_noncommuting_of_card [Finite A] {C D K : Subgroup A}
    (hC : IsCyclic C) (hCK : C ≤ K) (hDK : D ≤ K)
    (hcardC : Nat.card C = 3) (hcardK : Nat.card K = 21)
    (hnc : ¬ ∀ c ∈ C, ∀ d ∈ D, Commute c d) : C ⊔ D = K := by
  let := hC
  have hle : C ⊔ D ≤ K := sup_le hCK hDK
  have hdiv : Nat.card ↥(C ⊔ D) ∣ 21 := hcardK ▸ Subgroup.card_dvd_of_le hle
  have hdivC : 3 ∣ Nat.card ↥(C ⊔ D) := hcardC ▸ Subgroup.card_dvd_of_le
    (show C ≤ C ⊔ D from le_sup_left)
  obtain ⟨r, hr⟩ := hdivC
  rw [hr] at hdiv
  have hr7 : r ∣ 7 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hdiv
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hr7 with hr1 | hr7
  · have hcard : Nat.card ↥(C ⊔ D) = 3 := by omega
    have hCH : C = C ⊔ D := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    exfalso
    apply hnc
    intro c hc d hd
    have hdC : d ∈ C := by
      rw [hCH]
      exact (show D ≤ C ⊔ D from le_sup_right) hd
    exact (Commute.all (⟨c, hc⟩ : C) ⟨d, hdC⟩).map C.subtype
  · apply Subgroup.eq_of_le_of_card_ge hle
    omega

/-- The pointwise fixer of a pair intersection has exactly that fixed space. -/
theorem fixedSpace_pointwiseFixer_intersection (a : A) (F : Submodule (ZMod 2) W)
    (hF : F = fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)) :
    fixedSpace ρ (pointwiseFixer ρ F) = F := by
  have hFU : F ≤ fixedSpace ρ C := hF.le.trans inf_le_left
  have hFD : F ≤ fixedSpace ρ (C.map (MulAut.conj a).toMonoidHom) := by
    rw [fixedSpace_map_conj]
    exact hF.le.trans inf_le_right
  have hCK := (le_pointwiseFixer_iff ρ C F).mpr hFU
  have hDK := (le_pointwiseFixer_iff ρ _ F).mpr hFD
  apply le_antisymm
  · intro v hv
    rw [hF, ← fixedSpace_map_conj]
    exact ⟨fun c => hv ⟨c, hCK c.property⟩, fun d => hv ⟨d, hDK d.property⟩⟩
  · intro v hv g
    exact (mem_pointwiseFixer ρ F g).mp g.property v hv

end FactorConstruction

variable [Finite A] [Finite W]

/-- The actual exceptional quotient supplies every local factor clause
except the global cross-fixation clause. -/
theorem Input.exceptionalCandidate_of_quotient (h : Input ρ C)
    (a : A) (hnc : ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d)
    (F : Submodule (ZMod 2) W)
    (hF : F = fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a))
    (hexc : GoldschmidtONan.ExceptionalCase (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F))) :
    ExceptionalCandidate ρ C (pointwiseFixer ρ F) := by
  have hFU : F ≤ fixedSpace ρ C := hF.le.trans inf_le_left
  have hFD : F ≤ fixedSpace ρ (C.map (MulAut.conj a).toMonoidHom) := by
    rw [fixedSpace_map_conj]
    exact hF.le.trans inf_le_right
  have hCK := (le_pointwiseFixer_iff ρ C F).mpr hFU
  have hDK := (le_pointwiseFixer_iff ρ _ F).mpr hFD
  have hfixdim := h.fixed_finrank_quotientOnFixer F hFU
  have hqdim := F.finrank_quotient_add_finrank
  have hsplitdim := Submodule.finrank_add_eq_of_isCompl h.split
  have hd : finrank (ZMod 2) (displacementSpan ρ C ⊤) = 2 := by
    have h1 := hexc.1
    have h3 := hexc.2.1
    omega
  have hC3 : Nat.card C = 3 := by rw [h.card_eq, hd]; norm_num
  have hjoin := sup_eq_of_noncommuting_of_card h.cyclic hCK hDK hC3 hexc.2.2.1 hnc
  have hKnormal : pointwiseFixer ρ F ≤ normalClosure (C : Set A) := by
    rw [← hjoin]
    apply sup_le le_normalClosure
    rintro _ ⟨c, hc, rfl⟩
    exact (inferInstance : (normalClosure (C : Set A)).Normal).conj_mem c
      (le_normalClosure hc) a
  have hodd : Odd (Nat.card (pointwiseFixer ρ F)) := by rw [hexc.2.2.1]; decide
  have hsplit : IsCompl (fixedSpace ρ (pointwiseFixer ρ F))
      (displacementSpan ρ (pointwiseFixer ρ F) ⊤) :=
    GoldschmidtONan.isCompl_fixed_moved_of_odd hodd
  refine ⟨hCK, hKnormal, hsplit, hC3, hexc.2.2.1, hexc.2.2.2, ?_⟩
  have hh := Submodule.finrank_add_eq_of_isCompl hsplit
  rw [fixedSpace_pointwiseFixer_intersection a F hF] at hh
  have h3 := hexc.2.1
  omega

end Representation.RegularCyclicNormalClosure
