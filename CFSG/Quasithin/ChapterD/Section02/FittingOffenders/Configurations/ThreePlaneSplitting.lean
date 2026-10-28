module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.ThreePlaneSplitting.Factors
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.ThreePlaneSplitting.PlaneAction

/-!
# The three invariant support planes in D.2.14

Assume the exact reduced action, cubic ratio greater than one, and that
every invariant order-three line has a binary plane as its moved space.
Hyperplane centralizers generate the core; small-support rigidity and
coprime splitting construct its marked factors and the literal direct sum
of their supports. Each support has one fixed and one moved dimension
under the actor. Two factors would give ratio one, so there are three.

This proves the invariant-plane branch of Aschbacher--Smith D.2.14(3),
(6),(7)(ii), printed p.187, on the original reduced representation. The
invariant-line reduction supplying the small-support hypothesis belongs
to the separate source assembly. No factor, independence, generation,
or fixed-line premise is retained in the main theorem.
-/

public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The invariant-plane branch of D.2.14(3),(7)(ii), retaining every
marked factor and every literal support in the original representation. -/
theorem Reduced.three_plane_splitting {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hlow : 1 < cubicRatio ρ)
    (hsmall : SmallInvariantSupports ρ P A) :
    ∃ d : SupportFactors ρ P s, s = 3 ∧ ∀ i,
      A ≤ Subgroup.normalizer (d.ambient i : Set G) ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator ρ (subspaceCommutator ρ ⊤ (d.ambient i)) A) = 1 ∧
      A ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ (d.ambient i)) ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator ρ ⊤ (d.ambient i) ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) = 1 := by
  obtain ⟨d, hn⟩ := h.exists_invariant_supportFactors ρ hsmall
  have hline (i : Fin s) : IsInvariantLine P A (d.ambient i) := by
    refine ⟨Subgroup.map_subtype_le _, ?_, hn i⟩
    exact (Subgroup.card_map_of_injective P.subtype_injective).trans (d.card_factor i)
  have hd (i : Fin s) := h.invariant_plane_data ρ (hline i) (d.support_dim i)
  have hcodim : fixedCodim ρ A = s := d.fixedCodim_eq_of_fixed_lines ρ A
    (fun i => (hd i).1) (fun i => (hd i).2.2)
  have hs : s = 3 := by
    rcases h.rank_cases with hs | hs
    · have hone : cubicRatio ρ = 1 := by
        rw [← h.starred.1.2.2.2, actionRatio, hcodim, hs, h.actor_rank ρ]
        exact ENNReal.div_self (by norm_num) (by simp)
      rw [hone] at hlow
      exact (lt_irrefl _ hlow).elim
    · exact hs
  exact ⟨d, hs, fun i => ⟨hn i, (hd i).2.1, (hd i).1, (hd i).2.2⟩⟩

/-- The constructed invariant configuration attains the genuine global
cubic minimum, with the fixed-line premises discharged. -/
theorem Reduced.small_invariant_support_ratio {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hlow : 1 < cubicRatio ρ)
    (hsmall : SmallInvariantSupports ρ P A) :
    s = 3 ∧ fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 := by
  obtain ⟨d, hs, hd⟩ := h.three_plane_splitting ρ hlow hsmall
  have hc := (d.fixedCodim_eq_of_fixed_lines ρ A
    (fun i => (hd i).2.2.1) (fun i => (hd i).2.2.2)).trans hs
  exact ⟨hs, hc, h.cubicRatio_eq_of_fixedCodim_three ρ hc⟩

/-- Application to the literal local group `PA`: its original core and actor
are viewed inside their join, on the given reduced representation. -/
theorem local_generated_three_plane_splitting (P A : Subgroup G)
    (σ : Representation (ZMod 2) (P ⊔ A : Subgroup G) V) {s : ℕ}
    (h : Reduced σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) s)
    (hlow : 1 < cubicRatio σ)
    (hsmall : SmallInvariantSupports σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A))) :
    ∃ d : SupportFactors σ (P.subgroupOf (P ⊔ A)) s,
      s = 3 ∧ d.Alternatives (A.subgroupOf (P ⊔ A)) ∧
      fixedCodim σ (A.subgroupOf (P ⊔ A)) = 3 ∧ cubicRatio σ = 3 / 2 := by
  obtain ⟨d, hs, hd⟩ := h.three_plane_splitting σ hlow hsmall
  have hc := (d.fixedCodim_eq_of_fixed_lines σ (A.subgroupOf (P ⊔ A))
    (fun i => (hd i).2.2.1) (fun i => (hd i).2.2.2)).trans hs
  exact ⟨d, hs, Or.inr ⟨hs, fun i => ⟨(hd i).1, (hd i).2.1⟩⟩,
    hc, h.cubicRatio_eq_of_fixedCodim_three σ hc⟩

end CFSG.Quasithin.ChapterD.FittingConfigurations
