module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import Theory.Representation.Triality.PrimitiveDegree
public import Theory.GroupTheory.AutomorphismRankCyclicOuter
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.SpecificGroups.Triality.OuterOddSubgroups

/-!
# Triality actor bounds from the actual G.9 component

The source component is quasisimple. Transport through its specified model
isomorphism, together with the proved carrier centerlessness, supplies the
simplicity and perfectness premises of automorphism coverage. They do not
need independent model certification for this consumer.

Coverage by inner and coefficient automorphisms makes the outer group cyclic.
An intrinsic two-rank bound of 5*n then gives actor rank at most 5*n+1.
The same faithful representation has degree at least 12*n and at most
10*n+4, which excludes n>=3. Coverage and the intrinsic rank bound remain
explicit genuine inputs. The cases n=1,2 and the stronger general automorphism
rank bound are not proved here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.9, p.356;
GLS3 §2.5 for the separately owned automorphism-coverage theorem.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09
open Triality.Standard
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : CFSG.Quasithin.GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

theorem inherited_model_hypotheses
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} {hn : 0 < n}
    (e : L ≃* BinaryCarrier n hn) :
    IsQuasisimple (BinaryCarrier n hn) ∧
      Group.IsPerfect (BinaryCarrier n hn) ∧
      IsSimpleGroup (BinaryCarrier n hn) := by
  let : IsQuasisimple L := h.component.2
  let : IsQuasisimple (BinaryCarrier n hn) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (BinaryCarrier n hn ⧸ center (BinaryCarrier n hn)) :=
    IsQuasisimple.simple
  let eQ : (BinaryCarrier n hn ⧸ center (BinaryCarrier n hn)) ≃*
      BinaryCarrier n hn :=
    (QuotientGroup.quotientMulEquivOfEq (Triality.Standard.binaryCarrier_center_eq_bot n hn)).trans
      QuotientGroup.quotientBot
  exact ⟨inferInstance, inferInstance, eQ.isSimpleGroup_congr.mp inferInstance⟩

theorem actor_rank_le_of_inherited_model_estimate
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} {hn : 0 < n}
    (e : L ≃* BinaryCarrier n hn) {r : ℕ}
    (hestimate : IsSimpleGroup (BinaryCarrier n hn) →
      Group.IsPerfect (BinaryCarrier n hn) →
      primeRank 2 (MulAut (BinaryCarrier n hn)) ≤ r) : m ≤ r := by
  obtain ⟨_, hperfect, hsimple⟩ := inherited_model_hypotheses h e
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hAL : A ≤ normalizer (L : Set G) := by
    rw [normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top
  have hr := h.toSetup.rank_le_automorphisms hAL
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  exact hr.trans (hestimate hsimple hperfect)

theorem inherited_coefficient_coverage
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} {hn : 0 < n}
    (e : L ≃* BinaryCarrier n hn)
    (hcoverage : IsSimpleGroup (BinaryCarrier n hn) →
      Group.IsPerfect (BinaryCarrier n hn) →
      ∀ a : MulAut (BinaryCarrier n hn), ∃ g : BinaryCarrier n hn,
        ∃ f : OuterOdd.CoefficientAut (binaryParameters n hn),
          a = MulAut.conj g * OuterOdd.coefficientAction (binaryParameters n hn) f) :
    ∀ a : MulAut (BinaryCarrier n hn), ∃ g : BinaryCarrier n hn,
      ∃ f : OuterOdd.CoefficientAut (binaryParameters n hn),
        a = MulAut.conj g * OuterOdd.coefficientAction (binaryParameters n hn) f := by
  obtain ⟨_, hperfect, hsimple⟩ := inherited_model_hypotheses h e
  exact hcoverage hsimple hperfect
theorem not_triality_of_coarse_rank_and_coverage
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* BinaryCarrier n (by omega))
    (hrank : primeRank 2 (BinaryCarrier n (by omega)) ≤ 5 * n)
    (hcoverage : IsSimpleGroup (BinaryCarrier n (by omega)) →
      Group.IsPerfect (BinaryCarrier n (by omega)) →
      ∀ a : MulAut (BinaryCarrier n (by omega)),
        ∃ g : BinaryCarrier n (by omega),
        ∃ f : OuterOdd.CoefficientAut (binaryParameters n (by omega)),
          a = MulAut.conj g *
            OuterOdd.coefficientAction (binaryParameters n (by omega)) f) : False := by
  have hn0 : 0 < n := by omega
  have hc := inherited_coefficient_coverage h e hcoverage
  let : IsCyclic (MulAut.Outer (BinaryCarrier n hn0)) :=
    OuterOdd.outer_isCyclic_of_inner_coefficient (binaryParameters n hn0) hc
  have haut := Theory.GroupTheory.automorphism_twoRank_le_of_cyclic_outer (Triality.Standard.binaryCarrier_center_eq_bot n hn0)
  have hm : m ≤ 5 * n + 1 := actor_rank_le_of_inherited_model_estimate h e
    (fun _ _ => haut.trans (Nat.add_le_add_right hrank 1))
  have hd := Triality.PrimitiveDegree.finrank_ge n hn0
    ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
  have hu := h.degree_le
  omega

/-- Apply the coarse route to the source's actual triality-model witness. -/
theorem not_triality_of_coarse_model_estimates
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 3 ≤ n)
    (model : Triality.Standard.IsTrialityGroupAt (2 ^ n) L)
    (hrank : primeRank 2 (BinaryCarrier n (by omega)) ≤ 5 * n)
    (hcoverage : IsSimpleGroup (BinaryCarrier n (by omega)) →
      Group.IsPerfect (BinaryCarrier n (by omega)) →
      ∀ a : MulAut (BinaryCarrier n (by omega)),
        ∃ g : BinaryCarrier n (by omega),
        ∃ f : OuterOdd.CoefficientAut (binaryParameters n (by omega)),
          a = MulAut.conj g *
            OuterOdd.coefficientAction (binaryParameters n (by omega)) f) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L n (by omega)).mp model
  exact not_triality_of_coarse_rank_and_coverage h hn e hrank hcoverage

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
