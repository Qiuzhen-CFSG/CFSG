module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FourResiduals

/-!
# Assembly of the original L₃(2) Sylow and fusion branches

Both escaping-normalizer alternatives now have explicit mathematical
contracts. In the fixed-L₁ case the two-member maximal elementary family
contradicts the normalizer index three. In the moving-L₁ case the actual
four-residual action gives a normal subgroup and the same contradiction
by uniqueness. The remaining normalizer-contained case promotes the local
Sylow subgroup of M∩C_G(v) to a Sylow subgroup of C_G(v), and orbit separation
then proves weak closure of the fixed involution in V.

This is conditional source assembly. LocalCalculations, FixedResidualCalculation
and MovingResidualCalculation must be constructed from the source before
asserting the unconditional 12.4.7 input.

Source: Aschbacher–Smith, 12.4.5–7, printed pp.813–814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u

/-- The original local module calculations of 12.4.5 and the beginning of
12.4.6. Their source construction is independent of the two escape cases. -/
def LocalCalculations : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    Nonempty (LocalGeometry D)

/-- The C.1.34 block, Frattini and B.2.21 calculations in the fixed-L₁
branch must supply the actual maximum elementary family of R₁. -/
def FixedResidualCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ d : LocalGeometry D,
    ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G) →
    normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G) →
    ∃ A : Subgroup G, V ∈ elementaryAbelianMaxSubgroups d.R ∧
      elementaryAbelianMaxSubgroups d.R ⊆ {V, A}

/-- The actual X/O₂(X)≃E₉ and C.1.10 calculation in the moving-L₁
branch must construct the four residuals and their relative overgroup. -/
def MovingResidualCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ d : LocalGeometry D,
    ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G) →
    ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G) →
    Nonempty (FourResidualGeometry d)

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The original R₁=C_T(E) is Sylow in C_G(v) once the two independent
escaping-normalizer calculations have been supplied. -/
theorem sylow_centralizer_of_escape_calculations
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (fixed : FixedResidualCalculation.{u}) (moving : MovingResidualCalculation.{u}) :
    Chapter1.IsSylowIn 2 d.R (centralizer ({d.v} : Set G)) := by
  apply sylow_centralizer_of_normalizer_le d.v d.local_sylow
  by_contra hescape
  by_cases hline : normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)
  · obtain ⟨A, hV, hpair⟩ := fixed G T L V h D hmodel hne d hescape hline
    obtain ⟨_, _, _, _, hi⟩ := d.escape_geometry h structural marked hmodel hne hescape
    obtain ⟨_, z, _, _, _, hM, _, _⟩ := exists_slThree_fixed_involution_setup
      h D structural marked uniquenessEarlier_knownSimple hmodel hne
    exact not_index_three_of_maxFamily_pair d.R V A (normalizer (L : Set G))
      hM hV hpair hi
  · obtain ⟨f⟩ := moving G T L V h D hmodel hne d hescape hline
    exact d.false_of_moving_lineResidual h structural marked hmodel hne hescape hline f

/-- The literal 12.4.6 witness, including its index two in the original T. -/
theorem sylow_witness_of_calculations
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (moving : MovingResidualCalculation.{u}) :
    ∃ (E : Subgroup G) (v : G), E ≤ V ∧ Nat.card E = 4 ∧ v ∈ E ∧
      v ∉ fixedSubgroup L V ∧
      ((T : Subgroup G) ⊓ centralizer (E : Set G)).relIndex T = 2 ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (E : Set G))
        (centralizer ({v} : Set G)) := by
  obtain ⟨d⟩ := localFacts G T L V h D hmodel hne
  exact ⟨d.E, d.v, d.le_module, d.card_plane, d.mem_plane, d.nonfixed, d.index,
    sylow_centralizer_of_escape_calculations h D structural marked hmodel hne d fixed moving⟩

/-- Source 12.4.7, with the 12.4.6 Sylow premise discharged by the local
and two escaping-normalizer calculations. Weak closure concerns V only. -/
theorem fusion_of_calculations
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (moving : MovingResidualCalculation.{u}) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      centralizer ({z} : Set G) ≤ normalizer (V : Set G) ∧
      (∀ g : G, MulAut.conj g z ∈ V → MulAut.conj g z = z) ∧
      ∀ x ∈ V, ∀ y ∈ V, IsConj x y → ∃ l ∈ L, MulAut.conj l x = y := by
  obtain ⟨E, v, hEV, _, hvE, hv, hi, hR⟩ :=
    sylow_witness_of_calculations h D structural marked hmodel hne localFacts fixed moving
  exact source_slThree_fusion h D structural marked uniquenessEarlier_knownSimple
    hmodel hne v (hEV hvE) hv ((T : Subgroup G) ⊓ centralizer (E : Set G))
    inf_le_left hi hR

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
