module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.Components
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Residual
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The residual core and the old component's derived two-core

The actual point stabilizer in GL₄(2) is perfect. Its preimage P therefore
satisfies P = O²(P) O₂(L). Relative C-component subnormality identifies
[O₂(O²(P)),O²(P)] with [O₂(P),O²(P)]. Expanding the latter product gives

  [O₂(P),P] = [O₂(O²(P)),O²(P)] [O₂(L),O₂(L)].

Thus the remaining local calculation is the containment of the old
component's derived two-core in the residual commutator. The quotient
P/O₂(P) alone does not remove this term, and this module does not assert
that the containment has been proved from the earlier source hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24 and C.1.34, printed pp.1129–1130 and 136–137.
-/

public section

open scoped Pointwise
open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {L : Subgroup G}

private theorem finite_perfect_twoPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- Perfectness of the marked point stabilizer supplements the residual by
the old component core, which can be smaller than O₂(P). -/
theorem point_eq_residual_sup_componentCore (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    point h x = Stellmacher.twoResidualAmbient (point h x) ⊔ L.pCoreIn 2 := by
  let P := point h x
  let f := pointActor h x
  let _ : Finite (pointStabilizer x) := Finite.of_surjective f (pointActor_surjective h x)
  let _ := point_isPerfect (by decide : 4 ≤ 4) hx
  have hmap : (pResidual 2 P).map f = ⊤ := by
    rw [map_pResidual_of_surjective 2 f (pointActor_surjective h x)]
    exact (pResidual_eq_top_iff 2 _).mpr finite_perfect_twoPerfect
  have he := congrArg (comap f) hmap
  rw [comap_map_eq, comap_top] at he
  have hm := congrArg (map P.subtype) he
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hm
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  have hk : f.ker.map P.subtype = L.pCoreIn 2 := by
    rw [show f.ker = (L.pCoreIn 2).subgroupOf P from pointActor_ker h x,
      map_subgroupOf_eq_of_le (componentCore_le_point h x)]
  rw [hk] at hm
  exact hm.symm

/-- The external P-core commutator agrees with the intrinsic residual core.
This comparison uses the actual relative C-component, not only its quotient. -/
theorem residual_core_commutator_eq (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
      Stellmacher.twoResidualAmbient (point h x)⁆ =
    ⁅(point h x).pCoreIn 2, Stellmacher.twoResidualAmbient (point h x)⁆ := by
  let P := point h x
  let D := Stellmacher.twoResidualAmbient P
  have hDP : D ≤ P := map_subtype_le _
  let E := D.subgroupOf P
  have hc : E.IsCComponent := (point_residual_component h hx).1
  let _ := hc.perfect
  have hle := commutator_le_core_commutator_of_isSubnormal E (pCore 2 P)
    hc.subnormal finite_perfect_twoPerfect pCore_isPGroup
    (by rw [normalizer_eq_top]; exact le_top)
  have hm := map_mono (f := P.subtype) hle
  have he : E.map P.subtype = D := map_subgroupOf_eq_of_le hDP
  let e : E ≃* D := subgroupOfEquivOfLe hDP
  have hcore : (pCore 2 E).map (P.subtype.comp E.subtype) = D.pCoreIn 2 := by
    change (pCore 2 E).map (D.subtype.comp e.toMonoidHom) = _
    rw [← map_map, pCore_map_iso]
    rfl
  have htop : (⊤ : Subgroup E).map (P.subtype.comp E.subtype) = D := by
    rw [← map_map, ← MonoidHom.range_eq_map, range_subtype, he]
  rw [map_commutator, he, map_map, map_commutator, hcore, htop] at hm
  exact le_antisymm
    (commutator_mono (pCoreAmbient_mono_of_isSubnormalIn D P 2 hDP hc.subnormal) le_rfl) hm

omit [Finite G] in
private theorem commutator_join_bound (A B C P N : Subgroup G)
    (hBP : B ≤ P) (hCP : C ≤ P) (hPN : P ≤ normalizer N)
    (hB : ⁅A, B⁆ ≤ N) (hC : ⁅A, C⁆ ≤ N) : ⁅A, B ⊔ C⁆ ≤ N := by
  have he : B ⊔ C ≤ commutatorPreimage P A N :=
    sup_le (le_commutatorPreimage hBP (by rwa [commutator_comm]))
      (le_commutatorPreimage hCP (by rwa [commutator_comm]))
  rw [commutator_comm]
  exact (commutator_mono he le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hPN)

omit [Finite G] in
private theorem core_join_comparison (P D Q N : Subgroup G)
    (hD : D ≤ P) (hQ : Q ≤ P) (hNQ : N ≤ Q)
    (hn : P ≤ normalizer (N : Set G)) (hgen : D ⊔ N = P) :
    ⁅Q, P⁆ = ⁅Q, D⁆ ⊔ ⁅N, N⁆ := by
  let C := ⁅Q, D⁆ ⊔ ⁅N, N⁆
  have hPC : P ≤ normalizer C := by
    apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · rw [← hgen]
      exact sup_le (normalizer_commutator_ge_right _ _)
        (hNQ.trans (normalizer_commutator_ge_left _ _))
    · rw [← N.map_subtype_commutator]
      exact hn.trans (normalizer_le_normalizer_characteristic_image N (commutator N))
  have hfactor : Q ≤ (Q ⊓ D) ⊔ N := by
    intro q hq
    have hp : q ∈ (D : Set G) * (N : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right D N (hD.trans hn), hgen]
      exact hQ hq
    obtain ⟨a, ha, b, hb, he⟩ := hp
    have haq : a ∈ Q := by
      have hh := Q.mul_mem hq (Q.inv_mem (hNQ hb))
      rw [← he, mul_inv_cancel_right] at hh
      exact hh
    exact he ▸ mul_mem (mem_sup_left ⟨haq, ha⟩) (mem_sup_right hb)
  have hQN : ⁅Q, N⁆ ≤ C := by
    rw [commutator_comm]
    apply (commutator_mono le_rfl hfactor).trans
    apply commutator_join_bound N (Q ⊓ D) N P C
      (inf_le_right.trans hD) (hNQ.trans hQ) hPC
    · rw [commutator_comm]
      exact (commutator_mono inf_le_right hNQ).trans
        (by rw [commutator_comm]; exact le_sup_left)
    · exact le_sup_right
  apply le_antisymm
  · conv_lhs => rw [← hgen]
    exact commutator_join_bound Q D N P C hD (hNQ.trans hQ) hPC le_sup_left hQN
  · exact sup_le (commutator_mono le_rfl hD)
      (commutator_mono hNQ (hNQ.trans hQ))

/-- The exact residual comparison leaves only the derived subgroup of the
old O₂(L). Removing this term needs the additional local source argument. -/
theorem coreCommutator_eq_residualCore_sup_componentDerived (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    coreCommutator (point h x) =
      ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆ ⊔ ⁅L.pCoreIn 2, L.pCoreIn 2⁆ := by
  rw [residual_core_commutator_eq h hx]
  exact core_join_comparison (point h x) (Stellmacher.twoResidualAmbient (point h x))
    ((point h x).pCoreIn 2) (L.pCoreIn 2) (map_subtype_le _) (pCoreIn_le _ _)
    (componentCore_le_pointCore h x)
    ((point_le h x).trans (L.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))
    (point_eq_residual_sup_componentCore h hx).symm

/-- An exact reduction of the still-needed local equality, rather than an
assumption that the parabolic quotient determines its commutator core. -/
theorem residual_core_eq_iff_componentDerived_le (h : NaturalDual d L)
    {x : Space 4} (hx : x ≠ 0) :
    ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
      Stellmacher.twoResidualAmbient (point h x)⁆ = coreCommutator (point h x) ↔
    ⁅L.pCoreIn 2, L.pCoreIn 2⁆ ≤
      ⁅(Stellmacher.twoResidualAmbient (point h x)).pCoreIn 2,
        Stellmacher.twoResidualAmbient (point h x)⁆ := by
  rw [coreCommutator_eq_residualCore_sup_componentDerived h hx, eq_comm, sup_eq_left]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization
