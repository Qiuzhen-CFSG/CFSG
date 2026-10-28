module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Odd
public import Theory.GroupTheory.GeneralizedFitting.InnerMovingActor
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# Ordinary components in an adapted nonsingular centralizer

The original fixed line lies in the point residual. A component cannot
centralize this line, since C_G(w,z) has characteristic two. The odd-rank
bound makes every two-perfect actor normalize each component; the component
commutator dichotomy therefore gives [K,O²(C_L(w))]=K.

Together with the proved trivial odd core, failure of characteristic two
now produces an actual ordinary component with these source controls.
Excluding that component by the source classification is still required.
Source: Aschbacher--Smith, 12.1.1, printed p.788.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The relative point centralizer C_M(w) has characteristic two. -/
theorem doubleNatural_localPoint_characteristic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (w : componentOrbit V (T : Subgroup G)) :
    B.localPointCentralizer w ∈ Chapter1.He G := by
  let := D.doubledOrbit_elementary h
  let M := normalizer (L : Set G)
  have hM : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (h.simpleQTKE.evenCharacteristic T M (D.doubledNormalizer_unique h).1
      D.sylow_normalizes_component)
  have hp : IsPGroup 2 (zpowers (w : G)) :=
    (IsElementaryAbelian.isPGroup 2 (componentOrbit V (T : Subgroup G))).to_le
      (zpowers_le.mpr w.property)
  have hwM : zpowers (w : G) ≤ M := zpowers_le.mpr
    (D.sylow_normalizes_component ((D.doubledOrbit_E322 h).le_sylow w.property))
  have hc := pCoreIn_selfCentralizing_centralizer hM hp hwM
  change (B.localPointCentralizer w) ⊓
    centralizer ((B.localPointCentralizer w).pCoreIn 2 : Set G) ≤ _
  simpa only [DoubledBranch.localPointCentralizer,DoubledBranch.pointCentralizer,
    zpowers_eq_closure,centralizer_closure] using hc

/-- An ordinary component of C_G(w) cannot lie in the original normalizer. -/
theorem doubleNatural_point_component_not_le_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (w : componentOrbit V (T : Subgroup G))
    (K : Subgroup G) (hK : IsComponentIn K (B.pointCentralizer w)) :
    ¬ K ≤ normalizer (L : Set G) := by
  intro hKM
  exact not_isComponent_of_twoCore
    (Chapter1.mem_He_iff.mp (D.doubleNatural_localPoint_characteristic h B w)) _
    (hK.restrict (le_inf hKM hK.1) inf_le_right).2

/-- The original fixed line lies in O²(C_L(w)). -/
theorem doubleNatural_adapted_fixedLine_le_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.AdaptedPoint S w → B.fixedLine ≤ B.pointResidual w := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  apply (S.adapted_fixedLine_le_moving w hw).trans
  apply le_normalizer_iff_commutator_le_right.mp
  apply le_trans _ (B.localPointCentralizer_normalizes_residual w)
  exact le_inf ((D.doubledOrbit_E322 h).le_sylow.trans D.sylow_normalizes_component)
    (B.orbit_le_pointCentralizer w)

/-- Every ordinary component moves the original T-fixed line. -/
theorem doubleNatural_adapted_component_not_centralizes_fixedLine
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.AdaptedPoint S w → ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ K ≤ centralizer (B.fixedLine : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK hKC
  have hline : B.fixedLine ≠ ⊥ := by
    intro he
    apply hw.residual_moves
    intro x hx y hy
    have hy1 : y = 1 := mem_bot.mp (he ▸ hy)
    simp [hy1]
  obtain ⟨z,hz,hz1⟩ := B.fixedLine.bot_or_exists_ne_one.resolve_left hline
  have hKz : K ≤ centralizer ({z} : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hKC hk z hz).symm
  have hc := D.doubleNatural_point_fixedPoint_characteristic h B w z hz hz1
  exact not_isComponent_of_twoCore (Chapter1.mem_He_iff.mp hc) _
    (hK.restrict (le_inf hK.1 hKz) inf_le_left).2

/-- The actual residual normalizes and generates each component by commutators. -/
theorem doubleNatural_adapted_component_residual_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.AdaptedPoint S w → ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        B.pointResidual w ≤ normalizer (K : Set G) ∧ ⁅K,B.pointResidual w⁆ = K := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  let H := B.pointCentralizer w
  let R := B.pointResidual w
  have hRH : R ≤ H := (B.pointResidual_le w).trans inf_le_right
  have hKH : K ≤ H := hK.1
  have hsqt : IsStronglyQuasithin H :=
    (h.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer
      (D.doubleNatural_point_orderOf_two h B w hw.nonsingular))).stronglyQuasithin
  have hp : IsPPerfect 2 (R.subgroupOf H) := (B.pointResidual_isPPerfect w).of_surjective
    (subgroupOfEquivOfLe hRH).symm.toMonoidHom (subgroupOfEquivOfLe hRH).symm.surjective
  have hn : R.subgroupOf H ≤ normalizer (K.subgroupOf H : Set H) := by
    rcases hK.2.normal_or_index_two_of_odd_rank_le_two hsqt with hnormal | hi
    · let := hnormal
      rw [normalizer_eq_top]
      exact le_top
    · let N := normalizer (K.subgroupOf H : Set H)
      let : N.Normal := N.normal_of_index_eq_two hi
      have hq : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card (n := 1) (by
        change N.index = 2 ^ 1
        simpa only [pow_one] using hi)
      exact (le_pResidual_of_isPPerfect _ hp).trans (sInf_le ⟨inferInstance,hq⟩)
  have hn' : R ≤ normalizer (K : Set G) := by
    have he : normalizer (K.subgroupOf H : Set H) =
        (normalizer (K : Set G)).subgroupOf H := (subgroupOf_normalizer_eq hK.1).symm
    rw [he] at hn
    intro r hr
    exact hn (show (⟨r,hRH hr⟩ : H) ∈ R.subgroupOf H from hr)
  refine ⟨hn',?_⟩
  have hne : ⁅K,R⁆ ≠ ⊥ := by
    intro he
    exact D.doubleNatural_adapted_component_not_centralizes_fixedLine h B S w hw K hK
      ((commutator_eq_bot_iff_le_centralizer.mp he).trans
        (centralizer_le (D.doubleNatural_adapted_fixedLine_le_residual h B S w hw)))
  have he : ⁅K.subgroupOf H,R.subgroupOf H⁆ = K.subgroupOf H := by
    rcases hK.2.commutator_dichotomy (R.subgroupOf H) with hc | hc
    · change ⁅K.subgroupOf H,R.subgroupOf H⁆ = ⊥ at hc
      apply False.elim
      apply hne
      simpa only [map_commutator,map_subgroupOf_eq_of_le hKH,
        map_subgroupOf_eq_of_le hRH,Subgroup.map_bot] using congrArg (map H.subtype) hc
    · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
        ((le_iSup_conjugates (K.subgroupOf H) (R.subgroupOf H)).trans hc.symm.le)
  simpa only [map_commutator,map_subgroupOf_eq_of_le hKH,
    map_subgroupOf_eq_of_le hRH] using congrArg (map H.subtype) he

/-- Only an ordinary component can obstruct characteristic two; all displayed action controls are proved. -/
theorem doubleNatural_adapted_characteristic_or_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.AdaptedPoint S w →
        generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) ∨
        ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) ∧
          B.pointResidual w ≤ normalizer (K : Set G) ∧
          ⁅K,B.pointResidual w⁆ = K ∧ ¬ K ≤ centralizer (B.fixedLine : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  by_cases hc : generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)
  · exact Or.inl hc
  · obtain ⟨K,hK⟩ := exists_component_of_oddCore_eq_bot
      (D.doubleNatural_adapted_oddCore_eq_bot h B S w hw) hc
    let A := K.map (B.pointCentralizer w).subtype
    have hA : IsComponentIn A (B.pointCentralizer w) := by
      refine ⟨map_subtype_le _,?_⟩
      rwa [show A.subgroupOf (B.pointCentralizer w) = K from
        comap_map_eq_self_of_injective (B.pointCentralizer w).subtype_injective K]
    obtain ⟨hn,hcomm⟩ := D.doubleNatural_adapted_component_residual_action h B S w hw A hA
    exact Or.inr ⟨A,hA,hn,hcomm,
      D.doubleNatural_adapted_component_not_centralizes_fixedLine h B S w hw A hA⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
