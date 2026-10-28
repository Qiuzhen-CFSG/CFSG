module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.PointAction
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Core
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.RelativeSylowNormalizer
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ModelConstruction.Construction

/-!
# The original common core and the nonsingular pushing-up setup

The action of L_w C_T(w) has two-core-free image. Its two-core lies in
C_T(w), so C_T(W)=Q identifies it with the original Q=O₂(LT). Applying
A.4.2(7) inside C_G(w) proves that Q is radical there and Sylow in its
normal closure under C_M(w). This constructs the genuine C.2.3 setup.
Radicality also puts O₂(C_G(w)) in Q, hence in C_G(W).

If L_w is normal in C_G(w), a normalizer of C_T(w) normalizes the join
L_w C_T(w), hence Q. The established normalizer control then promotes
C_T(w) to an ambient Sylow. The final application constructs the compatible
model and corrected L-conjugate for every original nonsingular point.

Ordinary-component exclusion and the remaining normal and parabolic arguments
of 12.1.1 are still required by qt-d-double-natural-centralizers.
Source: Aschbacher--Smith, 12.1.1, printed pp.788--789, using A.4.2(7), p.57.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The point-residual join has the original core Q = O₂(LT), using only the Sylow in C_M(w). -/
theorem doubleNatural_adapted_pointJoin_twoCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      (B.pointResidual w ⊔ B.pointSylow w).pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := B.pointResidual w ⊔ B.pointSylow w
  have hPM : B.pointSylow w ≤ B.localPointCentralizer w :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hJM : J ≤ B.localPointCentralizer w := sup_le
    (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)) hPM
  have hJLT : J ≤ L ⊔ (T : Subgroup G) := sup_le
    ((B.pointResidual_le w).trans (inf_le_left.trans le_sup_left))
    (inf_le_left.trans le_sup_right)
  have hQT : Q ≤ (T : Subgroup G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [← D.doubledOrbit_sylow_centralizer h]
    exact inf_le_left
  have hQJ : Q ≤ J := (le_inf hQT (D.doubleNatural_core_le_pointCentralizer h B w)).trans le_sup_right
  have hJQ : J ≤ normalizer (Q : Set G) := hJLT.trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  apply le_antisymm _ (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) hQJ hJQ)
  obtain ⟨P,hP⟩ := hw.local_sylow.restrict (show B.pointSylow w ≤ J from le_sup_right) hJM
  have hcoreT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    ((pCoreIn_le_sylow J P).trans_eq hP).trans inf_le_left
  let q := (S.localPointAction w).comp (inclusion hJM)
  have hq : Function.Surjective q := S.adapted_pointJoin_action_surjective w hw hPM
  have hm : (pCore 2 J).map q ≤ pCore 2 (S.setup.stabilizer (Additive.ofMul w)) :=
    le_sSup ⟨(inferInstance : (pCore 2 J).Normal).map q hq, pCore_isPGroup.map q⟩
  rw [S.nonsingular_stabilizer_twoCore w hw.nonsingular] at hm
  rw [← D.doubledOrbit_sylow_centralizer h]
  refine le_inf hcoreT ?_
  rintro x ⟨j,hj,rfl⟩
  have he : q j = 1 := mem_bot.mp (hm (mem_map_of_mem q hj))
  have he' : B.actionProjection (inclusion (hJM.trans inf_le_left) j) = 1 :=
    congrArg Subtype.val he
  have hk := (QuotientGroup.eq_one_iff (inclusion (hJM.trans inf_le_left) j)).mp he'
  rw [normalizerAction_ker] at hk
  exact hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem point_normalClosure_transport {H M R : Subgroup G} (hMH : M ≤ H) :
    ((normalClosure ((R.subgroupOf H).subgroupOf (M.subgroupOf H) : Set (M.subgroupOf H))).map
      (M.subgroupOf H).subtype).map H.subtype =
        (normalClosure (R.subgroupOf M : Set M)).map M.subtype := by
  let e := subgroupOfEquivOfLe hMH
  have he : ((R.subgroupOf H).subgroupOf (M.subgroupOf H)).map e.toMonoidHom =
      R.subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  have hn := map_normalClosure
    ((R.subgroupOf H).subgroupOf (M.subgroupOf H) : Set (M.subgroupOf H))
    e.toMonoidHom e.surjective
  rw [← coe_map,he] at hn
  rw [← hn,map_map,map_map]
  rfl

/-- A.4.2(7) discharges every C.2.3 premise for the literal nonsingular point centralizer. -/
theorem doubleNatural_adapted_pushingUpSetup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple (B.pointCentralizer w)
        ((L ⊔ (T : Subgroup G)).pCoreIn 2) (B.localPointCentralizer w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let H := B.pointCentralizer w
  let M := B.localPointCentralizer w
  let X := (B.pointResidual w).subgroupOf H
  let M₀ := M.subgroupOf H
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := Q.subgroupOf H
  have hMH : M ≤ H := inf_le_right
  have hXM : B.pointResidual w ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  have hXH := hXM.trans hMH
  have hPH : B.pointSylow w ≤ H := inf_le_right
  have hQH : Q ≤ H := D.doubleNatural_core_le_pointCentralizer h B w
  have hne : Q ≠ ⊥ := h.maximal_faithful.1.1.2.2
  have hneR : R ≠ ⊥ := by
    intro he
    have hm := congrArg (map H.subtype) he
    exact hne (by simpa only [R,map_subgroupOf_eq_of_le hQH,Subgroup.map_bot] using hm)
  have hs : IsSylowIn 2 ((B.pointSylow w).subgroupOf H) M₀ := by
    apply (IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    simpa only [M₀,map_subgroupOf_eq_of_le hPH,map_subgroupOf_eq_of_le hMH] using hw.local_sylow
  obtain ⟨P,hP⟩ := hs
  have hR : (X ⊔ (P : Subgroup M₀).map M₀.subtype).pCoreIn 2 = R := by
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      Subgroup.map_sup,hP,map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hPH,
      map_subgroupOf_eq_of_le hQH]
    exact D.doubleNatural_adapted_pointJoin_twoCore h B S w hw
  have hn : M₀ ≤ normalizer (X : Set H) := by
    rw [← subgroupOf_normalizer_eq hXH]
    exact comap_mono (B.localPointCentralizer_normalizes_residual w)
  have hctl : R.characteristicNormalizerClosure ≤ M₀ :=
    D.doubleNatural_point_characteristicNormalizerClosure h B w
  have hN : normalizer ((X ⊔ (P : Subgroup M₀).map M₀.subtype).pCoreIn 2 : Set H) ≤ M₀ := by
    rw [hR]
    exact (normalizer_le_characteristicNormalizerClosure_self R hneR).trans hctl
  have hp : IsPPerfect 2 X := (B.pointResidual_isPPerfect w).of_surjective
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  have hc := normal_sylow_core_conclusions X M₀ (comap_mono hXM) hn hp P hN
  dsimp only at hc
  rw [hR] at hc
  refine ⟨h.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer
    (D.doubleNatural_point_orderOf_two h B w hw.nonsingular)),hQH,hMH,
    ⟨hneR,hc.2.2.2.2.2.1.symm⟩,hctl,?_⟩
  have hm := (IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hc.2.2.2.2.2.2
  rw [map_subgroupOf_eq_of_le hQH,point_normalClosure_transport hMH] at hm
  exact hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The ambient point-centralizer two-core lies in the original Q by radicality. -/
theorem doubleNatural_adapted_pointCore_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      (B.pointCentralizer w).pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  have hs := D.doubleNatural_adapted_pushingUpSetup h B S w hw
  have hc := pCore_le_of_pCore_normalizer_le _ hs.radical.isPGroup hs.radical.2.le
  have hm := map_mono (f := (B.pointCentralizer w).subtype) hc
  rwa [map_subgroupOf_eq_of_le hs.radical_le] at hm

/-- The full ambient point-centralizer two-core centralizes the original doubled orbit. -/
theorem doubleNatural_adapted_pointCore_centralizes_orbit
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      (B.pointCentralizer w).pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  have hc := D.doubleNatural_adapted_pointCore_le h B S w hw
  rw [← D.doubledOrbit_sylow_centralizer h] at hc
  exact hc.trans inf_le_right

/-- In the normal-residual branch, the original C_T(w) is Sylow in C_G(w). -/
theorem doubleNatural_adapted_ambientSylow_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hn
  have hRH := (B.pointResidual_le w).trans inf_le_right
  have hHn : B.pointCentralizer w ≤ normalizer (B.pointResidual w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRH).mp hn
  apply exists_sylow_eq_of_relative_normalizer_le hw.local_sylow inf_le_right
  have hN : B.pointCentralizer w ⊓ normalizer (B.pointSylow w : Set G) ≤
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
    rw [← D.doubleNatural_adapted_pointJoin_twoCore h B S w hw]
    apply le_trans _ (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    exact (le_inf (inf_le_left.trans hHn) inf_le_right).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQM : normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
    (normalizer_le_characteristicNormalizerClosure_self _ h.maximal_faithful.1.1.2.2).trans
      (D.doubleNatural_core_characteristicNormalizerClosure h)
  exact le_inf (hN.trans hQM) inf_le_left

/-- Every nonsingular point has an L-conjugate satisfying the actual C.2.3 setup; the compatible model is discharged. -/
theorem doubleNatural_nonsingular_pushingUpSetup_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G), B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧
        B.quadratic (Additive.ofMul w') = 1 ∧
        IsSylowIn 2 (B.pointSylow w') (B.localPointCentralizer w') ∧
        (B.pointResidual w' ⊔ B.pointSylow w').pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple (B.pointCentralizer w')
          ((L ⊔ (T : Subgroup G)).pCoreIn 2) (B.localPointCentralizer w') := by
  let := D.doubledOrbit_elementary h
  intro w hw
  obtain ⟨S⟩ := B.nonempty_sourceModel
  obtain ⟨l,w',he,hw'⟩ := D.doubleNatural_adaptedPoint h B S w hw
  exact ⟨l,w',he,hw'.nonsingular,hw'.local_sylow,
    D.doubleNatural_adapted_pointJoin_twoCore h B S w' hw',
    D.doubleNatural_adapted_pushingUpSetup h B S w' hw'⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
