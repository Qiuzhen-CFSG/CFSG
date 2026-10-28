module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.NativeNonFF
public import Theory.SpecificGroups.Janko4.Model.SmallMathieuThompson
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.MathieuTwentyTwoRadicals

/-!
# Hall faithfulness for the original M₂₂ orbit

The full native residual maps onto M₂₂ and moves the whole radical exactly
on the original module. The native involution centralizers force this radical
to be elementary. Its order is at most 2048 and the original module has index
at most two, so it is the module centralizer inside the residual normalizer.
The original non-FF action then makes it the Thompson subgroup of a full J₄
Sylow, whose prime-23 normalizer contradicts the original module order 1024.
This excludes every original M₂₂ Hall-kernel witness with all central covers
and literal inclusion and quotient maps retained.

Source: Aschbacher–Smith 4.2.13 and 4.4.14, printed pp.611–612,624–625.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original M22 native radical is elementary of order at most 2048,
with the actual original module of index at most two. -/
theorem sourceOrbit_pushingUp_m22_radical_elementary
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let j := H.subtype.comp K.subtype
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let U := ((J.pCoreIn 2).comap j).map q
    let E := (V.comap j).map q
    IsElementaryAbelian 2 U ∧ Nat.card U ≤ 2048 ∧ E.relIndex U ≤ 2 := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Fk := F.comap j
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := Fk.map q
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK := hw.2.2.2.2.2.2.1.ordinary_component_contains_original K hK
  let b : Fk ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFH)
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : Group.IsPerfect Fk := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective Fk)
  have hn := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hn
  have hEU : E ≤ U := hn.2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := hn.2.2.2.2.2.2.1
  have hlower : 1024 ≤ Nat.card E := by
    rw [hn.2.2.2.2.2.2.2.1]
    let := D.elementary
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) V]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (D.sourceOrbit_mathieu_twoRank_ge_ten hV (.inr (.inl hm)))
  let a : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L) := hn.2.2.2.2.2.2.2.2.some
  let z := ((centerQuotientCongr a).trans (D.orbitCentralQuotientEquiv h)).trans hm.some
  let f := z.toMonoidHom.comp
    ((QuotientGroup.mk' (center (B ⧸ pCore 2 B))).comp (QuotientGroup.mk' (pCore 2 B)))
  let hElem : IsElementaryAbelian 2 U := Janko4.InvolutionCentralizers.m22_radical_elementary
    B U E f (z.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)))
    hn.2.1.isPGroup hn.2.2.2.1 hEU (by omega)
    (D.sourceOrbit_pushingUp_small_radical_centralizes h hV hfix (.inr hm) hw K hK e)
    (D.sourceOrbit_pushingUp_small_radical_displacement h hV hfix (.inr hm) hw K hK e).le
  let := hElem
  have hupper : Nat.card U ≤ 2048 :=
    (primeRank_le_iff_elementary_card_le Janko4.Model).mp
      Janko4.TwoRank.model_twoRank_le_eleven U hElem
  have hcount := (E.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv] at hcount
  change Nat.card E * E.relIndex U = Nat.card U at hcount
  exact ⟨hElem,hupper,by nlinarith⟩

/-- The original M22 pushing-up configuration contradicts non-FF, through
its elementary native radical and the prime-23 Thompson normalizer. -/
theorem sourceOrbit_pushingUp_m22_false
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) : False := by
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U := ((J.pCoreIn 2).comap j).map q
  let E := (V.comap j).map q
  let B := (F.comap j).map q
  let C := normalizer (B : Set Janko4.Model)
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hdim := ((D.sourceOrbit_pushingUp_small_module h hmany hV hnon hw K hK e).2 hm).finrank
  have hVcard : Nat.card V = 1024 := by
    have hc : Nat.card D.orbitSpace = Nat.card V :=
      (Nat.card_congr D.sourceOrbitCoordinates.toEquiv).trans
        (congrArg (fun X : Subgroup G => Nat.card X) hV.symm)
    rw [←hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    decide
  have hnat := D.sourceOrbit_pushingUp_native_radical hfix hw K hK e
  dsimp only at hnat
  have hsmall := D.sourceOrbit_pushingUp_m22_radical_elementary h.toHypothesis1221 hV hfix hm hw K hK e
  let : IsElementaryAbelian 2 U := hsmall.1
  let : IsElementaryAbelian 2 E := hnat.2.2.2.2.2.2.1
  have hN := sourceOrbit_pushingUp_native_normalizer hw K hK e
  have hc : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (MulEquiv.subgroupCongr hN.1)).mpr hN.2
  have hn := Subgroup.abelian_radical_in_constrained U C hnat.2.1
    (U.le_normalizer.trans hnat.2.2.1) hnat.2.2.1 hc
  have hcore := D.sourceOrbit_pushingUp_native_normalizer_core h.toHypothesis1221 hV hfix (.inr hm) hw K hK e
  have hcent : C ⊓ centralizer (E : Set Janko4.Model) = U := by
    refine le_antisymm (Subgroup.centralizer_le_core_of_fixed_index_le_two
      C U E hn.1 hn.2.2.le hnat.2.2.2.2.2.1 hsmall.2.2 hcore.2.2.2) ?_
    exact le_inf (U.le_normalizer.trans hnat.2.2.1)
      (D.sourceOrbit_pushingUp_small_radical_centralizes h.toHypothesis1221 hV hfix (.inr hm) hw K hK e)
  obtain ⟨P,hPC,hth⟩ := native_sylow_of_elementary_core_nonFF U E B
    hnat.2.2.2.2.2.1 hn.1 hn.2.1 hcent hcore.2.2.2
    (D.sourceOrbit_pushingUp_native_nonFF h.toHypothesis1221 hV hfix (.inr hm) hnon hw K hK e)
  apply Janko4.not_small_module_of_thompson_radical P U E hth hsmall.2.1 hnat.2.1.isPGroup
    (hnat.2.2.2.2.2.2.2.1.trans hVcard)
  · exact hn.2.1.le.trans hcore.2.2.2
  · exact (congrArg (fun X : Subgroup Janko4.Model => X ⊓ centralizer (E : Set Janko4.Model)) hn.2.1).trans hcent

open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open scoped Pointwise
/-- Every literal original odd Hall subgroup is faithful in the M22 case. -/
theorem sourceOrbit_m22_hall_faithful
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H₀)
    (B₀ : Subgroup H₀) (hBN : B₀ ≤ (normalizer (L : Set G)).subgroupOf H₀)
    (hHall : IsHallSubgroup oddPrimes
      (B₀.subgroupOf ((normalizer (L : Set G)).subgroupOf H₀))) :
    B₀.map H₀.subtype ⊓ sectionCentralizer L = ⊥ := by
  by_contra hker
  have hsource := D.sourceOrbit_mathieu_hall_pushingUp_only
    h hmany hV (.inr (.inl hm)) hnon hH hlarge B₀ hBN hHall hker
  obtain ⟨p,A,hA⟩ := hsource
  obtain ⟨hp,ho,hne,he,hAH,hAL,hAV,hAT,hN,hX,hcontrol,hsmall,hfact,hgap⟩ := hA
  obtain ⟨J,H,W,hw,K,hK,hn,hout,hFK,e,hrest⟩ := hgap
  exact D.sourceOrbit_pushingUp_m22_false h hmany hV hm hnon hw K hK e
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
