module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.QuadraticBound
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.ThreeRadical
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourcePrime
public import Theory.GroupTheory.GeneralizedFitting.JointCoreDetection

/-!
# Excluding the nonquasisimple point quotient in the abelian branch

If the degree-four point quotient is not quasisimple, the original
component comparison gives its elementary seven-core of order 49. A.3.6
then makes its generalized Fitting subgroup that seven-core: the other
nilpotent alternative excludes seven by its prime congruence.

In the literal J = K₁T quotient by O₂(J), the image of K₁ is normal and
has two-group quotient. Its generalized Fitting subgroup therefore contains
the ambient generalized Fitting subgroup. The seven-core is consequently
self-centralizing. F.9.16 supplies a quadratic ratio at most two on U_J/V₁,
whereas D.2.13 says a minimal cubic actor can move only a three- or five-core.
Such an actor would centralize the self-centralizing seven-core, impossible
for a nontrivial two-group. This proves the exceptional-row exclusion in
12.9.5(2), after the preceding K₁T membership assertion. PointModels completes the quasisimple
model rows. Both source centralizer bounds remain to be proved.

Source: Aschbacher--Smith, 12.9.5, printed pp.860--861; A.3.6,
pp.43--45; D.2.13(1), pp.184--185. All quotient maps are the original maps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

private theorem seven_fitting_of_nonsimple_radical
    {X : Type*} [Group X] [Finite X]
    (h : Chapter1.Section02.A36Natural X ∨ Chapter1.Section02.A36Nilpotent X)
    (h7 : 7 ∣ Nat.card (fittingSubgroup X)) : generalizedFitting X = pCore 7 X := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  rcases h with ⟨hF,p,hp,hp3,ha⟩ | h
  · obtain ⟨he,hcard⟩ := Chapter1.RadicalStructure.natural_elementary ha
    have hd : 7 ∣ p ^ 2 := by simpa only [←hF,hcard] using h7
    have hp7 : p = 7 := ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp
      ((by decide : Nat.Prime 7).dvd_of_dvd_pow hd)).symm
    subst p
    exact hF.trans (Chapter1.RadicalStructure.fitting_eq_core (by
      rw [←hF]
      exact IsPGroup.of_card hcard))
  · have hh := (h.2.2.2 7 (by decide) (h.1.symm ▸ h7)).1
    norm_num at hh

private theorem no_quadratic_bound_of_seven_fitting_extension
    {X E : Type*} [Group X] [Finite X]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) X E) (hf : Function.Injective ρ)
    (N : Subgroup X) [N.Normal] (hq : IsPGroup 2 (X ⧸ N))
    (hc : pCore 2 X = ⊥) (hN : generalizedFitting N = pCore 7 N)
    (hb : quadraticRatio ρ ≤ 2) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hF : generalizedFitting X ≤ pCore 7 X := by
    have hl := generalizedFitting_le_normal_of_two_quotient N hq hc
    rw [hN] at hl
    exact hl.trans (le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩)
  have hself : centralizer (pCore 7 X : Set X) ≤ pCore 7 X :=
    (Subgroup.centralizer_le hF).trans ((centralizer_generalizedFitting_le X).trans hF)
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr
    ((cubicRatio_le_quadraticRatio ρ).trans hb)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hcomm : ⁅pCore 7 X,A⁆ = ⊥ := by
    by_contra hn
    have hh := (ChapterD.source_lemma_D_2_13_one_two ρ hf hA (by decide) hn).1
    omega
  have hA7 : A ≤ pCore 7 X :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans hself
  have hd := IsPGroup.disjoint_of_ne 2 7 (by decide) A (pCore 7 X)
    (IsElementaryAbelian.isPGroup 2 A) pCore_isPGroup
  exact hA.1.2.1.1 (bot_unique ((le_inf le_rfl hA7).trans hd.le_bot))

/-- The exceptional nonquasisimple point row is incompatible with the actual
abelian-span action on K₁T. This is the seven-core exclusion in 12.9.5(2). -/
theorem four_point_quasisimple_of_abelian_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L)
    (hJ : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G))) :
    IsQuasisimple (C.K1 ⧸ pCore 2 C.K1) := by
  by_contra hn
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let J := C.K1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H := sup_le C.point_le (F.invariant 1)
  let N := C.K1.subgroupOf J
  have hN : N.IsCComponent := C.component.subgroupOf_of_le le_sup_left hJH
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal))
  let q := QuotientGroup.mk' (pCore 2 J)
  let D := N.map q
  let : D.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
  let e₀ : N ≃* C.K1 := subgroupOfEquivOfLe le_sup_left
  let e : (C.K1 ⧸ pCore 2 C.K1) ≃* D :=
    (QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)).symm.trans
      (cComponentTwoCoreQuotientEquiv hN)
  have hnD : ¬ IsQuasisimple D := fun hh => hn (hh.of_mulEquiv e.symm)
  have hsJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Components.Gi_twoLocal h F 1 (by decide))).subgroup _)
  have ha := Chapter1.Section02.proposition_1_2_1_four_earlier_conclusion
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    (ChapterE.Structure.sqtk_two_quotient hsJ (pCore 2 J) pCore_isPGroup) hN
  have haD := Chapter1.RadicalStructure.nonsimple_radical ha hnD
  have hm := (Components.component_nonquasisimple_seven_core h F 1
    (Or.inr ⟨rfl,Or.inl rfl⟩) rfl ⟨C.point_le,C.component⟩ C.contains hn).1
  let e₇ : pCore 7 (C.K1 ⧸ pCore 2 C.K1) ≃* pCore 7 D :=
    ((pCore 7 (C.K1 ⧸ pCore 2 C.K1)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 7 e))
  have hcard : Nat.card (pCore 7 D) = 49 := by
    rw [←Nat.card_congr e₇.toEquiv,Nat.card_congr hm.some.toEquiv]
    simp
  have h7 : 7 ∣ Nat.card (fittingSubgroup D) :=
    (show 7 ∣ Nat.card (pCore 7 D) by rw [hcard]; decide).trans
      (card_dvd_of_le (pCore_le_fitting D 7))
  have hfit := seven_fitting_of_nonsimple_radical haD h7
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show C.K1 ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hgenq : D ⊔ ((T : Subgroup G).subgroupOf J).map q = ⊤ := by
    change N.map q ⊔ ((T : Subgroup G).subgroupOf J).map q = ⊤
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 ((J ⧸ pCore 2 J) ⧸ D) :=
    isPGroup_quotient_of_sup_eq_top D _ (T.isPGroup'.comap_subtype.map q) hgenq
  obtain ⟨hU,a,ha⟩ := abelian_local_quadratic_bound h earlier F hab J hJ
  let := hU
  exact no_quadratic_bound_of_seven_fitting_extension a.representation a.faithful
    D hquot (pCore_quotient_pCore_eq_bot 2) hfit ha

/-- Apply the exceptional-row exclusion after source 12.9.5(1), retaining
only its quotient-centralizer bound and the original outer-two fact. -/
theorem four_point_quasisimple_of_controlled_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hab : IsMulCommutative F.U)
    (C : ComponentGeometry F L)
    (ho : IsPGroup 2 (MulAut.Outer (C.K1 ⧸ pCore 2 C.K1)))
    (hc : pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    IsQuasisimple (C.K1 ⧸ pCore 2 C.K1) :=
  four_point_quasisimple_of_abelian_join h earlier F hab C
    (point_join_mem_Hz_of_quotient_centralizer h earlier F C ho hc)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
