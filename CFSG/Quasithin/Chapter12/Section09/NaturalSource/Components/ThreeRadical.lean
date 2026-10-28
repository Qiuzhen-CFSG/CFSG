module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.JankoComplete
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryContaining
public import Theory.SpecificGroups.SL2.LinearThreeSection
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceSwapped.Detection
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import Theory.GroupTheory.CComponent.NormalOrbitRank
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension

/-!
# The nonquasisimple three-space component in the natural flag

The actual linear-three residual forces the nonquasisimple containing
component to have an elementary seven-core of order 49 and SL₂(7) quotient.
Its characteristic Ξ₇ radical centralizes the original three-space. Ambient
even characteristic and uniqueness over LT show that it is not normal in
the point normalizer. The source Ξ-component detection theorem therefore
places it in an ordinary component orbit there.

This adapts the checked radical argument of Section05 to the literal
natural flag, including its degree-five solvable residual convention.
ThreeComplete applies it to the original degree-five component assertion.
Source: Aschbacher--Smith 12.9.3, printed p.858; compare 12.5.3, pp.818--819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open Chapter1.Section02.LocalModels BinaryLinear.OuterCyclic
private theorem seven_core_of_nonquasisimple
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : Nat.card (B ⧸ pCore 2 B) = 168)
    (f : B →* A) [Group.IsSolvable f.ker]
    (h : Chapter1.Section02.A36Natural A ∨ Chapter1.Section02.A36Nilpotent A) :
    ElementaryModel 7 2 (pCore 7 A) ∧ IsSL (A ⧸ pCore 7 A) 2 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have parameter (N : Subgroup A) [N.Normal] [Group.IsSolvable N]
      {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hm : IsSL (A ⧸ N) 2 p) : p = 7 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let g := e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)
    let : Group.IsSolvable g.ker := by
      change Group.IsSolvable (e.toMonoidHom.comp ((QuotientGroup.mk' N).comp f)).ker
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
        QuotientGroup.ker_mk']
      exact isSolvable_comap_of_solvable_ker f N
    exact Theory.SL2.prime_eq_seven_of_solvable_kernel hB hp hp3 hF g
  rcases h with h | h
  · obtain ⟨p,hp,hp3,ha⟩ := h.2
    let N := generalizedFitting A
    let : Group.IsNilpotent N := by change Group.IsNilpotent (generalizedFitting A); rw [h.1]; infer_instance
    obtain ⟨F,_,_,hF,v,ρ,hact⟩ := ha
    have he : p = 7 := parameter N hp hp3 ⟨F,inferInstance,inferInstance,hF,⟨ρ⟩⟩
    have hF7 : Nat.card F = 7 := hF.trans he
    have hc : Nat.card N = 7^2 := (Chapter1.RadicalStructure.natural_elementary
      ⟨F,inferInstance,inferInstance,hF7,v,ρ,hact⟩).2
    have hN : N = pCore 7 A := h.1.trans
      (Chapter1.RadicalStructure.fitting_eq_core (by
        rw [←h.1]; exact IsPGroup.of_card hc))
    let : Fintype F := Fintype.ofFinite F
    have hfc : Fintype.card F = Fintype.card (ZMod 7) := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF7
    let a : F ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hfc
    refine ⟨?_,?_⟩
    · rw [←hN]
      exact ⟨v.trans (AddEquiv.piCongrRight (fun _ : Fin 2 => a.toAddEquiv)).toMultiplicative⟩
    · exact ⟨F,inferInstance,inferInstance,hF7,
        ⟨(QuotientGroup.quotientMulEquivOfEq hN.symm).trans ρ⟩⟩
  · let := h.2.1
    have he := parameter (generalizedFitting A) (by decide : Nat.Prime 5) (by decide) h.2.2.1
    norm_num at he

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The literal linear-three quotient at the source indices. -/
theorem Li_three_core_equiv
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) (i : ℕ) (hi : ComponentIndex n i)
    (hd : max i (n-i) = 3) :
    Nonempty ((F.Li L i ⧸ pCore 2 (F.Li L i)) ≃* SL(3,ZMod 2)) := by
  let := h.chosen.elementary
  obtain ⟨d,he,_,⟨e⟩⟩ := Li_core_linear F h.naturalMarking i hi
  have he' : d = 3 := he.trans hd
  rw [he'] at e
  exact ⟨e.trans (slEquivLinear 3).symm⟩

/-- The only nonquasisimple quotient has its actual elementary seven-core
and actual SL₂(7) quotient, at each source linear-three index. -/
theorem component_nonquasisimple_seven_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : InvariantFlag T V n) (i : ℕ) (hi : ComponentIndex n i)
    (hd : max i (n-i) = 3) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi i)) (hLD : F.Li L i ≤ D)
    (hn : ¬ IsQuasisimple (D ⧸ pCore 2 D)) :
    ElementaryModel 7 2 (pCore 7 (D ⧸ pCore 2 D)) ∧
      IsSL ((D ⧸ pCore 2 D) ⧸ pCore 7 (D ⧸ pCore 2 D)) 2 7 := by
  let B := F.Li L i
  let b := (Li_three_core_equiv h F i hi hd).some
  let := h.chosen.elementary
  let : IsQuasisimple (B ⧸ pCore 2 B) := Li_core_quasisimple F h.naturalMarking i hi
  have hbtop := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 B) pCore_isPGroup (Li_twoPerfect F i)
  let := hbtop.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := B)).toMonoidHom) topEquiv.surjective
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := b.isSimpleGroup
  have hb : Nat.card (B ⧸ pCore 2 B) = 168 :=
    (Nat.card_congr b.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
  let H := F.Gi i
  let C := (D.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  let a := subgroupOfEquivOfLe hD.1
  let e : (D ⧸ pCore 2 D) ≃* C :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hD.2)
  have hnC : ¬ IsQuasisimple C := fun hq => hn (hq.of_mulEquiv e.symm)
  let f : B →* C := e.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 D)).comp (inclusion hLD))
  have hf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (e.toMonoidHom.comp
      ((QuotientGroup.mk' (pCore 2 D)).comp (inclusion hLD))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLD)
  let : Group.IsNilpotent f.ker := hf.isNilpotent
  have hc := Chapter1.Section02.proposition_1_2_1_four_earlier_conclusion
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    (ChapterE.Structure.sqtk_two_quotient
      (h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F i (by
        rcases hi with ⟨_,hlo,_⟩ | ⟨_,he⟩ <;> omega)))
      (pCore 2 H) pCore_isPGroup) hD.2
  obtain ⟨hm,hq⟩ := seven_core_of_nonquasisimple hb f
    (Chapter1.RadicalStructure.nonsimple_radical hc hnC)
  let a7 : pCore 7 (D ⧸ pCore 2 D) ≃* pCore 7 C :=
    ((pCore 7 (D ⧸ pCore 2 D)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 7 e))
  refine ⟨⟨a7.trans hm.some⟩,?_⟩
  obtain ⟨k,_,_,hk,⟨q⟩⟩ := hq
  exact ⟨k,inferInstance,inferInstance,hk,
    ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 7 e)).trans q⟩⟩

/-- A containing component in M equals the original residual, for either
of the source residual conventions. -/
theorem component_eq_of_le_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (i : ℕ) (hi : ComponentIndex n i)
    {D : Subgroup G} (hD : D ∈ Chapter1.cComponentsIn (F.Gi i))
    (hLD : F.Li L i ≤ D) (hDM : D ≤ normalizer (L : Set G)) : D = F.Li L i := by
  let H := F.Gi i
  let C := D.subgroupOf H
  let e : C ≃* D := subgroupOfEquivOfLe hD.1
  let : Group.IsPerfect C := hD.2.perfect
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let R := (L.subgroupOf H).subgroupOf C
  let : R.Normal := normal_subgroupOf_of_le_normalizer (by
    intro c hc l
    exact hDM hc (l : G))
  have hR : R = ⊤ := by
    by_contra hne
    let : Group.IsSolvable R := hD.2.isSolvable_of_subnormal_lt_top
      (inferInstance : R.Normal).isSubnormal hne
    let f : F.Li L i →* R :=
      { toFun := fun b => ⟨⟨⟨b,(F.Li_le L i b.property).2⟩,hLD b.property⟩,
          (F.Li_le L i b.property).1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro a b he
      exact Subtype.ext (congrArg (fun x : R => (((x : C) : H) : G)) he)
    exact Chapter1.mem_L_not_isSolvable (Li_mem_local h earlier F i hi)
      (Group.isSolvable_of_isSolvable_injective hf)
  have hDL : D ≤ L := by
    intro d hd
    have hr : (⟨⟨d,hD.1 hd⟩,hd⟩ : C) ∈ R := hR.symm ▸ mem_top _
    exact hr
  have hN : D ≤ L ⊓ F.Gi i := le_inf hDL hD.1
  let a := subgroupOfEquivOfLe hN
  let : Group.IsPerfect (D.subgroupOf (L ⊓ F.Gi i)) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  have hres := le_solvableResidual_of_isPerfect (D.subgroupOf (L ⊓ F.Gi i))
  have hsol : D ≤ (solvableResidual (L ⊓ F.Gi i : Subgroup G)).map (L ⊓ F.Gi i).subtype := by
    intro d hd
    exact mem_map_of_mem _ (hres (show (⟨d,hN hd⟩ : (L ⊓ F.Gi i : Subgroup G)) ∈
      D.subgroupOf (L ⊓ F.Gi i) from hd))
  apply le_antisymm _ hLD
  unfold Li
  split_ifs
  · exact hsol
  · let : Group.IsNilpotent ((L ⊓ F.Gi i : Subgroup G) ⧸ pResidual 2 (L ⊓ F.Gi i : Subgroup G)) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact hsol.trans (map_mono (solvableResidual_le_of_solvable_quotient _))


/-- The characteristic seven-radical fixes the original three-space pointwise. -/
theorem three_radical_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n) {D : Subgroup G}
    (hDG : D ≤ F.Gi 3) (hLD : F.Li L 3 ≤ D) :
    Chapter1.XiP 7 D ≤ centralizer (F.Vi 3 : Set G) := by
  let := h.chosen.elementary
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 D
  let A := X.subgroupOf D
  let Y := BinaryLinear.GL (space (V := V) (F.Vi 3))
  let f := (flagLinearAction F 3).comp (inclusion hDG)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨l,hl⟩ := Li_flagLinearAction_surjective F h.naturalMarking 3 (by decide) (by omega) a
    exact ⟨inclusion hLD l,hl⟩
  let e₀ := (Module.finBasisOfFinrankEq (ZMod 2) _ (flag_space_finrank F 3 (by omega))).equivFun
  let e : Y ≃* SL(3,ZMod 2) :=
    (BinaryLinear.SmallParabolicLevi.linearGroupCongr e₀).trans (slEquivLinear 3).symm
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  let : IsSimpleGroup Y := e.isSimpleGroup
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : A.Normal := inferInstance
  let : Group.IsSolvable X := Chapter1.RadicalNormalizers.XiP_solvable 7 (by decide) D
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (Chapter1.XiP_le 7 D)).toMonoidHom)
    (subgroupOfEquivOfLe (Chapter1.XiP_le 7 D)).injective
  let : (A.map f).Normal := Normal.map inferInstance f hf
  let : Group.IsSolvable (A.map f) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap A) (f.subgroupMap_surjective A)
  have he : A.map f = ⊥ := by
    rcases (inferInstance : (A.map f).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · let : Group.IsSolvable (⊤ : Subgroup Y) := he ▸ (inferInstance : Group.IsSolvable (A.map f))
      exact (Group.IsPerfect.not_isSolvable Y
        (Group.isSolvable_of_surjective (f := (topEquiv (G := Y)).toMonoidHom)
          topEquiv.surjective)).elim
  have hk : A ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
  intro x hx v hv
  have hxk := hk (show (⟨x,Chapter1.XiP_le 7 D hx⟩ : D) ∈ A from hx)
  change flagLinearAction F 3 ⟨x,hDG (Chapter1.XiP_le 7 D hx)⟩ = 1 at hxk
  have hval := congrArg (fun a => (a
    (⟨Additive.ofMul ⟨v,F.le_seed 3 hv⟩,hv⟩ : space (V := V) (F.Vi 3))).val.toMul.val) hxk
  change x * v * x⁻¹ = v at hval
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- The radical lies in the literal point normalizer. -/
theorem three_radical_le_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n) {D : Subgroup G}
    (hDG : D ≤ F.Gi 3) (hLD : F.Li L 3 ≤ D) :
    Chapter1.XiP 7 D ≤ F.H :=
  (three_radical_centralizes h hn F hDG hLD).trans
    ((centralizer_le (F.monotone (by decide : 1 ≤ 3))).trans (Subgroup.centralizer_le_normalizer _))

/-- The actual radical is a member of the source Ξ family, with noncyclic
seven-quotient and irreducible action by the original full Sylow. -/
theorem three_radical_mem_Xi
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 3)) (hLD : F.Li L 3 ≤ D)
    (hN : (D.subgroupOf (F.Gi 3)).Normal) (hq : ¬ IsQuasisimple (D ⧸ pCore 2 D)) :
    Chapter1.XiP 7 D ∈ Chapter1.Xi G (T : Subgroup G) ∧
      Chapter1.XiOddQuotient 7 (Chapter1.XiQuotient (Chapter1.XiP 7 D)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hT : (T : Subgroup G) ≤ F.Gi 3 := F.invariant 3
  have hlocal : D ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent
      (Chapter1.mem_H_of_isTwoLocal (Gi_twoLocal h F 3 (by decide)))
      ⟨T.subtype hT,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT]⟩ hD.1 hD.2
  let J := D ⊔ (T : Subgroup G)
  have hJG : J ≤ F.Gi 3 := sup_le hD.1 hT
  have hJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 3 (by decide))).subgroup (J.subgroupOf (F.Gi 3)))
  have hQ := ChapterE.Structure.sqtk_two_quotient hJ (pCore 2 J) pCore_isPGroup
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hTD := hT.trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hN)
  have hi : ComponentIndex n 3 := by
    rcases hn with rfl | rfl
    · exact Or.inr ⟨rfl,Or.inr rfl⟩
    · exact Or.inl ⟨rfl,by decide,by decide⟩
  obtain ⟨hm,_⟩ := component_nonquasisimple_seven_core h F 3 hi (by omega) hD hLD hq
  have hc : Nat.card (pCore 7 (D ⧸ pCore 2 D)) = 49 := by
    rw [Nat.card_congr hm.some.toEquiv]; simp
  have hd : 7 ∣ Nat.card (fittingSubgroup (D ⧸ pCore 2 D)) :=
    dvd_trans (by rw [hc]; decide) (card_dvd_of_le (pCore_le_fitting (D ⧸ pCore 2 D) 7))
  have hquot := (Chapter1.XiP_oddQuotient_of_A36 hA36 hlocal hQ hq (by decide : Odd 7) hd).2
  refine ⟨⟨Chapter1.XiP_isPPerfect 7 D,Chapter1.XiP_invariant 7 hTD,
    Chapter1.XiP_join_mem_H 7 hlocal,⟨7,by decide,by decide,hquot⟩,?_⟩,hquot⟩
  exact Chapter1.RadicalActions.XiP_irreducible_of_A36 hA36 hlocal hQ hq hTD (by decide) hd

/-- The noncyclic seven-quotient supplies rank at least two in the actual radical. -/
theorem three_radical_seven_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 3)) (hLD : F.Li L 3 ≤ D)
    (hN : (D.subgroupOf (F.Gi 3)).Normal) (hq : ¬ IsQuasisimple (D ⧸ pCore 2 D)) :
    2 ≤ primeRank 7 (Chapter1.XiP 7 D) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨hx,hquot⟩ := three_radical_mem_Xi h hn F hD hLD hN hq
  let P : Sylow 7 (Chapter1.XiP 7 D) := Classical.choice inferInstance
  by_contra hr
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)
  exact hquot.not_isCyclic ((hx.sylowQuotientEquiv (by decide) hquot P).isCyclic.mp hc)

/-- The radical has nontrivial two-core by the ambient even-characteristic
hypothesis, applied inside its original three-space normalizer. -/
theorem three_radical_core_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (F : InvariantFlag T V n) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 3)) (hLD : F.Li L 3 ≤ D)
    (hN : (D.subgroupOf (F.Gi 3)).Normal) (hq : ¬ IsQuasisimple (D ⧸ pCore 2 D)) :
    (Chapter1.XiP 7 D).pCoreIn 2 ≠ ⊥ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 D
  have hX : X ≠ ⊥ := by
    intro he
    have hr := three_radical_seven_rank h hn F hD hLD hN hq
    change 2 ≤ primeRank 7 X at hr
    rw [he] at hr
    have hz : primeRank 7 (⊥ : Subgroup G) = 0 :=
      PrimeRank.eq_zero_iff_not_dvd_card.mpr (by simp)
    omega
  have hXG : X ≤ F.Gi 3 := (Chapter1.XiP_le 7 D).trans hD.1
  have hXN : (X.subgroupOf (F.Gi 3)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (Chapter1.XiP_invariant 7 ((normal_subgroupOf_iff_le_normalizer hD.1).mp hN))
  have hHe := Chapter1.lemma_1_1_3_1
    (Chapter1.twoLocal_mem_He_of_sylow_le T (h.source.simpleQTKE.evenCharacteristic T)
      (Gi_twoLocal h F 3 (by decide)) (F.invariant 3)) hX hXG hXN.isSubnormal
  change X ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ X.pCoreIn 2 at hHe
  intro he
  change X.pCoreIn 2 = ⊥ at he
  apply hX
  apply bot_unique
  intro x hx
  apply he ▸ hHe
  refine ⟨hx,?_⟩
  intro y hy
  have hy1 : y = 1 := hy
  simp [hy1]

/-- Normality of the radical in G₁ would make LT normalize its nontrivial
two-core. Uniqueness over LT then collapses the original three-component. -/
theorem three_radical_not_normal_in_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 3)) (hLD : F.Li L 3 ≤ D)
    (hN : (D.subgroupOf (F.Gi 3)).Normal) (hq : ¬ IsQuasisimple (D ⧸ pCore 2 D)) :
    ¬ ((Chapter1.XiP 7 D).subgroupOf F.H).Normal := by
  intro hx
  let := h.chosen.elementary
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 D
  have h1 : F.Li L 1 ≤ normalizer (X : Set G) :=
    ((F.Li_le L 1).trans inf_le_right).trans
      ((normal_subgroupOf_iff_le_normalizer (three_radical_le_point h hn F hD.1 hLD)).mp hx)
  have h3 : F.Gi 3 ≤ normalizer (X : Set G) :=
    Chapter1.XiP_invariant 7 ((normal_subgroupOf_iff_le_normalizer hD.1).mp hN)
  have hL : L ≤ normalizer (X : Set G) := by
    rw [← flag_generation_of_linear F h.naturalMarking.geometryAction h.residual 3
      (flag_linear_generation F (by omega) 3 (by decide) (by omega))]
    exact conjugateSpanBy_le h1
      ((inf_le_right.trans h3).trans (normalizer (X : Set G)).le_normalizer)
  have hc : normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  have hM : normalizer (X.pCoreIn 2 : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hJN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique earlier.structural earlier.uniqueness).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN,hJN⟩)
    · exact isPGroup_pCoreIn 2 X
    · exact three_radical_core_ne_bot h hn F hD hLD hN hq
    · exact (sup_le hL ((F.invariant 3).trans h3)).trans hc
  have hi : ComponentIndex n 3 := by
    rcases hn with rfl | rfl
    · exact Or.inr ⟨rfl,Or.inr rfl⟩
    · exact Or.inl ⟨rfl,by decide,by decide⟩
  have he := component_eq_of_le_normalizer h earlier F 3 hi hD hLD
    (hD.1.trans (h3.trans (hc.trans hM)))
  exact hq (he ▸ Li_core_quasisimple F h.naturalMarking 3 hi)

/-- Source 1.3.4 detects an actual ordinary component orbit containing the
radical inside the original point normalizer. -/
theorem three_radical_point_component_orbit
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 3)) (hLD : F.Li L 3 ≤ D)
    (hN : (D.subgroupOf (F.Gi 3)).Normal) (hq : ¬ IsQuasisimple (D ⧸ pCore 2 D)) :
    ∃ Q : Subgroup G, Q ∈ Chapter1.cComponentsIn F.H ∧
      IsQuasisimple (Q ⧸ pCore 2 Q) ∧
      Chapter1.XiP 7 D ≤ componentOrbit Q (T : Subgroup G) ∧
      ((componentOrbit Q (T : Subgroup G)).subgroupOf F.H).Normal := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let X := Chapter1.XiP 7 D
  obtain ⟨hX,hquot⟩ := three_radical_mem_Xi h hn F hD hLD hN hq
  have ht : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) F.H :=
    ⟨T.subtype ht,by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le ht]⟩
  let P : Sylow 7 X := Classical.choice inferInstance
  have d := Chapter1.XiEmbedding.localInput_of_mem_Xi hX hT
    (sup_le (three_radical_le_point h hn F hD.1 hLD) (F.invariant 1)) (by decide : Odd 7) hquot P
  rcases d.normal_or_detected_containment
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      (h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))) hT with
    hx | ⟨Q,hQ,hNQ,_,_,hXQ⟩
  · exact (three_radical_not_normal_in_point h hn earlier F hD hLD hN hq hx).elim
  · exact ⟨Q,hQ.mem,hQ.quasisimple,hXQ,hNQ⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
