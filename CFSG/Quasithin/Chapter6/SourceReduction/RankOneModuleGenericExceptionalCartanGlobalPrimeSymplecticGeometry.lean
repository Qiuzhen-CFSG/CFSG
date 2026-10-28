module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticSelection
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair
public import CFSG.Quasithin.ChapterF.Section01.CoreQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedSelection

/-!
# Complete symplectic right factors for the prime Cartan argument

The chosen perfect lifts retain their images in the literal source quotient.
The unique Sylow two-subgroup of the model Borel identifies the right Borel
with the original maximal overlap. Restriction of the original odd Hall
subgroup then gives its product with the Sylow intersection.

The action on the two actual parabolic conjugacy classes has kernel fixing
each local factor. It bounds the relative Sylow-normalizer index by two.
Together these calculations complete every RightData clause for both
symplectic factors, and construct the literal prime pair and its two core
branches. No equality between the original and residual field degrees is used.
The linear diagram selection and subsequent model exclusions remain with
qt-d-1222-rankone-cartan-local-to-global.

Source: Aschbacher--Smith E.2.2,5.1.11(3),5.2.1--2,
printed pp.215--216,635,646--649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X Y : Type*} [Group X] [Finite X] [Group Y]
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem model_sylow_in_borel {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    {A : Subgroup (Sp F)} (hUA : unipotent ≤ A) (P : Sylow 2 A)
    (hP : (P : Subgroup A).map A.subtype ≤ borel (F := F)) :
    (P : Subgroup A).map A.subtype = unipotent := by
  have hle : (P : Subgroup A).map A.subtype ≤ unipotent := by
    have hh := (unipotentSylow hF hf).is_maximal'
      ((P.isPGroup'.map A.subtype).to_sup_of_normal_right'
        (unipotentSylow hF hf).isPGroup' (hP.trans borel_le_normalizer_unipotent)) le_sup_right
    exact le_sup_left.trans hh.le
  have he := P.3 ((unipotentSylow hF hf).isPGroup'.comap_of_injective A.subtype A.subtype_injective)
    (map_le_iff_le_comap.mp hle)
  rw [←he]
  exact map_subgroupOf_eq_of_le hUA

omit [CharP F 2] in
private theorem mapped_sylow_eq_unipotent {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    (q : X →* Y) (j : Sp F →* Y) (hj : Function.Injective j)
    {M R : Subgroup X} {A : Subgroup (Sp F)}
    (hM : (M.map q).comap j = borel (F := F))
    (hR : R.map q = A.map j) (hUA : unipotent ≤ A)
    (P : Sylow 2 R) (hP : (P : Subgroup R).map R.subtype ≤ M) :
    ((P : Subgroup R).map R.subtype).map q = unipotent.map j := by
  let e := (MulEquiv.subgroupCongr hR).trans (A.equivMapOfInjective j hj).symm
  let a := e.toMonoidHom.comp (q.subgroupMap R)
  have ha : Function.Surjective a := e.surjective.comp (q.subgroupMap_surjective R)
  let Q := P.mapSurjective ha
  have hmap : ((Q : Subgroup A).map A.subtype).map j =
      ((P : Subgroup R).map R.subtype).map q := by
    change (((P : Subgroup R).map a).map A.subtype).map j = _
    simp only [map_map]
    congr 1
    ext x
    change j (e (q.subgroupMap R x)).val = q x.val
    exact congrArg Subtype.val ((A.equivMapOfInjective j hj).apply_symm_apply
      ((MulEquiv.subgroupCongr hR) (q.subgroupMap R x)))
  have hb : (Q : Subgroup A).map A.subtype ≤ borel (F := F) := by
    rw [←hM]
    apply map_le_iff_le_comap.mp
    rw [hmap]
    exact map_mono hP
  rw [←hmap,model_sylow_in_borel hF hf hUA Q hb]


/-- The canonical perfect lift maps onto the actual determinant kernel. -/
theorem symplecticSourceFactor.map_quotient {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (M C : Subgroup X) (e : sourceImage M C ≃* Sp F) (i : Bool) :
    (symplecticSourceFactor M C e i).map (QuotientGroup.mk' (sourceKernel M)) =
      (symplecticModelLocal F i).map ((sourceImage M C).subtype.comp e.symm.toMonoidHom) := by
  let A := symplecticModelLocal F i
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  let : Group.IsPerfect A := by
    cases i
    · exact planeLocal_perfect hF hf
    · exact pointLocal_perfect hF hf
  let : Group.IsPerfect (A.map j) := Group.IsPerfect.map j
  unfold symplecticSourceFactor
  simpa only [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype]
    using map_solvableResidual_comap (QuotientGroup.mk' (sourceKernel M))
      (QuotientGroup.mk'_surjective _) (A.map j)

/-- The literal rank-one Borel is the original maximal-subgroup intersection. -/
theorem symplecticSourceFactor.borel_eq_overlap {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (T : Sylow 2 X) {M C : Subgroup X} (hTM : (T : Subgroup X) ≤ M)
    (e : sourceImage M C ≃* Sp F)
    (he : (componentOverlap M C).map e.toMonoidHom = borel (F := F))
    (i : Bool)
    (hnot : ¬ symplecticSourceFactor M C e i ≤ M)
    (hquot : ChapterF.Source.IsRankOneModel
      (symplecticSourceFactor M C e i ⧸ pCore 2 (symplecticSourceFactor M C e i)))
    (P : Sylow 2 (symplecticSourceFactor M C e i))
    (hP : (P : Subgroup _).map (symplecticSourceFactor M C e i).subtype =
      (T : Subgroup X) ⊓ symplecticSourceFactor M C e i) :
    ChapterF.Source.borel (symplecticSourceFactor M C e i) (T : Subgroup X) =
      M ⊓ symplecticSourceFactor M C e i := by
  let R := symplecticSourceFactor M C e i
  let q := QuotientGroup.mk' (sourceKernel M)
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := (sourceImage M C).subtype_injective.comp e.symm.injective
  have hM : (M.map q).comap j = borel (F := F) := by
    rw [source_overlap_coordinate] at he
    exact (comap_equiv_eq_map_symm e.symm _).trans he
  have hUA : unipotent ≤ symplecticModelLocal F i := by
    cases i
    · exact inf_le_right
    · exact inf_le_left
  have hmP : ((T : Subgroup X) ⊓ R).map q = unipotent.map j := by
    rw [←hP]
    exact mapped_sylow_eq_unipotent hF hf.le q j hj hM (symplecticSourceFactor.map_quotient hf hF M C e i) hUA P
      (hP ▸ inf_le_left.trans hTM)
  have hbM : ChapterF.Source.borel R (T : Subgroup X) ≤ M := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := (symplecticSourceFactor.map_quotient hf hF M C e i).le (mem_map_of_mem q hx.1)
    have hn : q x ∈ normalizer (unipotent.map j : Set _) := by
      rw [←hmP]
      exact le_normalizer_map q (mem_map_of_mem q hx.2)
    have hny : y ∈ normalizer (unipotent (F := F) : Set (Sp F)) := by
      rw [←hxy] at hn
      change y ∈ (normalizer (unipotent.map j : Set _)).comap j at hn
      rwa [comap_normalizer_eq_of_le_range (map_le_range _ _),
        comap_map_eq_self_of_injective hj] at hn
    have hym : j y ∈ M.map q := by
      change y ∈ (M.map q).comap j
      rw [hM,borel_eq_normalizer_unipotent]
      exact hny
    rw [hxy] at hym
    have hpre : (M.map q).comap q = M := comap_map_eq_self (by
      rw [QuotientGroup.ker_mk'];exact M.normalCore_le)
    rw [←hpre]
    exact hym
  have hfacts := ChapterF.Source.rankOneBorelFacts_of_sylow R (T : Subgroup X) P hP
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient hquot P)
  apply le_antisymm (le_inf hbM inf_le_left)
  apply hfacts.unique_maximal
  · exact inf_le_inf hTM le_rfl
  · apply lt_of_le_of_ne inf_le_right
    intro hh
    exact hnot (hh.ge.trans inf_le_left)


omit [Finite X] in
/-- The two parabolic classes bound the normalizer index of either perfect lift. -/
theorem symplecticSourceFactor.normalizer_index_le_two {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    {M C U : Subgroup X} [C.Normal] (hUM : U ≤ M)
    (e : sourceImage M C ≃* Sp F)
    (he : (componentOverlap M C).map e.toMonoidHom = borel (F := F)) (i : Bool) :
    (U ⊓ normalizer (symplecticSourceFactor M C e i : Set X)).relIndex U ≤ 2 := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let N := sourceImage M C
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let j := N.subtype.comp e.symm.toMonoidHom
  have hM : (M.map q).comap j = borel (F := F) := by
    rw [source_overlap_coordinate] at he
    exact (comap_equiv_eq_map_symm e.symm _).trans he
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^f from Nat.pow_lt_pow_right (by decide) hf)
  let a := (extensionAction N e.symm).comp (q.comp U.subtype)
  let r := (parabolicClassAction hlarge).comp a
  have hkn : r.ker ≤ (normalizer (symplecticSourceFactor M C e i : Set X)).subgroupOf U := by
    intro u hu
    have hd : PreservesDiagram (a u) := (mem_parabolicClassAction_ker_iff hlarge _).mp hu
    have hb : (borel (F := F)).map (a u).toMonoidHom = borel (F := F) := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨x,hx,rfl⟩
        rw [←hM] at hx ⊢
        change j (a u x) ∈ M.map q
        rw [show j (a u x) = q u.val * j x * (q u.val)⁻¹ from
          extensionAction_apply N e.symm (q u.val) x]
        have hum : q u.val ∈ M.map q := mem_map_of_mem q (hUM u.property)
        exact (M.map q).mul_mem ((M.map q).mul_mem hum hx) ((M.map q).inv_mem hum)
      · rw [card_map_of_injective (a u).injective]
    have hU := EvenBorelTorus.FullTorusFixer.map_unipotent_of_map_borel hF (a u) hb
    have hl := local_pair_map_of_unipotent_map hF hf (a u) hd hU
    have hm : (symplecticModelLocal F i).map (a u).toMonoidHom = symplecticModelLocal F i := by
      cases i
      · exact hl.2
      · exact hl.1
    have hn : q u.val ∈ normalizer ((symplecticModelLocal F i).map j : Set _) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      calc
        _ = ((symplecticModelLocal F i).map (a u).toMonoidHom).map j := by
          rw [map_map,map_map]
          congr 1
          ext x
          exact (extensionAction_apply N e.symm (q u.val) x).symm
        _ = _ := by rw [hm]
    let P := ((symplecticModelLocal F i).map j).comap q
    exact (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
      (le_normalizer_comap q hn)
  rw [inf_relIndex_left]
  have hd := index_dvd_of_le hkn
  have hri : r.ker.index ≤ 2 := by
    rw [index_ker]
    apply le_trans (card_le_card_group r.range)
    let : Fintype (parabolicClasses hlarge) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    have hh : Fintype.card (parabolicClasses hlarge) ≤ 2 := by
      simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hlarge
    exact (Nat.factorial_le (n := 2) hh).trans (by decide)
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero r.ker.index_ne_zero_of_finite) hd).trans hri

/-- The symplectic diagram row supplies the full right-side local geometry. -/
theorem symplectic_source_rightData
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      ((pointParabolic (F := F)).subgroupOf (Sp4Derived F))
      ((planeParabolic (F := F)).subgroupOf (Sp4Derived F))) :
    ∃ R : Bool → Subgroup G, ∀ i, RightData T L H B (R i) ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) := by
  let S := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  obtain ⟨eF,hmark,hr⟩ := symplectic_source_original_factors_marked
    hTL hH hpar c hC hqs hc hf hF e he hmove
  let R0 := symplecticSourceFactor M C eF
  let R := fun i => (R0 i).map H.subtype
  have hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hSK := diagram_sourceS_intersection_residual hTL hH hpar hC hc hf
    (Or.inr ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,e,he,hmove⟩)
  let : C.Normal := DiagramHall.single_component_normal S hC hc
  refine ⟨R,?_⟩
  intro i
  obtain ⟨hRK,hout,hgen,hquot,hcomp,hSn,hBn,P,hP⟩ := hr i
  have hRH : R i ≤ H := map_subtype_le _
  have hSR : Global.sourceS L H ⊓ R i = (T : Subgroup G) ⊓ R i := by
    calc
      _ = (Global.sourceS L H ⊓ residual H) ⊓ R i := by rw [inf_assoc,inf_eq_right.mpr hRK]
      _ = _ := by rw [hSK,inf_assoc,inf_eq_right.mpr hRK]
  let er := (R0 i).equivMapOfInjective H.subtype H.subtype_injective
  let P0 := P.mapSurjective (f := er.symm.toMonoidHom) er.symm.surjective
  have hP0 : (P0 : Subgroup (R0 i)).map (R0 i).subtype = (S : Subgroup H) ⊓ R0 i := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,hST]
    calc
      _ = (P : Subgroup (R i)).map (R i).subtype := by
        change (((P : Subgroup (R i)).map er.symm.toMonoidHom).map (R0 i).subtype).map H.subtype = _
        simp only [map_map]
        congr 1
        ext x
        exact congrArg Subtype.val (er.apply_symm_apply x)
      _ = _ := hP.trans hSR
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  have hnot0 : ¬ R0 i ≤ M := by
    intro hh
    exact hout (map_le_iff_le_comap.mpr hh)
  have hq0 : ChapterF.Source.IsRankOneModel (R0 i ⧸ pCore 2 (R0 i)) :=
    .linear f (by omega) (hquot.of_mulEquiv eqr)
  have hb0 := symplecticSourceFactor.borel_eq_overlap hf hF S (comap_mono hTL) eF hmark i hnot0 hq0 P0 hP0
  have hb : ChapterF.Source.borel (R i) (Global.sourceS L H) =
      normalizer (L : Set G) ⊓ R i := by
    have hh := congrArg (map H.subtype) hb0
    change (ChapterF.Source.borel (R0 i) (S : Subgroup H)).map H.subtype =
      (M ⊓ R0 i).map H.subtype at hh
    rw [ChapterF.Source.borel_map_of_ker_le H.subtype (R0 i) S ⟨P0,hP0⟩
      (by rw [H.ker_subtype];exact bot_le),hST,
      Subgroup.map_inf _ _ _ H.subtype_injective,subgroupOf_map_subtype] at hh
    rw [inf_assoc,inf_eq_right.mpr hRH] at hh
    change R i ⊓ normalizer ((Global.sourceS L H ⊓ R i : Subgroup G) : Set G) = _
    rw [hSR]
    exact hh
  have hNC : (normalizer (R i : Set G)).comap H.subtype = normalizer (R0 i : Set H) := by
    rw [comap_normalizer_eq_of_le_range (by rw [range_subtype];exact hRH),
      comap_map_eq_self_of_injective H.subtype_injective]
  have hind : (normalizingSylow T (R i)).relIndex (T : Subgroup G) ≤ 2 := by
    change ((T : Subgroup G) ⊓ normalizer (R i : Set G)).relIndex (T : Subgroup G) ≤ 2
    rw [inf_relIndex_left,←hST,←relIndex_comap,hNC,←inf_relIndex_left]
    exact symplecticSourceFactor.normalizer_index_le_two hf hF (comap_mono hTL) eF hmark i
  refine ⟨⟨hRK,hout,hgen,?_,hcomp,hind,hSK,hSn,hBn,⟨P,hP⟩,
    .linear f (by omega) hquot,?_⟩,hquot⟩
  · intro hs
    let := hs
    exact hcomp.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show R i ≤ R i ⊔ normalizingSylow T (R i) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  · let U := normalizer (L : Set G) ⊓ R i
    have hU : U ≤ Global.intersection L H := le_inf inf_le_left (inf_le_right.trans hRH)
    have hBU : B ≤ normalizer (U : Set G) :=
      (le_inf ((c.right_le.trans inf_le_left).trans (normalizer (L : Set G)).le_normalizer)
        hBn).trans inf_normalizer_le_normalizer_inf
    have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hU hBU
    obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le (show U ≤ R i from inf_le_right)
      (hP.trans hSR ▸ le_inf (inf_le_left.trans hTL) inf_le_right)
    have heq := congrArg (map U.subtype) (OddHall.sylow_complement_of_hall Q hh).sup_eq_top
    have hi : B ⊓ U = B ⊓ R i := by
      dsimp [U]
      rw [←inf_assoc,inf_eq_left.mpr (c.right_le.trans inf_le_left)]
    rw [Subgroup.map_sup,hQ,hP,subgroupOf_map_subtype,hi,
      ←MonoidHom.range_eq_map,range_subtype] at heq
    rw [hb]
    exact heq.symm

/-- Both symplectic factors give the genuine F.1.1 pair in the zero-core
branch and the actual moving-factor normalizer in the other branch. -/
theorem symplectic_source_prime_pair
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      ((pointParabolic (F := F)).subgroupOf (Sp4Derived F))
      ((planeParabolic (F := F)).subgroupOf (Sp4Derived F))) :
    ∃ R : Bool → Subgroup G, ∀ i,
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      LocalData T L H B D (R i) ∧
      (((generated L H D (R i)).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R i] (Global.sourceS L H)) ∨
       ((generated L H D (R i)).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R i : Set G) ∧
        (normalizingSylow T (R i)).relIndex (T : Subgroup G) = 2)) := by
  obtain ⟨R,hr⟩ := symplectic_source_rightData h.sylow_normalizes hH hpar c hC hqs hc hf hF e he hmove
  refine ⟨R,?_⟩
  intro i
  let d := (hr i).1.localData h hH c hd
  refine ⟨(hr i).2,d,?_⟩
  by_cases hz : (generated L H D (R i)).pCoreIn 2 = ⊥
  · exact Or.inl ⟨hz,d.hypothesisF11 h hH c hd hz⟩
  · exact Or.inr ⟨hz,d.prime_actor_not_normalizes_right h hH c hd hz,
      d.normalizingSylow_index hH.1.1.2 c hd hz⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The remaining linear diagram source row, retaining the literal source
quotient, Borel marking and diagram action. The component two-core quotient
may be PSL₃ or SL₃; this definition does not identify those covers. -/
@[expose] def RightLinearDiagramSource (T : Sylow 2 G) (L H : Subgroup G) : Prop :=
  ∃ (C : Subgroup H) (f : ℕ), C.IsCComponent ∧
    IsQuasisimple (C ⧸ pCore 2 C) ∧
    C ⊔ (T : Subgroup G).subgroupOf H = ⊤ ∧ 1 < f ∧
    SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      0 < f ∧ Nat.card F = 2 ^ f ∧
      ∃ e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
        (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.borel F ∧
        MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
          ((T : Subgroup G).subgroupOf H) e (Matrix.PSL3.LinearThree.pointParabolic F)
          (Matrix.PSL3.LinearThree.lineParabolic F)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Source selection now leaves only the linear diagram row. The symplectic,
exchanged and all single-Bender alternatives construct the literal local pair. -/
theorem source_prime_pair_or_linear_diagram
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) :
    (∃ R : Subgroup G, LocalData T L H B D R) ∨ Global.RightLinearDiagramSource T L H := by
  rcases source_prime_pair_or_diagram h hH hpar c hd with hr | hs
  · exact Or.inl hr
  obtain ⟨C,f,hC,hqs,hgen,hf,hc,hm⟩ := hs
  rcases hm with hl | ⟨F,_,_,_,_,hF,e,he,hmove⟩
  · exact Or.inr ⟨C,f,hC,hqs,hgen,hf,hc,hl⟩
  · obtain ⟨R,hr⟩ := symplectic_source_rightData h.sylow_normalizes hH hpar c hC hqs hc hf hF e he hmove
    exact Or.inl ⟨R true,(hr true).1.localData h hH c hd⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
