module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.Linear
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL2

/-!
# The generation minimum from an elementary root lift

A model of K/O₂(K) does not by itself determine n(H). This module proves
an ambient lower obstruction that retains an actual elementary subgroup
of H mapping onto a full Sylow two-subgroup of the normal PSL₂ image.

Use all elementary subgroups whose quotient images lie in that simple
component and have the order of its Sylow. Inside a prescribed ambient
Sylow, every such image is the same root subgroup. Its weak-closure
normalizer therefore maps into the proper root normalizer. An E-member
containing a full root image either normalizes that root or contains the
simple component in its image. In the second case its intrinsic two-core
cannot kill any of the root image, so its quotient rank is at least the
field degree. This obstructs E-generation at every smaller rank.

The actual ComponentSeed application combines this obstruction with the
proved upper bound, identifying the literal model exponent with
ChapterE.generationParameter H. It then supplies RankOneReduction in the
normal PSL₂ row, retaining the original quotient map and relative normality.

The elementary full-root lift is an explicit, still unconstructed input;
it is not a consequence asserted here of an arbitrary two-core quotient.
Its construction, the other model rows, and unconditional recognition
remain with qt-d-1222-shadow-parameter-component. The independent doubled
parameter bound retains qt-d-1222-shadow-doubled-exclusion; final discharge
of the preceding source inputs stays with qt-d-1222-shadow-linear-geometry.
This module does not assert unconditional 11.3.5 or 11.3.6.

Source: Aschbacher--Smith, E.1.2--6, pp.210--211, and the generation
minimum used in 11.3.5(1), pp.771--772. Compare the E.2.2 quotient warning
in docs/quasithin-proof-basis.md.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
open ChapterE
variable {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]

omit [Finite X] [Finite Y] in
private theorem rank_range_le_of_ker_le {B : Type*} [Group B] [Finite B]
    (f : B →* X) (g : B →* Y) (h : f.ker ≤ g.ker) :
    Group.rank g.range ≤ Group.rank f.range := by
  let a := QuotientGroup.quotientKerEquivRange f
  let b := QuotientGroup.quotientKerEquivRange g
  let q := QuotientGroup.map f.ker g.ker (MonoidHom.id B) h
  have hq : Function.Surjective q := QuotientGroup.map_surjective_of_surjective
    f.ker g.ker (MonoidHom.id B) QuotientGroup.mk_surjective h
  exact Group.rank_le_of_surjective
    (b.toMonoidHom.comp (q.comp a.symm.toMonoidHom))
    (b.surjective.comp (hq.comp a.symm.surjective))

private theorem rank_image_le_core_image (q : X →* Y)
    (L : Subgroup Y) [IsSimpleGroup L] (hL : ¬ Group.IsSolvable L)
    (A K : Subgroup X) (hAK : A ≤ K) (hAL : A.map q ≤ L)
    (hLK : L ≤ K.map q) :
    Group.rank (A.map q) ≤
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) := by
  let j := q.subgroupMap K
  let R := (pCore 2 K).map j
  let : R.Normal := Subgroup.Normal.map inferInstance j (q.subgroupMap_surjective K)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    (j.subgroupMap_surjective (pCore 2 K))
  have hinj := Subgroup.RankOneSylowExtension.simple_quotient_injective hL
    (inclusion hLK) (inclusion_injective hLK) R
  let B := A.subgroupOf K
  let f := (QuotientGroup.mk' (pCore 2 K)).comp B.subtype
  let g := q.comp (K.subtype.comp B.subtype)
  have hker : f.ker ≤ g.ker := by
    intro x hx
    have hc : (x : K) ∈ pCore 2 K := (QuotientGroup.eq_one_iff _).mp hx
    have hxL : q (x.val : X) ∈ L := hAL (mem_map_of_mem q x.property)
    have he : (QuotientGroup.mk' R) (inclusion hLK ⟨q (x.val : X),hxL⟩) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem j hc)
    have he' := hinj (he.trans (map_one _).symm)
    exact congrArg (fun z : L => (z : Y)) he'
  have hr := rank_range_le_of_ker_le f g hker
  have hf : f.range = B.map (QuotientGroup.mk' (pCore 2 K)) := by
    dsimp only [f]
    rw [MonoidHom.range_comp,range_subtype]
  have hg : g.range = A.map q := by
    dsimp only [g]
    rw [MonoidHom.range_comp,MonoidHom.range_comp,range_subtype,
      map_subgroupOf_eq_of_le hAK]
  exact (Group.rank_congr (MulEquiv.subgroupCongr hg)).symm.le.trans
    (hr.trans (Group.rank_congr (MulEquiv.subgroupCongr hf)).le)

omit [Finite X] [Finite Y] in
private theorem map_conjugate (q : X →* Y) (A : Subgroup X) (g : X) :
    (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp

/-- A full elementary lift of a rank-one Sylow supplies the lower
obstruction in the original group, without quotient invariance of n(X). -/
theorem not_isEGenerated_of_rankOne_quotient_lift (q : X →* Y)
    (hq : Function.Surjective q)
    (L : Subgroup Y) [L.Normal] [IsSimpleGroup L]
    (hL : ¬ Group.IsSolvable L) (P : Sylow 2 L)
    (hproper : ∀ J : Subgroup L, (P : Subgroup L) ≤ J → J ≠ ⊤ →
      J ≤ normalizer (P : Set L))
    (hn : normalizer (P : Set L) ≠ ⊤)
    (A : Subgroup X) [IsElementaryAbelian 2 A]
    (hA : A.map q = (P : Subgroup L).map L.subtype)
    (i : ℕ) (hi : i < Group.rank P) : ¬ IsEGenerated i X := by
  let B : Subgroup Y := (P : Subgroup L).map L.subtype
  change A.map q = B at hA
  have hBL : B ≤ L := map_subtype_le _
  obtain ⟨T,hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let U := T.mapSurjective hq
  have hBU : B ≤ (U : Subgroup Y) := hA ▸ map_mono hAT
  have hB : B = (U : Subgroup Y) ⊓ L := by
    have hPU : (P : Subgroup L) ≤ (U : Subgroup Y).subgroupOf L :=
      map_le_iff_le_comap.mp hBU
    have he := P.is_maximal' U.isPGroup'.comap_subtype hPU
    change (U : Subgroup Y).subgroupOf L = (P : Subgroup L) at he
    rw [←subgroupOf_map_subtype,he]
  let Ω : Set (Subgroup X) := {C | IsElementaryAbelian 2 C ∧
    C.map q ≤ L ∧ Nat.card (C.map q) = Nat.card B}
  have hAΩ : A ∈ Ω := ⟨inferInstance,hA ▸ hBL,congrArg (fun C : Subgroup Y => Nat.card C) hA⟩
  have hΩ : IsElementaryFamily Ω := by
    refine ⟨fun C hC => hC.1,?_⟩
    intro g C hC
    let := hC.1
    refine ⟨IsElementaryAbelian.map _,?_,?_⟩
    · rw [map_conjugate]
      rintro _ ⟨c,hc,rfl⟩
      exact (inferInstance : L.Normal).conj_mem c (hC.2.1 hc) (q g)
    · rw [map_conjugate]
      exact (Nat.card_congr ((C.map q).equivMapOfInjective
        (MulAut.conj (q g)).toMonoidHom (MulAut.conj (q g)).injective).toEquiv).symm.trans hC.2.2
  have himage : ∀ C ∈ Ω, C ≤ (T : Subgroup X) → C.map q = B := by
    intro C hC hCT
    apply eq_of_le_of_card_ge
    · rw [hB]
      exact le_inf (map_mono hCT) hC.2.1
    · exact hC.2.2.ge
  have hw : (weakClosure (T : Subgroup X) Ω).map q = B := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro C hC
      exact map_le_iff_le_comap.mp (himage C hC.1 hC.2).le
    · rw [←hA]
      exact map_mono (le_sSup ⟨hAΩ,hAT⟩)
  have hnB : normalizer (B : Set Y) ≠ ⊤ := by
    intro he
    apply hn
    have hh := congrArg (comap L.subtype) he
    rw [comap_normalizer_eq_of_le_range (by simpa using hBL),
      show B.comap L.subtype = (P : Subgroup L) from
        comap_map_eq_self_of_injective L.subtype_injective _,comap_top] at hh
    exact hh
  let M := (normalizer (B : Set Y)).comap q
  have hM : M ≠ ⊤ := by
    intro he
    apply hnB
    have hh := congrArg (map q) he
    rwa [map_comap_eq_self_of_surjective hq,map_top_of_surjective _ hq] at hh
  apply ChapterE.ValuesEvenClassical.not_isEGenerated_of_members_le T Ω hΩ M hM
  · apply map_le_iff_le_comap.mp
    simpa only [hw] using (weakClosure (T : Subgroup X) Ω).le_normalizer_map q
  · intro C hC hCT J hJ
    have he := himage C hC hCT
    have hCJ := hJ.1.2.2.1
    rcases Subgroup.RankOneSylowExtension.le_or_le_normalizer L P hproper
      (J.map q) (show B ≤ J.map q from he ▸ map_mono hCJ) with hLJ | hJN
    · have hr := rank_image_le_core_image q L hL C J hCJ hC.2.1 hLJ
      have hu := ChapterE.ValuesEvenClassical.Sp4Lower.member_core_rank_le hJ
      have hri : i < Group.rank (C.map q) := by
        calc
          i < Group.rank P := hi
          _ = Group.rank B := Group.rank_congr ((P : Subgroup L).equivMapOfInjective
            L.subtype L.subtype_injective)
          _ = Group.rank (C.map q) := Group.rank_congr (MulEquiv.subgroupCongr he.symm)
      exact (Nat.not_le_of_gt hri (hr.trans hu)).elim
    · exact map_le_iff_le_comap.mp hJN

/-- The actual binary PSL₂ model turns the full elementary root lift into
an obstruction at the predecessor of its literal field exponent. -/
theorem not_isEGenerated_of_linear_quotient_lift (q : X →* Y)
    (hq : Function.Surjective q) (L : Subgroup Y) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hm : ClassicalGroup.IsPSL L 2 (2 ^ f))
    (P : Sylow 2 L) (A : Subgroup X) [IsElementaryAbelian 2 A]
    (hA : A.map q = (P : Subgroup L).map L.subtype) :
    ¬ IsEGenerated (f - 1) X := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfour : 4 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hf
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup L := e.isSimpleGroup
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let P₀ := ChapterF.Source.Linear.projectiveSylow F
  let P₁ := P₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hP₁ := ChapterF.Source.Linear.transport e.symm P₀ P₁ rfl
    (ChapterF.Source.Linear.projective_facts F f (by omega) hcard P₀)
  have hP := ChapterF.Source.Linear.all_sylows P₁ hP₁ P
  have hc₀ : Nat.card P₀ = 2 ^ f := by
    change Nat.card (ChapterF.Source.Linear.projectiveSylow F :
      Subgroup (BenderSuzuki.Converse.PSL2 F)) = _
    rw [ChapterF.Source.Linear.projectiveSylow_coe,
      BenderSuzuki.Converse.PUnip_card,hcard]
  have hc₁ : Nat.card P₁ = 2 ^ f := by
    change Nat.card ((P₀ : Subgroup (BenderSuzuki.Converse.PSL2 F)).map e.symm.toMonoidHom) = _
    rw [←Nat.card_congr ((P₀ : Subgroup (BenderSuzuki.Converse.PSL2 F)).equivMapOfInjective
      e.symm.toMonoidHom e.symm.injective).toEquiv]
    exact hc₀
  have hc : Nat.card P = 2 ^ f := (Nat.card_congr (P.equiv P₁).toEquiv).trans hc₁
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 ((P : Subgroup L).map L.subtype) := hA ▸ inferInstance
  let a := (P : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  apply not_isEGenerated_of_rankOne_quotient_lift q hq L
    (Group.IsPerfect.not_isSolvable L) P
    (fun J hPJ hJ => hP.unique_maximal J hPJ (lt_top_iff_ne_top.mpr hJ))
    hP.proper.ne A hA
  have hr := IsElementaryAbelian.rank_ge_of_card (p := 2) hc
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

/-- Identify the field exponent with the genuine generation minimum in the
normal model row, given an elementary lift of its full root Sylow. The lift
is in H and its image uses the original two-core quotient map. -/
theorem ComponentSeed.linear_parameter_eq_of_normal_lift (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A.map (QuotientGroup.mk' (pCore 2 H)) =
      (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
        ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype) :
    ChapterE.generationParameter H = f := by
  let B := K.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := B.map q
  let : B.Normal := hn
  let : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  let e := s.intrinsicQuotientEquiv.trans (cComponentTwoCoreQuotientEquiv s.component.2)
  have hmJ : ClassicalGroup.IsPSL J 2 (2 ^ f) := hm.of_mulEquiv e.symm
  have hlow := Models.not_isEGenerated_of_linear_quotient_lift q
    (QuotientGroup.mk'_surjective _) J hf hmJ P A hA
  apply Nat.le_antisymm (s.linear_parameter_le h pr hc hs hf hm)
  by_contra hlt
  have hk := degree_le_parameter h pr hc hs
  have hnpos := S.nonbinary
  exact hlow ((ChapterE.isEGenerated_generationParameter_of_pos (G := H) (by omega)).mono
    (by omega))

/-- The normal row feeds the actual 11.3.5 output: recognition is now at
n(H), and relative normality identifies K with the embedded O²(H). -/
theorem ComponentSeed.rankOneReduction_of_normal_linear_lift (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (P : Sylow 2 ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))))
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A.map (QuotientGroup.mk' (pCore 2 H)) =
      (P : Subgroup ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).map
        ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).subtype) :
    RankOneReduction S H := by
  have he := s.linear_parameter_eq_of_normal_lift h pr hc hs hn hf hm P A hA
  refine ⟨K,s.component,s.span,?_,fun _ => s.normal_iff_eq_residual.mp hn⟩
  rwa [he]
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
