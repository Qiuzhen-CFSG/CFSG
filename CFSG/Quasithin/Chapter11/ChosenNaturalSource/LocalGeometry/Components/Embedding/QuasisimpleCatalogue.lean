module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.LargeSporadic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining

/-!
# The complete quasisimple relative-component embedding catalogue

The original relative SQTK group supplies A.3.6 for the actual image of
its containing component modulo the ambient two-core. When the intrinsic
component quotient is quasisimple, that theorem gives the complete simple
or central-three-cover catalogue. The canonical component quotient
isomorphism retains the original subgroup and its intrinsic two-core.

The simple branch is now exhaustive. In the covering branch, the established
embedding results handle binary SL₃, binary SU₃, both odd ternary signs,
3.A₆, 3.A₇ and 3.M₂₂. The binary linear cover's mod-three condition excludes
degree one. Thus every covering row yields the literal same-field 11.1.1
alternative, without an assumed carrier list or field comparison.

Applications retain both original flag normalizers, full V₂, and arbitrary
eligible nontrivial U ≤ V₁ with N_T(U) Sylow. Quasisimplicity is an explicit
branch condition; the nonquasisimple odd-extension source branch remains
with qt-d-1222-natural-relative-components, together with the remaining
11.1.2 refinements and triangle. The preceding flag markings and pointwise
line action belong to qt-d-1222-natural-flag-cartan and are discharged by
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith A.3.6, A.3.12--14 and 11.1.1,
printed pp.43--50,761, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private def center_quotient_equiv {A C : Type*} [Group A] [Group C] (e : A ≃* C) :
    (A ⧸ center A) ≃* (C ⧸ center C) :=
  QuotientGroup.congr (center A) (center C) e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem three_cover_transport {A C : Type*} {M : Type} [Group A] [Group C] [Group M]
    (e : A ≃* C) (h : IsThreeCover C M) : IsThreeCover A M := by
  obtain ⟨hq,⟨z⟩,⟨a⟩⟩ := h
  let := hq
  exact ⟨IsQuasisimple.of_mulEquiv e.symm,⟨(centerCongr e).trans z⟩,
    ⟨(center_quotient_equiv e).trans a⟩⟩

/-- Every actual central-three-cover row in A.3.6 gives the same-field
11.1.1 alternative, retaining both special linear and unitary coverings. -/
theorem relative_component_alternative_of_three_cover
    {H B K P : Subgroup G} (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    {A : Type*} [Group A] (e : (K ⧸ pCore 2 K) ≃* A)
    (hmodel : ThreeCoverModel A) : ComponentAlternative B K n := by
  let : Group.IsPerfect B := by
    let := hB.1.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  cases hmodel with
  | classical u q hq hmodel =>
    have ht : IsSLSign (K ⧸ pCore 2 K) u 3 q := by
      cases u
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hmodel
        exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩
      · obtain ⟨F,_,_,J,hF,hconj,⟨a⟩⟩ := hmodel
        exact ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨e.trans a⟩⟩
    rcases hq with ⟨m,hmpos,rfl,hmod⟩ | ⟨hp,ho⟩
    · cases u
      · have hm2 : 1 < m := by
          by_contra h
          have hm1 : m = 1 := by omega
          norm_num [hm1] at hmod
        exact relative_component_alternative_of_split_or_ree hP hB hK hBK hn hm
          (.inl ⟨m,hm2,.inl ht⟩)
      · exact .equal (relative_eq_of_nonEnlarging_carrier hP hB hK hBK
          (.inr (.inl ⟨m,hmpos,ht⟩)))
    · obtain ⟨hn2,rfl⟩ := relative_odd_ternary_parameters hP hB hK hBK hPB hn hm hp ho u (.inr ht)
      exact .four hn2 (.three u (.inr ht))
  | alternating_six hmodel =>
    exact .equal (relative_eq_of_nonEnlarging_carrier hP hB hK hBK
      (.inr (.inr (.inr (.inr (three_cover_transport e hmodel))))))
  | alternating_seven hmodel =>
    exact component_alternative_of_small_finite hBK hn hm
      (.inr (.inl (three_cover_transport e hmodel)))
  | mathieu hmodel =>
    exact component_alternative_of_small_sporadic hBK hn hm
      (.inr (.inl (three_cover_transport e hmodel)))

/-- The source-derived 11.1.1 classification for every quasisimple two-core
quotient. A.3.6 supplies the full covering catalogue; no model list is assumed. -/
theorem relative_quasisimple_component_alternative
    {H B K P : Subgroup G} (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hP : Chapter1.IsSylowIn 2 P H)
    (hB : B ∈ Chapter1.L G P) (hK : Source.ComponentIn H K) (hBK : B ≤ K)
    (hPB : P ≤ normalizer (B : Set G)) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    [IsQuasisimple (K ⧸ pCore 2 K)] : ComponentAlternative B K n := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := K.subgroupOf H
  let C := J.map q
  let k := subgroupOfEquivOfLe hK.1
  let kq := QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let e : (K ⧸ pCore 2 K) ≃* C := kq.symm.trans (cComponentTwoCoreQuotientEquiv hK.2)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e
  have hQ := ChapterE.Structure.sqtk_two_quotient hH (pCore 2 H) pCore_isPGroup
  rcases SourceEmbeddings.quasisimple_containing_component_models_knownSimple hQ
      (pCore_quotient_pCore_eq_bot 2) (hK.2.map_quotient (pCore 2 H)) with ⟨hs,_⟩ | ⟨_,hc⟩
  · let := hs
    let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
    exact relative_simple_component_alternative hH hP hB hK hBK hPB hn hm
  · exact relative_component_alternative_of_three_cover hP hB hK hBK hPB hn hm e hc

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Both original flag normalizers with every quasisimple quotient model,
including the central covering rows and the literal full V₂. -/
theorem flag_quasisimple_component_alternative (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) [IsQuasisimple (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li i) K S.field.degree := by
  have hTV : (T : Subgroup G) ≤ normalizer (f.Vi i.castSucc : Set G) := f.invariant i.castSucc
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G)
      (normalizer (f.Vi i.castSucc : Set G)) :=
    ⟨T.subtype hTV,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]⟩
  exact relative_quasisimple_component_alternative
    (S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal i.castSucc)) hs
    (flag_mem_local_of_model D S f i hm) hK hLK (f.sylow_normalizes_Li i) S.nonbinary hm

/-- The arbitrary-subspace clause for all quasisimple quotient models,
retaining the actual N_T(U) Sylow and pointwise V₁ action. -/
theorem subspace_quasisimple_component_alternative
    (U : Subgroup G) (hU : U ≠ ⊥) (hUV : U ≤ f.Vi 0)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (U : Set G))
      (normalizer (U : Set G)))
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (U : Set G)) K)
    (hLK : f.Li 0 ≤ K) [IsQuasisimple (K ⧸ pCore 2 K)] :
    ComponentAlternative (f.Li 0) K S.field.degree := by
  let : IsElementaryAbelian 2 (f.Vi 0) :=
    D.centralQuotientPreimage_elementary (c.binarySubspace (f.space 0))
  have htwo : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (f.Vi 0)).to_le hUV
  have hUL : f.Li 0 ≤ normalizer (U : Set G) :=
    (hfix.trans (centralizer_le hUV)).trans (Subgroup.centralizer_le_normalizer _)
  let P := (T : Subgroup G) ⊓ normalizer (U : Set G)
  have hUP : U ≤ P := le_inf
    (hUV.trans ((D.centralQuotientPreimage_le _).trans D.le_sylow)) U.le_normalizer
  have hcore : U ≤ (f.Li 0 ⊔ P).pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (hUP.trans le_sup_right) (sup_le hUL inf_le_right)
  have hlocal := flag_mem_local_of_model D S f 0 hm
  have hlocalP : f.Li 0 ∈ Chapter1.L G P :=
    ⟨hlocal.1.subgroupOf_of_le le_sup_left (sup_le_sup_left inf_le_left _),
      hSyl.restrict le_sup_right (sup_le hUL inf_le_right),
      fun he => hU (bot_unique (he ▸ hcore))⟩
  exact relative_quasisimple_component_alternative (S.source.simpleQTKE.twoLocal_sqtk ⟨U,hU,htwo,rfl⟩)
    hSyl hlocalP hK hLK (inf_le_left.trans (f.sylow_normalizes_Li 0)) S.nonbinary hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding
