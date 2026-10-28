module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Normalizers
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Binary

/-!
# Point-normalizer decomposition and the surviving degree-five model

The original point component induces the inner automorphisms of its two-core
quotient. When the outer automorphism group is a two-group, Sylow surjectivity
therefore gives G₁ = K₁ T C_G₁(K₁/O₂(K₁)), with the literal action and kernel.
For A₇, PSL₄(2) and PSL₅(2), the outer two-group assertion is proved, so the
source quotient-centralizer bound implies K₁T ∈ Hz. This removes that extra
premise from the actual LocalControl assembly.

In degree five, the original L₁ has PSL₄(2) two-core quotient and is strictly
contained in K₁ once the quotient centralizer is controlled. Quotient orders
exclude A₇; equality of two-core quotient orders for nested local components
excludes PSL₄(2). Thus the surviving list reduces to PSL₅(2).

The centralizer bound, the surviving model list, plane movement and the plane
centralizer bound remain source obligations of qt-d-1291-natural-source.

Source: Aschbacher--Smith, 12.9.5--7, printed pp.860--862 of refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- The original point component induces exactly the inner quotient action. -/
theorem point_component_action_image (F : InvariantFlag T V n) (C : ComponentGeometry F L) :
    (C.K1.subgroupOf F.H).map (pointQuotientAction C) =
      MulAut.innerSubgroup (C.K1 ⧸ pCore 2 C.K1) := by
  have hi (k : C.K1) : pointQuotientAction C (inclusion C.point_le k) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 C.K1) k) := by
    exact pCoreJoinAction_on_component 2
      ((F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)) k
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨QuotientGroup.mk' (pCore 2 C.K1) ⟨g,hg⟩, (hi ⟨g,hg⟩).symm⟩
  · rintro ⟨q,rfl⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C.K1) q
    exact ⟨inclusion C.point_le k,k.property,hi k⟩

/-- Outer two-group action gives the source G₁=K₁ T C_G₁(K₁/O₂(K₁)). -/
theorem point_normalizer_decomposition (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (ho : IsPGroup 2 (MulAut.Outer (C.K1 ⧸ pCore 2 C.K1))) :
    (C.K1 ⊔ pointQuotientCentralizer C) ⊔ (T : Subgroup G) = F.H := by
  let a := pointQuotientAction C
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (C.K1 ⧸ pCore 2 C.K1))).comp a
  have hk : f.ker = C.K1.subgroupOf F.H ⊔ a.ker := by
    rw [show f.ker = (QuotientGroup.mk' (MulAut.innerSubgroup (C.K1 ⧸ pCore 2 C.K1))).ker.comap a
      from (MonoidHom.comap_ker _ _).symm, QuotientGroup.ker_mk',
      ← point_component_action_image F C, comap_map_eq]
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  let U := S.mapSurjective f.rangeRestrict_surjective
  have hu : (U : Subgroup f.range) = ⊤ :=
    (U.is_maximal' ((ho.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  have hm : (S : Subgroup F.H).map f.rangeRestrict = ⊤ := hu
  have he := congrArg (Subgroup.comap f.rangeRestrict) hm
  rw [comap_map_eq, MonoidHom.ker_rangeRestrict, hk, comap_top] at he
  have he' := congrArg (Subgroup.map F.H.subtype) he
  rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le C.point_le,
    ← MonoidHom.range_eq_map, range_subtype] at he'
  have hs : (S : Subgroup F.H).map F.H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (F.invariant 1)
  rw [hs] at he'
  exact (sup_comm _ _).trans he'

private theorem binary_model_outer_two {X : Type*} [Group X]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hm : ClassicalGroup.IsPSL X d 2) :
    IsPGroup 2 (MulAut.Outer X) := by
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := hm
  let := Fintype.ofFinite k
  let f : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let e := (e₀.trans (Atlas.fieldEquivPSL d f)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < d))
  exact (BinaryLinear.OuterCyclic.linear_outer_isTwoGroup hd).of_equiv
    (MulAut.outerCongr e).symm

omit [Finite G] in
/-- All three surviving source point models have outer two-groups. -/
theorem point_outer_two_of_local_models (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    IsPGroup 2 (MulAut.Outer (C.K1 ⧸ pCore 2 C.K1)) := by
  rcases hm with ha | hm | hm
  · obtain ⟨e⟩ := ha
    exact alternatingGroup.SevenComponent.outer_two.of_equiv (MulAut.outerCongr e).symm
  · exact binary_model_outer_two (Or.inl rfl) hm
  · exact binary_model_outer_two (Or.inr rfl) hm

/-- The actual Sylow join belongs to Hz once the source quotient centralizer
is controlled and the point quotient has outer two-group. -/
theorem point_join_mem_Hz_of_quotient_centralizer
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (ho : IsPGroup 2 (MulAut.Outer (C.K1 ⧸ pCore 2 C.K1)))
    (hc : pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G)) := by
  let X := C.K1 ⊔ (T : Subgroup G)
  have hXH : X ≤ F.H := sup_le C.point_le (F.invariant 1)
  have hZ : F.Vi 1 ≤ X := ((F.le_seed 1).trans h.chosen.le_sylow).trans le_sup_right
  have hcard : Nat.card (F.Vi 1) = 2 := by
    simpa using F.card 1 (by have := h.rank; omega)
  have hcore : X.pCoreIn 2 ≠ ⊥ := by
    have hp : IsPGroup 2 (F.Vi 1) := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have hle := le_pCoreIn_of_normalizes hp hZ hXH
    intro he
    have hz := le_bot_iff.mp (he ▸ hle)
    rw [hz, card_bot] at hcard
    contradiction
  refine ⟨⟨hcore, ?_⟩, hXH, ?_⟩
  · intro g hg
    rcases hg with hg | hg
    · exact mem_sup_left (C.contains hg)
    · exact mem_sup_right hg
  · intro he
    apply h.flag_escape F earlier.alternatives
    rw [← point_normalizer_decomposition F C ho]
    exact sup_le (sup_le (le_sup_left.trans he) hc) (le_sup_right.trans he)

/-- Controlled quotient centralizers force a strict point-component enlargement. -/
theorem point_residual_lt_of_controlled_quotient
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (ho : IsPGroup 2 (MulAut.Outer (C.K1 ⧸ pCore 2 C.K1)))
    (hc : pointQuotientCentralizer C ≤ normalizer (L : Set G)) :
    F.Li L 1 < C.K1 := by
  have hx := (point_join_mem_Hz_of_quotient_centralizer h earlier F C ho hc).2.2
  refine lt_of_le_of_ne C.contains ?_
  intro he
  apply hx
  rw [← he]
  exact sup_le (((F.Li_le L 1).trans inf_le_left).trans L.le_normalizer)
    (h.sylow_normalizes earlier.structural)

/-- In degree five the surviving source list reduces to PSL₅(2).
A₇ is too small, and a second PSL₄(2) quotient would force equality of the
original nested local components, contradicting the controlled-centralizer escape. -/
theorem five_point_model_of_controlled_quotient
    (h : HigherRankHypothesis K T L V 5) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 5) (C : ComponentGeometry F L)
    (hc : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hm : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2) :
    ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 := by
  have hlt := point_residual_lt_of_controlled_quotient h earlier F C
    (point_outer_two_of_local_models F C hm) hc
  have hb : F.Li L 1 ∈ ChapterA.Section03.localCComponents T :=
    (Components.Li_mem_local h earlier F 1 (Or.inl ⟨rfl,by decide,by decide⟩)).1
  have hd : C.K1 ∈ ChapterA.Section03.localCComponents T :=
    C.component.subgroupOf_of_le le_sup_left (sup_le C.point_le (F.invariant 1))
  have hbm : ClassicalGroup.IsPSL (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) 4 2 :=
    Components.Li_core_model h F 1 (Or.inl ⟨rfl,by decide,by decide⟩)
  have hbcard := ChapterA.Section03.SourceEmbeddings.AlternatingEight.model_card hbm
  have hcard : ¬ Nat.card (C.K1 ⧸ pCore 2 C.K1) ≤ 20160 := by
    intro hle
    apply hlt.ne
    exact ChapterA.Section03.SourceEmbeddings.BinaryNested.local_eq_of_twoCore_card_le
      T hb hd C.contains (hbcard.symm ▸ hle)
  rcases hm with ha | ha | ha
  · obtain ⟨e⟩ := ha
    have hka : Nat.card (C.K1 ⧸ pCore 2 C.K1) = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    exact (hcard (by rw [hka]; decide)).elim
  · exact (hcard (ChapterA.Section03.SourceEmbeddings.AlternatingEight.model_card ha).le).elim
  · exact ha

/-- Apply the decomposition to the original LocalControl consumer. Its
Hz clause is now derived; the missing source centralizer, model, movement
and plane-centralizer assertions remain with qt-d-1291-natural-source. -/
theorem localControl_of_plane_centralizer_and_models
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hmove : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  ⟨hcentral, point_join_mem_Hz_of_quotient_centralizer h earlier F C
    (point_outer_two_of_local_models F C hmodels) hcentral,
    hmodels, hmove, flag_normalizers_of_plane_centralizer h earlier F hplane⟩

/-- The actual LocalControl application retains only the binary five-space
point model when the original natural seed has dimension five. -/
theorem five_point_model_of_localControl
    (h : HigherRankHypothesis K T L V 5) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 5) (C : ComponentGeometry F L) (control : LocalControl C) :
    ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2 :=
  five_point_model_of_controlled_quotient h earlier F C control.quotient_centralizer control.models

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
