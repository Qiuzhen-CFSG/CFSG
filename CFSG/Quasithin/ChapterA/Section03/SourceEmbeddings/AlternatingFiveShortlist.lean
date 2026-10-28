module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveEvenModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveSporadicModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveOddModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveRankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalCoverTernaryQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinear
public import CFSG.Quasithin.MainConverse.AlternatingLocal.EightNineEven.Eight
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# The actual A₅ overcomponent shortlist

A proper local A₅ normalized by a full Sylow can lie in a quasisimple
SQTK container only in A₇, its triple cover, J₁, PSL₂(25), or the exceptional
prime PSL₂ rows. The even-characteristic and odd ternary rows are excluded
by faithful Sylow actions. The literal central quotient preserves the local
A₅, so the same exclusions handle all classical and Mathieu triple covers.

Source: Aschbacher--Smith A.3.14(3), pp.49--50; the contained-layer branch
of10.2.1, p.743. The surviving natural-module branch is not asserted here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Literal carrier alternatives; the alternating cover is the central triple cover. -/
def Shortlist (H : Type*) [Group H] : Prop :=
  IsAlternating H 7 ∨ IsAlternatingCover H 7 ∨ Nonempty (H ≃* Janko1.Model) ∨
    ClassicalGroup.IsPSL H 2 25 ∨ ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL H 2 p

private theorem five_quasisimple (S : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ localCComponents S) (e : B ≃* alternatingGroup (Fin 5)) :
    IsQuasisimple B ∧ center B = ⊥ ∧ pCore 2 B = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := e.isSimpleGroup
  let eB : B.subgroupOf (B ⊔ (S : Subgroup G)) ≃* B := subgroupOfEquivOfLe le_sup_left
  let := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.toMonoidHom) eB.surjective
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  have ho : pCore 2 B = ⊥ := by
    apply (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    let : Group.IsNilpotent (⊤ : Subgroup B) := ht ▸ pCore_isNilpotent (p := 2) (G := B)
    let : Group.IsSolvable B := Group.isSolvable_of_surjective
      (f := (topEquiv (G := B)).toMonoidHom) (topEquiv (G := B)).surjective
    exact Group.IsPerfect.not_isSolvable B inferInstance
  exact ⟨⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩,hz,ho⟩

omit [Finite G] in
private theorem top_component [IsQuasisimple G] : (⊤ : Subgroup G).IsCComponent :=
  (show IsComponent G ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent

private theorem not_eight (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (eB : B ≃* alternatingGroup (Fin 5))
    (e : G ≃* alternatingGroup (Fin 8)) : False := by
  apply not_sixteen_dvd_of_evenCharacteristic S
    ((MainConverse.evenCharacteristic_of_model_equiv e
      MainConverse.alternatingEight_evenCharacteristic) S) hB hSB eB
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The simple carrier list reduces to the genuine A₅ alternatives. -/
theorem shortlist_of_theoremC [IsQuasisimple G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) (hne : B ≠ ⊤) (hm : TheoremCModel G) :
    Shortlist G := by
  obtain ⟨hqB,hzB,hoB⟩ := five_quasisimple S hB eB
  let := hqB
  have htop := top_component (G := G)
  cases hm with
  | alternating n hn hm =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn' with rfl | rfl | rfl | rfl
    · exact (hne (eq_of_small_alternating_containing_component S hB htop le_top
        (.inl (hm.map fun e => topEquiv.trans e)))).elim
    · exact (not_six S hB eB hm.some).elim
    · exact .inl hm
    · exact (not_eight S hB hSB eB hm.some).elim
  | linear_odd p k hp ho hk _ hm =>
    rcases hk with rfl | rfl
    · have hm' : ClassicalGroup.IsPSL G 2 p := by simpa only [pow_one] using hm
      exact .inr (.inr (.inr (.inr ⟨p,
        (proper_primePSL2_models S hB htop le_top hne hp ho (hm'.of_mulEquiv topEquiv)).1,hm'⟩)))
    · have hsection : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :=
        ⟨((QuotientGroup.quotientMulEquivOfEq hoB).trans QuotientGroup.quotientBot).trans eB⟩
      have hp5 := (proper_quadraticPSL2_five_models S hB htop le_top hne hp ho
        (hm.of_mulEquiv topEquiv) hsection).1
      subst p
      exact .inr (.inr (.inr (.inl hm)))
  | three_odd p hp ho unitary hm => exact (not_three_odd S hB hSB eB hp ho unitary hm).elim
  | rank_one hm =>
    exact (hne (eq_of_bender_containing_component S hB htop le_top
      (hm.of_mulEquiv topEquiv))).elim
  | rank_two hm => exact (not_rankTwo S hB hSB eB hm).elim
  | binary_linear n hn hm =>
    exact (hne (eq_of_binary_linear_four_or_five S hB htop le_top hn
      (hm.of_mulEquiv topEquiv))).elim
  | sporadic name hn hm => exact (not_sporadic S hB hSB eB name hn hm).elim
  | janko_one hm => exact .inr (.inr (.inl hm))

private theorem center_image_five [IsQuasisimple G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) (hne : B ≠ ⊤) :
    let q := QuotientGroup.mk' (center G)
    let T := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
    B.map q ∈ localCComponents T ∧
    (T : Subgroup (G ⧸ center G)) ≤ normalizer (B.map q : Set _) ∧
    Nonempty (B.map q ≃* alternatingGroup (Fin 5)) ∧ B.map q ≠ ⊤ := by
  intro q T
  obtain ⟨_,hzB,_⟩ := five_quasisimple S hB eB
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (center G)).ker
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  have hi : Function.Injective (q.subgroupMap B) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro b hb
    have hz : (b : G) ∈ center G := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hb))
    have hzb : b ∈ center B := by
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (mem_center_iff.mp hz a)
    simpa only [hzB,mem_bot] using hzb
  refine ⟨localCComponents_map_of_solvable_ker hB q,
    (map_mono hSB).trans (le_normalizer_map q),
    ⟨(MulEquiv.ofBijective (q.subgroupMap B) ⟨hi,q.subgroupMap_surjective B⟩).symm.trans eB⟩,?_⟩
  intro ht
  apply hne
  apply eq_top_of_sup_center_eq_top B
  have hh := congrArg (Subgroup.comap q) ht
  simpa only [Subgroup.comap_map_eq,q,QuotientGroup.ker_mk',Subgroup.comap_top] using hh

/-- The only three-cover container left for a proper normalized local A₅ is 3.A₇. -/
theorem seven_of_threeCover [IsQuasisimple G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) (hne : B ≠ ⊤) (hm : ThreeCoverModel G) :
    IsAlternatingCover G 7 := by
  let q := QuotientGroup.mk' (center G)
  let T := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
  obtain ⟨hl,hn,⟨e⟩,hne'⟩ := center_image_five S hB hSB eB hne
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsQuasisimple (G ⧸ center G) :=
    IsQuasisimple.of_surjective q (QuotientGroup.mk'_surjective _)
  have htop := top_component (G := G ⧸ center G)
  cases hm with
  | classical unitary p hp hm =>
    rcases ClassicalCoverTernaryQuotient.models unitary p hp hm with ⟨p,hp,ho,hm⟩ | hb | ⟨n,hnn,hm⟩
    · rcases hm with hm | hm
      · exact (not_odd_linear T hl hn e hp ho hm).elim
      · exact (not_odd_unitary T hl hn e hp ho hm).elim
    · exact (hne' (eq_of_bender_containing_component T hl htop le_top
        (hb.of_mulEquiv topEquiv))).elim
    · exact (not_rankTwo T hl hn e (.linear n hnn hm)).elim
  | alternating_six hm => exact (not_six T hl e hm.2.2.some).elim
  | alternating_seven hm => exact hm
  | mathieu hm => exact (not_sporadic T hl hn e .m22 (by intro h; cases h) hm.2.2).elim

omit [Finite G] in
/-- Transport the literal shortlist through an actual group equivalence. -/
theorem Shortlist.of_equiv {H : Type*} [Group H] (h : Shortlist H) (e : G ≃* H) :
    Shortlist G := by
  rcases h with h | h | h | h | ⟨p,hp,h⟩
  · exact .inl (h.map fun a => e.trans a)
  · obtain ⟨hq,⟨ez⟩,⟨eq⟩⟩ := h
    let := hq
    let ec : (G ⧸ center G) ≃* (H ⧸ center H) :=
      QuotientGroup.congr (center G) (center H) e (by
        apply le_antisymm
        · rintro _ ⟨x,hx,rfl⟩
          exact (centerCongr e ⟨x,hx⟩).property
        · intro y hy
          exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
    exact .inr (.inl ⟨IsQuasisimple.of_mulEquiv e.symm,
      ⟨(centerCongr e).trans ez⟩,⟨ec.trans eq⟩⟩)
  · exact .inr (.inr (.inl (h.map fun a => e.trans a)))
  · exact .inr (.inr (.inr (.inl (h.of_mulEquiv e))))
  · exact .inr (.inr (.inr (.inr ⟨p,hp,h.of_mulEquiv e⟩)))

/-- The genuine contained-A₅ shortlist follows from the original SQTK
hypothesis, trivial two-core, and the literal proper local embedding. -/
theorem shortlist_knownSimple [IsQuasisimple G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) (hne : B ≠ ⊤) : Shortlist G := by
  let a : G ≃* (⊤ : Subgroup G) := topEquiv.symm
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv a
  let f := a.toMonoidHom
  have hk : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr a.injective
  let : Group.IsSolvable f.ker := hk ▸ inferInstance
  let T := S.mapSurjective (f := f) a.surjective
  have hl : B.map f ∈ localCComponents T := localCComponents_map_of_solvable_ker hB f
  have hn : (T : Subgroup (⊤ : Subgroup G)) ≤ normalizer (B.map f : Set _) :=
    (map_mono hSB).trans (le_normalizer_map f)
  let e : B.map f ≃* alternatingGroup (Fin 5) :=
    (B.equivMapOfInjective f a.injective).symm.trans eB
  have hb : B.map f ≠ ⊤ := by
    intro ht
    apply hne
    have hh := congrArg (Subgroup.comap f) ht
    simpa only [comap_map_eq,hk,sup_bot_eq,comap_top] using hh
  have hs : Shortlist (⊤ : Subgroup G) := by
    rcases quasisimple_containing_component_models_knownSimple hG hO
      (top_component (G := G)) with ⟨_,hm⟩ | ⟨_,hm⟩
    · exact shortlist_of_theoremC T hl hn e hb hm
    · exact .inr (.inl (seven_of_threeCover T hl hn e hb hm))
  exact hs.of_equiv a

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
