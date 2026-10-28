module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryEmbedding
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import Theory.SpecificGroups.Triality.BinaryMovedElementary
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.SpecificGroups.Classical.EvenDerivedThree

/-!
# Rank-two carrier comparison for the proper unitary image

The centerless natural image of K = O²(H) in J/O₂(J) embeds in the
literal central quotient. The image retains its full two-core of order
q², its fully moved action, and normalization by the original full Sylow.
The rank-two alternatives supplied by Theorem C now reduce to PSL₃(q).

The symplectic local cores have order q³, the G₂ cores were already excluded,
and the triality and Ree cores have still larger orders. Their actual
rank-one quotient isomorphisms identify the relevant field orders. The
binary triality endpoint is excluded by its moved-elementary bound; the
small derived symplectic and G₂ carriers and Tits are excluded by their
solvable proper Sylow overgroups. In the surviving linear row the same
quotient comparison identifies its field with the original q = 2^m;
PSL₃(2) is excluded by the order of the original core.

The companion applies this result to the literal Chapter12 overcomponent.
The six sporadic central quotients remain, as do lifting the linear central
quotient to the full quotient, its natural action, and the second-parabolic
contradiction. This is not unitary maximality or ambient recognition.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653, using A.3.12,
printed pp.47–48 (`refs/quasithin.pdf`). Imported ATLAS constructions retain
LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryRankTwo
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

private structure SectionData (S : Sylow 2 G) (B : Subgroup G) (m : ℕ) : Prop where
  local_mem : B ∈ localCComponents S
  proper : B ≠ ⊤
  psl : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^m)
  card : Nat.card (pCore 2 B) = (2^m)^2
  elementary : IsElementaryAbelian 2 (pCore 2 B)
  moved : pCore 2 B = ChapterC.blockU B
  normalized : (S : Subgroup G) ≤ normalizer (B : Set G)

private theorem SectionData.map {S : Sylow 2 G} {B : Subgroup G} {m : ℕ}
    (d : SectionData S B m) {X : Type*} [Group X] [Finite X] (e : G ≃* X) :
    SectionData (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom) m := by
  let a := B.equivMapOfInjective e.toMonoidHom e.injective
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let ac := (a.subgroupMap (pCore 2 B)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  refine ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker d.local_mem e.toMonoidHom,
    ?_,?_,?_,?_,?_,(map_mono d.normalized).trans (le_normalizer_map e.toMonoidHom)⟩
  · intro ht
    apply d.proper
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [ht,map_top_of_surjective _ e.surjective]
  · obtain ⟨F,_,_,hF,⟨b⟩⟩ := d.psl
    exact ⟨F,inferInstance,inferInstance,hF,⟨aq.symm.trans b⟩⟩
  · exact (Nat.card_congr ac.symm.toEquiv).trans d.card
  · let := d.elementary
    exact IsElementaryAbelian.of_injective ac.symm.toMonoidHom ac.symm.injective
  · have hh := congrArg (Subgroup.map a.toMonoidHom) d.moved
    simpa only [ChapterC.blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective a.toMonoidHom a.surjective] using hh

private theorem field_card_eq {X : Type*} [Group X] [Finite X]
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    (hm : ClassicalGroup.IsPSL X 2 (2^m)) (e : X ≃* PSL(2,F)) :
    2^m = Nat.card F := by
  obtain ⟨K,_,_,hK,⟨b⟩⟩ := hm
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  exact hK.symm.trans (binary_psl_field_card_eq (b.symm.trans e))

private theorem core_separation {X : Type*} [Group X] [Finite X]
    {F : Type*} [Field F] [Finite F] [CharP F 2] {m a : ℕ}
    (ha : a ≠ 2) (hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^m))
    (hc : Nat.card (pCore 2 X) = (2^m)^2)
    (e : (X ⧸ pCore 2 X) ≃* PSL(2,F))
    (hcard : Nat.card (pCore 2 X) = Nat.card F ^ a) : False := by
  rw [field_card_eq hm e] at hc
  exact ha (Nat.pow_right_injective (Finite.one_lt_card (α := F)) (hcard.symm.trans hc))

open Theory.SpecificGroups.SymplecticFour in
private theorem point_core_card {F : Type*} [Field F] [Finite F] [CharP F 2] :
    Nat.card (pointRadical (F := F)) = Nat.card F ^ 3 := by
  let f : F × F × F → pointRadical (F := F) := fun x =>
    ⟨pointRadicalElement x.1 x.2.1 x.2.2,pointRadicalElement_mem _ _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hh
      have he := (pointRadicalElement_eq_iff _ _ _ _ _ _).mp (congrArg Subtype.val hh)
      exact Prod.ext he.1 (Prod.ext he.2.1 he.2.2)
    · intro x
      refine ⟨(x.val.val.val (.inl 1) (.inr 0),
        x.val.val.val (.inr 1) (.inr 0),x.val.val.val (.inl 0) (.inr 0)),?_⟩
      exact Subtype.ext (pointRadical_eq_element x.val x.property).symm
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_prod,Nat.card_prod]
  ring

private theorem not_symplectic {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2^f) (hf : 1 < f)
    {S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F)}
    {B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)} {m : ℕ}
    (d : SectionData S B m) : False := by
  open Theory.SpecificGroups.SymplecticFour in
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement hF hf S B d.local_mem d.proper
  have dd := d.map (MulAut.conj g)
  rcases hg with hg | hg
  · rw [hg] at dd
    apply core_separation (by decide : 3 ≠ 2) dd.psl dd.card
      ((Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hf).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)))
    rw [Theory.SpecificGroups.SymplecticFour.pointLocal_core_eq hF hf]
    exact point_core_card
  · rw [hg] at dd
    apply core_separation (by decide : 3 ≠ 2) dd.psl dd.card
      ((Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hf).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)))
    rw [Theory.SpecificGroups.SymplecticFour.planeLocal_core_eq hF hf]
    exact Theory.SpecificGroups.SymplecticFour.EvenTwoRank.card_plane_radical

private theorem not_symplectic_containing {S : Sylow 2 G} {B : Subgroup G} {m f : ℕ}
    (d : SectionData S B m) (hf : 2 ≤ f) (h : ClassicalGroup.IsPSp G 2 (2^f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact not_symplectic hF hf (d.map
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm))

omit [Finite G] in
private theorem core_ne_bot {S : Sylow 2 G} {B : Subgroup G} {m : ℕ}
    (d : SectionData S B m) (hm : 1 < m) : pCore 2 B ≠ ⊥ := by
  intro he
  have hh := d.card
  rw [he,card_bot] at hh
  have hp : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hm
  nlinarith

private theorem not_triality {f : ℕ} (hf : 0 < f)
    {S : Sylow 2 (_root_.Triality.Standard.BinaryCarrier f hf)}
    {B : Subgroup (_root_.Triality.Standard.BinaryCarrier f hf)} {m : ℕ}
    (hm : 1 < m) (d : SectionData S B m) : False := by
  by_cases hf1 : f = 1
  · subst f
    let E := B.pCoreIn 2
    let := d.elementary
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map B.subtype
    let := d.local_mem.perfect
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
    have hns : ¬ Group.IsSolvable B := by
      intro hh
      let := hh
      exact d.local_mem.not_isSolvable
        (Group.isSolvable_of_isSolvable_injective
          (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left)).toMonoidHom)
          (subgroupOfEquivOfLe le_sup_left).injective)
    have hne : E ≠ ⊥ := fun hh => core_ne_bot d hm
      ((map_eq_bot_iff_of_injective (pCore 2 B) B.subtype_injective).mp hh)
    have hmov : ⁅E,B⁆ = E := by
      have hh := congrArg (Subgroup.map B.subtype) d.moved.symm
      simpa only [E,pCoreIn,ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
    exact _root_.Triality.Standard.BinaryLocalSections.no_moved_elementary (MulEquiv.refl _)
      S B E d.proper hns d.normalized (B.pCoreIn_le 2) hne hmov
  · have hq : 2 < 2^f := lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨g,a,hg⟩ := FiveLocalFF.Triality.local_placement f hf hq S B d.local_mem (core_ne_bot d hm)
    have dd := d.map (MulAut.conj g)
    rw [hg] at dd
    cases a with
    | central =>
      apply core_separation (by decide : 11 ≠ 2) dd.psl dd.card
        (_root_.Triality.Standard.Parabolics.localFactorCentralQuotientEquivPSL2 _ rfl)
      rw [_root_.Triality.Standard.Parabolics.localFactor_central_twoCore_card _ rfl,
        _root_.Triality.Standard.card_baseField]
    | arms =>
      have he := field_card_eq dd.psl
        (_root_.Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2 _ rfl)
      rw [_root_.Triality.Standard.card_extensionField] at he
      have hc := dd.card
      rw [_root_.Triality.Standard.Parabolics.localFactor_arms_twoCore_card _ rfl,he,←pow_mul] at hc
      have hh := Nat.pow_right_injective (by omega : 1 < (2^f)) hc
      norm_num at hh

private theorem not_triality_containing {S : Sylow 2 G} {B : Subgroup G} {m f : ℕ}
    (d : SectionData S B m) (hm : 1 < m) (hf : 1 ≤ f)
    (h : _root_.Triality.Standard.IsTrialityGroupAt (2^f) G) : False := by
  obtain ⟨e⟩ := (_root_.Triality.Standard.isTrialityGroupAt_binary_iff G f hf).mp h
  exact not_triality hf hm (d.map e)

private theorem three_dvd_psl {X : Type*} [Group X] [Finite X] {m : ℕ}
    (h : ClassicalGroup.IsPSL X 2 (2^m)) : 3 ∣ Nat.card X := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rw [Nat.card_congr e.toEquiv]
  exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (by decide : (0 : Fin 2) ≠ 1)).trans (commutator PSL(2,F)).card_subgroup_dvd_card

private theorem not_ree {r : ℕ} (hr : 1 ≤ r)
    (htop : (⊤ : Subgroup (ReeF4.Model r)).IsCComponent)
    {S : Sylow 2 (ReeF4.Model r)} {B : Subgroup (ReeF4.Model r)} {m : ℕ}
    (d : SectionData S B m) : False := by
  obtain ⟨g,s,hg⟩ := ReeLocal.local_placement hr htop S B d.local_mem d.proper
  have dd := d.map (MulAut.conj g)
  rw [hg] at dd
  cases s with
  | linear =>
    apply core_separation (by decide : 11 ≠ 2) dd.psl dd.card
      (ReeF4.Parabolics.linearLocalQuotientEquiv r)
    rw [ReeF4.Parabolics.card_local_pCore_linear]
    rw [ReeF4.field_card]
  | suzuki =>
    have h3 := three_dvd_psl dd.psl
    rw [Nat.card_congr (ReeF4.Parabolics.suzukiLocalQuotientEquiv r).toEquiv] at h3
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free r hr h3


private theorem not_solvable_overgroups [IsQuasisimple G]
    {S : Sylow 2 G} {B : Subgroup G} {m : ℕ}
    (d : SectionData S B m) (h : SolvableSylowOvergroups G) : False := by
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact d.proper (eq_of_solvable_sylow_overgroups S d.local_mem ht le_top
    (SolvableSylowOvergroups.of_equiv topEquiv h))

private theorem linear_field_eq {S : Sylow 2 G} {B : Subgroup G} {m f : ℕ}
    (d : SectionData S B m) (hm : 1 < m) (hf : 1 ≤ f)
    (h : ClassicalGroup.IsPSL G 3 (2^f)) : f = m := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hf' : 1 < f := by
    by_contra! hsmall
    have heq : f = 1 := by omega
    subst f
    let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod,pow_one] using hF)
    let a := ((e.trans (Atlas.fieldEquivPSL 3 k)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3))).trans
      (BinaryLinear.OuterCyclic.matrixEquivLinear 3).symm
    have hcard : Nat.card G = 168 := by
      rw [Nat.card_congr a.toEquiv,Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    have hd : 16 ∣ Nat.card (pCore 2 B) := by
      rw [d.card,←pow_mul]
      exact Nat.pow_dvd_pow 2 (by omega : 4 ≤ m*2)
    have hh := hd.trans ((pCore 2 B).card_subgroup_dvd_card.trans B.card_subgroup_dvd_card)
    rw [hcard] at hh
    norm_num at hh
  have dd := d.map e
  obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hf'
    _ _ dd.local_mem dd.proper
  have dc := dd.map (MulAut.conj g)
  have heq : 2^m = Nat.card F := by
    rcases hg with hg | hg
    · rw [hg] at dc
      exact field_card_eq dc.psl ((Matrix.PSL3.LinearThree.pointLocalCoreQuotientEquiv F).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)))
    · rw [hg] at dc
      exact field_card_eq dc.psl ((Matrix.PSL3.LinearThree.lineLocalCoreQuotientEquiv F).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)))
  exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) (hF.symm.trans heq.symm)

/-- The remaining central quotient is linear over the original field, or one
of the six retained sporadic carriers. Every alternative has an actual isomorphism. -/
@[expose] def LinearOrSporadic (X : Type*) [Group X] (m : ℕ) : Prop :=
  ClassicalGroup.IsPSL X 3 (2^m) ∨
    ∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .he ∨ name = .ru) ∧ Nonempty (X ≃* name.Carrier)

private theorem sieve [IsQuasisimple G]
    {S : Sylow 2 G} {B : Subgroup G} {m : ℕ}
    (d : SectionData S B m) (hm : 1 < m)
    (hmodels : UnitaryEmbedding.RemainingModels G) : LinearOrSporadic G m := by
  rcases hmodels.1 with ⟨f,hf⟩ | hs
  · cases hf with
    | linear hf he =>
      have hfm := linear_field_eq d hm hf he
      subst f
      exact .inl he
    | symplectic hf he => exact (not_symplectic_containing d hf he).elim
    | g2 hf he => exact (hmodels.2 ⟨f,hf,he⟩).elim
    | triality hf he => exact (not_triality_containing d hm hf he).elim
    | ree_f4 r hr _ he =>
      let e := he.some
      let : IsQuasisimple (ReeF4.Model r) := IsQuasisimple.of_mulEquiv e
      have ht : (⊤ : Subgroup (ReeF4.Model r)).IsCComponent :=
        (show IsComponent (ReeF4.Model r) ⊤ from
          ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
      exact (not_ree hr ht (d.map e)).elim
    | symplectic_derived _ he =>
      exact (FiveLocalFF.AlternatingSmall.not_proper_six S B d.local_mem d.proper
        (he.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
    | g2_derived _ he =>
      exact (not_solvable_overgroups d (SolvableSylowOvergroups.of_equiv he.some
        Atlas.G2.binaryDerived_solvableSylowOvergroups)).elim
    | tits _ he =>
      exact (not_solvable_overgroups d (SolvableSylowOvergroups.of_equiv he.some
        Tits.ProperSylowOvergroups.solvableSylowOvergroups)).elim
  · exact .inr hs

/-- Apply the carrier comparison to the literal central quotient of the
centerless natural image; the full core, its action and full Sylow survive. -/
theorem center_quotient_linear_or_sporadic [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) (hproper : B ≠ ⊤)
    {m : ℕ} (hb : ChapterC.IsL2EvenBlock B m)
    (hel : IsElementaryAbelian 2 (pCore 2 B))
    (hc : Nat.card (pCore 2 B) = (2^m)^2)
    (hmove : pCore 2 B = ChapterC.blockU B) (hz : center B = ⊥)
    (hmodels : UnitaryEmbedding.RemainingModels (G ⧸ center G)) :
    LinearOrSporadic (G ⧸ center G) m := by
  let q := QuotientGroup.mk' (center G)
  let f := q.comp B.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxz : (x : G) ∈ center G := (QuotientGroup.eq_one_iff _).mp hx
    have hxb : x ∈ center B := mem_center_iff.mpr (fun y =>
      Subtype.ext (mem_center_iff.mp hxz y))
    simpa only [hz,mem_bot] using hxb
  let e : B ≃* B.map q := MulEquiv.ofBijective (q.subgroupMap B)
    ⟨fun x y hh => hf (congrArg Subtype.val hh),q.subgroupMap_surjective B⟩
  let SB := S.mapSurjective (QuotientGroup.mk'_surjective (center G))
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  have hlocal : B.map q ∈ localCComponents SB :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB q
  have hne : B.map q ≠ ⊤ := by
    intro hh
    apply hproper
    apply eq_top_of_sup_center_eq_top B
    have hcomap := congrArg (Subgroup.comap q) hh
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hcomap
  have hbq := ChapterC.IsL2EvenBlock.of_mulEquiv hb e
  obtain ⟨F,_,_,hF,hpsl,_⟩ := hbq.2.2
  let ecore := (e.subgroupMap (pCore 2 B)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hcore : IsElementaryAbelian 2 (pCore 2 (B.map q)) := by
    let := hel
    exact IsElementaryAbelian.of_injective ecore.symm.toMonoidHom ecore.symm.injective
  have hmq : pCore 2 (B.map q) = ChapterC.blockU (B.map q) := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hmove
    simpa only [ChapterC.blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective e.toMonoidHom e.surjective] using hh
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsQuasisimple (G ⧸ center G) := IsQuasisimple.of_surjective q
    (QuotientGroup.mk'_surjective (center G))
  exact sieve ⟨hlocal,hne,hpsl,(Nat.card_congr ecore.symm.toEquiv).trans hc,hcore,hmq,
    (map_mono hSB).trans (le_normalizer_map q)⟩ hb.1 hmodels

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryRankTwo

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- Every rank-two central quotient of the actual proper unitary
 overcomponent is PSL₃ over the original field. The six sporadic alternatives
 remain explicit; no identification of the full quotient is assumed. -/
theorem Preparation.unitary_overcomponent_central_quotient_linear_or_sporadic
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    UnitaryRankTwo.LinearOrSporadic
      ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) m := by
  obtain ⟨hq,hmodels⟩ :=
    d.unitary_overcomponent_central_quotient_models h hH hp m hm he hJ hKJ hQR
  let := hq
  obtain ⟨_,_,hproper,S,_,hlocal,hnorm⟩ :=
    d.unitary_overcomponent_embedding_context h hH hp m hm he hJ hKJ
  obtain ⟨hb,hmove,hcenter⟩ :=
    d.unitary_overcomponent_proper_image_block h hH hp m hm he hJ hKJ.le hQR
  have hel := (d.unitary_overcomponent_quotient_image h hH hp m hm he hJ hKJ.le).2.2.1
  have hc := (d.unitary_overcomponent_proper_quotient_core h hH hp m hm he hJ hKJ.le hQR).1
  exact UnitaryRankTwo.center_quotient_linear_or_sporadic
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))) _
    hlocal hnorm hproper hb hel hc hmove hcenter hmodels

end Unitary

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
