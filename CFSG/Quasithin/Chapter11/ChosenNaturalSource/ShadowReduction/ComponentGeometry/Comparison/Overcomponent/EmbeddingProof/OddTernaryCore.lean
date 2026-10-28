module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddTernaryPairs
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionCovers
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer

/-!
# Faithful point quotients in odd ternary overcomponents

The original seed forces the ternary prime to be five. If the actual point
image in J/O₂(J) has nontrivial two-core, its normalized perfect subgroup
centralizes an involution. The signed ternary cubic cover embeds that subgroup
in SL₂(5), so its own two-core quotient is A₅. This contradicts the strict
seed--point chain. Thus the point image has trivial two-core, and the original
point quotient embeds faithfully through the literal containing projection.

A centralizing involution would give the same SL₂(5) contradiction. Hence the
full quotient Sylow acts faithfully on this image. The chosen-flag application
constructs both actions, retaining their quotient and conjugation formulas.
Both special and projective carriers, and both signs, are retained.

Classification of the remaining core-free quasisimple point image and the
other proper pairs remain with qt-d-1222-shadow-component-comparison, together
with inner placement, strict omega-center containment and the final equality.
Earlier geometry and the seed marking retain final discharge by
qt-d-1222-shadow-components. This module does not assert full 11.4.2.
Source: Aschbacher--Smith A.3.21, pp.55--56, and 11.4.2, pp.776--777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels

private theorem odd_ternary_five_involution_model
    {A : Type*} [Group A] [Finite A] (C : Subgroup A)
    [Group.IsPerfect C] [Nontrivial C] (u : Bool)
    (hm : IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5)
    (z : A) (hz : orderOf z = 2) (hzC : C ≤ centralizer ({z} : Set A)) :
    Nonempty (C ≃* SL(2,ZMod 5)) ∧ IsAlternating (C ⧸ pCore 2 C) 5 := by
  obtain ⟨r,H,_,_,hH,f,hf,hker,hcube⟩ := odd_three_cubic_carrier (by decide : Odd 5) u hm
  obtain ⟨i,hi⟩ := rankThree_cubic_quotient_perfect_embedding hH f hf hker hcube z hz C
    hzC
  let a : C ≃* i.range := MonoidHom.ofInjective hi
  let : Group.IsPerfect i.range := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Nontrivial i.range := a.symm.nontrivial
  have he : Nonempty (C ≃* SL(2,ZMod 5)) := by
    rcases ChapterA.RankActions.primePerfectSL2Recognition 5 (by decide) i.range
        inferInstance inferInstance with hfull | hsmall
    · exact ⟨a.trans hfull.some⟩
    · exact ⟨a.trans hsmall.2.some⟩
  obtain ⟨e⟩ := he
  have hk : IsPGroup 2 e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    exact IsPGroup.of_bot
  let b := Theory.PSL2.primeSL2CoverCoreEquiv (by decide : 3 < 5)
    e.toMonoidHom e.surjective hk
  exact ⟨⟨e⟩,⟨b.trans Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩⟩

/-- At prime five, a nontrivial two-core in the normalized local image
forces the actual binary cover SL₂(5), in either signed ternary carrier. -/
theorem odd_ternary_five_core_model
    {A : Type*} [Group A] [Finite A]
    (P : Sylow 2 A) (C : Subgroup A) (hC : C ∈ localCComponents P)
    (hPC : (P : Subgroup A) ≤ normalizer (C : Set A))
    (hc : pCore 2 C ≠ ⊥) (u : Bool)
    (hm : IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5) :
    Nonempty (C ≃* SL(2,ZMod 5)) ∧ IsAlternating (C ⧸ pCore 2 C) 5 := by
  let := hC.perfect
  let c := subgroupOfEquivOfLe (show C ≤ C ⊔ (P : Subgroup A) from le_sup_left)
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := c.toMonoidHom) c.surjective
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr (by
    intro he
    subst C
    exact hc (Subsingleton.elim _ _))
  obtain ⟨z,_,hz,hzC⟩ := exists_involution_centralized_by_perfect_sup_sylow P C
    (odd_three_two_rank (by decide : Odd 5) u hm) hPC hc
  exact odd_ternary_five_involution_model C u hm z hz (le_sup_left.trans hzC)

/-- A perfect core-free subgroup in the same quintic carrier has no
centralizing involution. Hence every ambient Sylow acts faithfully whenever
it normalizes this subgroup. -/
theorem odd_ternary_five_core_free_sylow_centralizer
    {A : Type*} [Group A] [Finite A]
    (P : Sylow 2 A) (C : Subgroup A) [Group.IsPerfect C] [Nontrivial C]
    (hc : pCore 2 C = ⊥) (u : Bool)
    (hm : IsPSLSign A u 3 5 ∨ IsSLSign A u 3 5) :
    (P : Subgroup A) ⊓ centralizer (C : Set A) = ⊥ := by
  apply AlternatingFive.sylow_centralizer_eq_bot_of_no_involution P C
  intro z hzC hz
  obtain ⟨⟨e⟩,⟨a⟩⟩ := odd_ternary_five_involution_model C u hm z hz
    (fun x hx => mem_centralizer_singleton_iff.mpr (hzC x hx))
  let b := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans a
  have hh := Nat.card_congr (e.symm.trans b).toEquiv
  rw [GorensteinWalter.sl2_card_formula,Nat.card_zmod,nat_card_alternatingGroup] at hh
  norm_num [Nat.factorial] at hh

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- The literal image of a subgroup in the containing two-core quotient. -/
def pointQuotientImage (B J : Subgroup G) : Subgroup (J ⧸ pCore 2 J) :=
  (B.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))

private theorem pointQuotientImage_local_setup {B₀ J : Subgroup G}
    (hB₀ : B₀ ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B₀ : Set G)) (hle : B₀ ≤ J) :
    ∃ P : Sylow 2 (J ⧸ pCore 2 J),
      pointQuotientImage B₀ J ∈ localCComponents P ∧
      (P : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (pointQuotientImage B₀ J : Set _) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J
    hTJ
  let B := B₀.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hB : B ∈ localCComponents P := by
    rw [hP]
    exact local_restrict hB₀.1 hle
  have hPB : (P : Subgroup J) ≤ normalizer (B : Set J) := by
    rw [hP,←subgroupOf_normalizer_eq hle]
    exact comap_mono hTB
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let C := B.map q
  let := pCore_isNilpotent (p := 2) (G := J)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  have hC : C ∈ localCComponents Q :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB q
  have hQC : (Q : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (C : Set _) :=
    (map_mono hPB).trans (B.le_normalizer_map q)
  exact ⟨Q,hC,hQC⟩

/-- A strict seed--point chain forces the actual point image in a signed
ternary quotient at prime five to have trivial two-core. -/
theorem odd_ternary_five_point_image_core
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hseed : E.L₁ ∈ Chapter1.L G (T : Subgroup G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hle : E.Kz ≤ J) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 5 ∨ IsSLSign (J ⧸ pCore 2 J) u 3 5) :
    pCore 2 (pointQuotientImage E.Kz J) = ⊥ := by
  obtain ⟨Q,hC,hQC⟩ := pointQuotientImage_local_setup h.point_mem_local_family
    (sylow_normalizes_overcomponent h hJ hle) (sylow_normalizes_point h) hle
  let B := E.Kz.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let C := B.map q
  change pCore 2 C = ⊥
  by_contra hc
  obtain ⟨_,⟨a⟩⟩ := odd_ternary_five_core_model Q C hC hQC hc u hm
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := subgroupOfEquivOfLe hle
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let d := (q.subgroupMap B).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective B) hk
  have hs : SolvableSylowOvergroups (E.Kz ⧸ pCore 2 E.Kz) :=
    SolvableSylowOvergroups.of_equiv (bq.symm.trans (d.trans a))
      (fun _ U _ hU => alternatingGroup.isSolvable_subgroup_five_of_ne_top U hU)
  exact (h.strict_comparison hf hne).2.1.ne
    (local_eq_of_quotient_sylow_solvable hseed h.point_mem_local_family
      (sylow_normalizes_point h) (le_conjugateSpanBy _ _) hs)

/-- Removing the intrinsic core of the actual image gives a faithful
embedding of the original point quotient, preserving the literal projection. -/
theorem point_core_embedding_of_image_core {B J : Subgroup G} (hle : B ≤ J)
    (hc : pCore 2 (pointQuotientImage B J) = ⊥) :
    ∃ i : (B ⧸ pCore 2 B) →* (J ⧸ pCore 2 J), Function.Injective i ∧
      ∀ b : B, i (QuotientGroup.mk' (pCore 2 B) b) =
        QuotientGroup.mk' (pCore 2 J) ⟨b,hle b.property⟩ := by
  let C := B.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let b := (subgroupOfEquivOfLe hle).symm
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let d := (q.subgroupMap C).quotientPCoreEquivOfSurjective (q.subgroupMap_surjective C) hk
  let a := bq.trans (d.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot))
  refine ⟨(pointQuotientImage B J).subtype.comp a.toMonoidHom,
    (pointQuotientImage B J).subtype_injective.comp a.injective,?_⟩
  intro x
  change (pointQuotientImage B J).subtype (QuotientGroup.quotientBot
    (QuotientGroup.quotientMulEquivOfEq hc (d (bq (QuotientGroup.mk' (pCore 2 B) x))))) = _
  rw [show bq (QuotientGroup.mk' (pCore 2 B) x) =
    QuotientGroup.mk' (pCore 2 C) (b x) from QuotientGroup.congr_mk' _ _ b _ x]
  rw [show d (QuotientGroup.mk' (pCore 2 C) (b x)) =
    QuotientGroup.mk' (pCore 2 (C.map q)) (q.subgroupMap C (b x)) from
      MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ _]
  rfl

/-- On the original chosen flag both signed ternary coverings force prime
five, a core-free point image and a faithful embedding of its literal quotient. -/
theorem ofFlag_odd_ternary_faithful_point_quotient
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hle : (ofFlag S f X z H).Kz ≤ J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    p = 5 ∧ pCore 2 (pointQuotientImage (ofFlag S f X z H).Kz J) = ⊥ ∧
      (∃ i : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) →*
          (J ⧸ pCore 2 J), Function.Injective i ∧
        ∀ b : (ofFlag S f X z H).Kz,
          i (QuotientGroup.mk' (pCore 2 (ofFlag S f X z H).Kz) b) =
            QuotientGroup.mk' (pCore 2 J) ⟨b,hle b.property⟩) ∧
      ∃ P : Sylow 2 (J ⧸ pCore 2 J),
        pointQuotientImage (ofFlag S f X z H).Kz J ∈ localCComponents P ∧
        ∃ hn : (P : Subgroup (J ⧸ pCore 2 J)) ≤
            normalizer (pointQuotientImage (ofFlag S f X z H).Kz J : Set _),
          Function.Injective ((pointQuotientImage (ofFlag S f X z H).Kz J).normalizerMonoidHom.comp
            (inclusion hn)) := by
  have hs : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have hseed := LocalGeometry.Components.flag_mem_local_of_model D S f 0 hs
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) (J ⊔ (T : Subgroup G)) :=
    ⟨T.subtype le_sup_right,by
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]⟩
  have hp5 := (LocalGeometry.Components.Embedding.relative_odd_ternary_parameters hP
    hseed (show Source.ComponentIn (J ⊔ (T : Subgroup G)) J from ⟨le_sup_left,hJ.1⟩)
    ((le_conjugateSpanBy _ _).trans hle) (f.sylow_normalizes_Li 0)
    S.nonbinary hs hp ho u hm).2
  subst p
  have hc := odd_ternary_five_point_image_core h
    (fixed_and_transitive D S _ hlinear h1132).1 hne hseed hJ hle u hm
  obtain ⟨P,hC,hPC⟩ := pointQuotientImage_local_setup h.point_mem_local_family
    (sylow_normalizes_overcomponent h hJ hle) (sylow_normalizes_point h) hle
  let C := pointQuotientImage (ofFlag S f X z H).Kz J
  let b := subgroupOfEquivOfLe (show C ≤ C ⊔ (P : Subgroup _) from le_sup_left)
  let := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  let : Nontrivial (C.subgroupOf (C ⊔ (P : Subgroup _))) :=
    (nontrivial_iff_ne_bot _).mpr hC.ne_bot
  let : Nontrivial C := b.injective.nontrivial
  have hz := odd_ternary_five_core_free_sylow_centralizer P C hc u hm
  refine ⟨rfl,hc,point_core_embedding_of_image_core hle hc,P,hC,hPC,?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply Subtype.ext
  apply mem_bot.mp
  rw [←hz]
  refine ⟨x.property,?_⟩
  change inclusion hPC x ∈ C.normalizerMonoidHom.ker at hx
  rwa [normalizerMonoidHom_ker] at hx

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
