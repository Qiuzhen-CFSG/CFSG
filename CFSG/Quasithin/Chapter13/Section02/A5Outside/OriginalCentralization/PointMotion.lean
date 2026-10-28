module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointSourceSections
public import Theory.SpecificGroups.SmallRankTwoPointMotion

/-!
# Local motion on the original complementary-point span

The original complementary point is fixed by the common Baumann Sylow and
moved by both original point groups. For SL₃(2), A₆ and S₆, their parabolic
lattices force its stabilizer in the faithful action quotient to be exactly
the common Sylow image. Every surviving ordinary B.5 section has a cubic
fixer of its Sylow-fixed vectors. The existing extension lemmas lift that
fixer through the literal central quotient and moved submodule, including
nonsplit extensions and the doubled-natural alternative. The exceptional
G₂ and cubic-six sections are too large for these three actors. This
contradicts the original point stabilizer and excludes the three quotients.

The cubic-six source comparisons must consequently remain faithful. The
seven-point, full cubic-six and binary G₂ motion arguments remain separate.
The universal SourceAssembly/PointMotion consumer retains both quotient maps
and the multiple-overgroup guard after every original rechoice.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1, printed p.99.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives NativeSections
private theorem sections_cubic_of_card_lt_1080
    {E V : Type*} [Group E] [Finite E] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) E V) (N : Subgroup E) (K : Subgroup N)
    (s : MovedSection (ρ.comp N.subtype) K)
    (h : SectionAlternatives s) (hc : Nat.card E < 1080) (S : Sylow 2 E) :
    ∃ c : E, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup E), ρ c v = v := by
  let T : Sylow 2 N := Classical.choice inferInstance
  have lift (h : ∃ d : N, d ∉ T ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (ρ.comp N.subtype) (T : Subgroup N), ρ d v = v) :
      ∃ c : E, c ∉ S ∧ c ^ 3 = 1 ∧
        ∀ v ∈ fixedSpace ρ (S : Subgroup E), ρ c v = v := by
    obtain ⟨d,hd,h3,hf⟩ := h
    exact sylow_fixedSpace_enlargement_of_embedded_cubic ρ N.subtype N.subtype_injective
      (T : Subgroup N) T.isPGroup' d h3 (fun he => hd (he ▸ T.one_mem)) hf S
  rcases h with h | h | h
  · exact lift (movedSection_model_enlargement s h T)
  · exact lift (movedSpace_model_enlargement s h T)
  · have hb : Nat.card K < 1080 := lt_of_le_of_lt
      (Nat.card_le_card_of_injective (N.subtype.comp K.subtype)
        (N.subtype_injective.comp K.subtype_injective)) hc
    cases h with
    | binaryG2 _ e =>
      rw [Nat.card_congr e.subgroupEquiv.toEquiv,
        Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hb
      omega
    | tripleSix _ a =>
      have hk : Nat.card K = 1080 := by
        rw [card_eq_card_quotient_mul_card_subgroup (center K),
          Nat.card_congr a.quotientEquiv.toEquiv,
          Nat.card_congr a.centerEquiv.toEquiv,
          nat_card_alternatingGroup,Nat.card_fin]
        norm_num [Nat.factorial]
      omega
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives NativeSections
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d
/-- Both original point groups move the literal seed. The module sections
therefore exclude SL₃(2), A₆ and S₆ as the faithful point-action quotient. -/
theorem point_action_not_small_classical
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPv : P₁ ≤ Gv (markedV d.flag.flag.module))
    (hinter : P₁ ⊓ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) =
      ChapterB.baumann (T : Subgroup G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    ChapterF.IsGoldschmidtTriple (P₁.subgroupOf J) (P₂.subgroupOf J) →
    ∀ (x : J), (x:G) = markedZ d.flag.flag.module * markedV d.flag.flag.module →
    ∀ hr : IsPReduced 2 (conjugateSpanBy (zpowers x) ⊤),
      letI := hr.normal
      letI := hr.elementary
      let U := conjugateSpanBy (zpowers x) ⊤
      let E := J ⧸ centralizer (U : Set J)
      let ρ := ChapterB.InternalThompsonAction.action U
      let N := offenderSubgroup ρ
      let σ := ρ.comp N.subtype
      ¬ Group.IsSolvable E →
      ∀ b : QuasisimpleComparison.BoundedBranch σ,
        SectionAlternatives b.source.sectionData →
        ¬ (Nonempty (E ≃* SL(3,ZMod 2)) ∨ Nonempty (E ≃* alternatingGroup (Fin 6)) ∨
          Nonempty (E ≃* Equiv.Perm (Fin 6))) := by
  intro P₂ J hg x hx hr
  let := hr.normal
  let := hr.elementary
  intro U E ρ N σ hns b hsections hmodel
  let f := QuotientGroup.mk' (centralizer (U : Set J))
  let A := P₁.subgroupOf J
  let B := P₂.subgroupOf J
  obtain ⟨S,hS⟩ := hg.intersection_sylow
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (centralizer (U : Set J)))
  let v : Additive U := Additive.ofMul ⟨x,le_conjugateSpanBy _ _ (mem_zpowers x)⟩
  let C : Subgroup E :=
    (MulAction.stabilizer (Module.End (ZMod 2) (Additive U))ˣ v).comap ρ.asGroupHom
  have hC (g : E) : g ∈ C ↔ ρ g v = v := Iff.rfl
  have hfixed : v ∈ fixedSpace ρ (S' : Subgroup E) := by
    apply (NormalElementaryQuotient.mem_fixedSpace_image U f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (S : Subgroup J) v).mpr
    intro a ha
    apply Subtype.ext
    change (a:G) * (x:G) = (x:G) * (a:G)
    rw [hx]
    have ha' : a ∈ A ⊓ B := hS.ge ha
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      a (hinter ▸ ha')
  have hSC : (S' : Subgroup E) ≤ C := fun a ha => (hC a).mpr (hfixed ⟨a,ha⟩)
  have haC : ¬ A.map f ≤ C := by
    intro h
    have hv : v ∈ fixedSpace ρ (A.map f) := fun a => (hC a).mp (h a.property)
    have hcent := (NormalElementaryQuotient.mem_fixedSpace_image U f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) A v).mp hv
    apply original_paired_point_not_centralizes_complement d hH hB hZ hs hz horiginal hPv
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg J.subtype (hcent ⟨a,mem_sup_left ha⟩ ha)
    change a * (x:G) = (x:G) * a at he
    rwa [hx] at he
  have hbC : ¬ B.map f ≤ C := by
    intro h
    have hv : v ∈ fixedSpace ρ (B.map f) := fun a => (hC a).mp (h a.property)
    have hcent := (NormalElementaryQuotient.mem_fixedSpace_image U f
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) B v).mp hv
    apply point_residual_not_centralizes_complement d
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg J.subtype (hcent ⟨a,mem_sup_right (mem_sup_left ha)⟩ (mem_sup_left ha))
    change a * (x:G) = (x:G) * a at he
    rwa [hx] at he
  have hproper (M : Subgroup J) (hm : Group.IsSolvable M) : M.map f ≠ ⊤ := by
    let := hm
    intro he
    apply hns
    apply Group.isSolvable_of_surjective (f := f.comp M.subtype)
    apply MonoidHom.range_eq_top.mp
    rwa [MonoidHom.range_comp,range_subtype]
  have hCS : C = (S' : Subgroup E) :=
    Theory.SpecificGroups.SmallRankTwoPointMotion.sylow_overgroup_eq_of_avoids_generators
      hmodel S' (A.map f) (B.map f) C
      (map_mono (hS ▸ inf_le_left)) (map_mono (hS ▸ inf_le_right))
      (by rw [←Subgroup.map_sup,hg.generated,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)])
      (hproper A hg.local_solvable) (hproper B hg.symm.local_solvable) hSC haC hbC
  have hc := Theory.SpecificGroups.SmallRankTwoPointMotion.card_lt_1080 hmodel
  obtain ⟨c,hcS,_,hcv⟩ := sections_cubic_of_card_lt_1080 ρ N (generalizedFitting N)
    b.source.sectionData hsections hc S'
  exact hcS (show c ∈ (S' : Subgroup E) from hCS ▸ (hC c).mpr (hcv v hfixed))
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
/-- A small offender actor in an order-168 ambient group would be the whole
SL₃(2) group, so excluding that actual isomorphism excludes order 168. -/
theorem point_card_ne_168_of_not_linearThree
    {E : Type*} [Group E] [Finite E] (N : Subgroup E)
    (h : QuasisimpleComparison.SmallActorModel N)
    (hne : ¬ Nonempty (E ≃* SL(3,ZMod 2))) : Nat.card E ≠ 168 := by
  intro hc
  have hb : Nat.card N ≤ 168 := by
    rw [←hc]
    exact Nat.card_le_card_of_injective N.subtype N.subtype_injective
  have hperm {n : ℕ} (e : N ≃* Equiv.Perm (Fin n)) : Nat.card N = n.factorial := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  have halt {n : ℕ} [Nontrivial (Fin n)] (e : N ≃* alternatingGroup (Fin n)) :
      Nat.card N = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
  cases h with
  | linearThree e =>
    have hn : Nat.card N = 168 :=
      (Nat.card_congr (e.trans Matrix.PSL3Two.equiv).toEquiv).trans Matrix.PSL3Two.card_PSL
    have hN : N = ⊤ := N.eq_top_of_card_eq (hn.trans hc.symm)
    exact hne ⟨((MulEquiv.subgroupCongr hN).trans topEquiv).symm.trans e⟩
  | alternatingSix e => have hh := halt e; norm_num [Nat.factorial] at hh; omega
  | symmetricSix e => have hh := hperm e; norm_num [Nat.factorial] at hh; omega
  | alternatingSeven e => have hh := halt e; norm_num [Nat.factorial] at hh; omega
  | symmetricSeven e => have hh := hperm e; norm_num [Nat.factorial] at hh; omega
  | tripleSix h =>
    have hn : Nat.card N = 1080 := by
      rw [card_eq_card_quotient_mul_card_subgroup (center N),
        Nat.card_congr h.2.2.some.toEquiv,Nat.card_congr h.2.1.some.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin]
      norm_num [GoldschmidtAlternatives.C,Nat.factorial]
    omega
  | g2Derived e =>
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hb
    omega
  | g2 e =>
    rw [Nat.card_congr e.toEquiv,Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at hb
    omega
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
/-- The local movement exclusions force both six-point cubic source covers
through the faithful branch of their original comparison map. -/
theorem point_cubic_six_faithful
    {D E : Type*} [Group D] [Group E] [Finite D] [Finite E] {g : D →* E}
    (c : PointCubicComparison g)
    (hnot : ¬ (Nonempty (E ≃* SL(3,ZMod 2)) ∨
      Nonempty (E ≃* alternatingGroup (Fin 6)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 6)))) :
    (∀ _ : Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.TripleAlternating D 6,
      ∃ e : D ≃* E, ∀ x, e x = g x) ∧
    (∀ _ : Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.TripleSymmetric D 6,
      ∃ e : D ≃* E, ∀ x, e x = g x) := by
  constructor
  · intro h
    rcases c.alternating_six h with h | ⟨_,e,_⟩
    · exact h
    · exact (hnot (Or.inr (Or.inl ⟨e⟩))).elim
  · intro h
    rcases c.symmetric_six h with h | ⟨_,e,_⟩
    · exact h
    · exact (hnot (Or.inr (Or.inr ⟨e⟩))).elim

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
