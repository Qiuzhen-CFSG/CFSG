module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointG2Motion
public import Theory.SpecificGroups.SmallRankTwoPointMotion.CentralCover

/-!
# Excluding the full central cubic A₆ point quotient

Both original point groups move the complementary point fixed by their common
Baumann Sylow. Local Sylow normal generation descends those two movements
through the cubic center. The ordinary A₆ parabolic interval forces the
projected stabilizer to be Sylow. Since a central fixer of the original point
fixes its whole conjugate span, the stabilizer meets the center trivially and
lifts to the original Sylow subgroup. Every surviving literal B.5 section has
a cubic fixer outside that subgroup, including nonsplit module extensions.

The already checked faithful comparison excludes the source cubic cover as
well. The two-group quotient of the normal offender subgroup also eliminates
action-quotient order 1080. SourceAssembly/PointCentralCover applies all of
these conclusions after every original rechoice, retaining both projections
and the multiple-overgroup guard.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1 and F.6.18(6).
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives NativeSections
private theorem sections_cubic
    {E V : Type*} [Group E] [Finite E] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) E V) (N : Subgroup E) (K : Subgroup N)
    (s : MovedSection (ρ.comp N.subtype) K)
    (h : SectionAlternatives s) (S : Sylow 2 E) :
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
  · cases h with
    | binaryG2 _ e => exact lift (ExceptionalFixedSpace.BinaryG2.enlargement s e T)
    | tripleSix hf a => exact lift (ExceptionalFixedSpace.TripleSix.movedSection_enlargement s hf a T)
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d
/-- The original point action cannot be the full cubic A₆ cover.
The central quotient descends the point stabilizer and both moving local groups.
The literal source section supplies a cubic fixer outside the resulting Sylow stabilizer. -/
theorem point_action_not_triple_alternating_six
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
        ¬ Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.TripleAlternating E 6 := by
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
  let q := hmodel.quotient.some.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hq : Function.Surjective q :=
    hmodel.quotient.some.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center E := by
    rw [MonoidHom.ker_comp_of_injective _ _ hmodel.quotient.some.injective,
      QuotientGroup.ker_mk']
  have hCpre : C.comap f = centralizer ({x} : Set J) := by
    ext j
    change (ρ (f j) v = v) ↔ j ∈ centralizer ({x} : Set J)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro he
      have hh := congrArg (fun w : Additive U => (w.toMul : J)) he
      rw [ChapterB.InternalThompsonAction.action_apply] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro he
      apply Subtype.ext
      change ((ρ (f j) v).toMul : J) = x
      rw [ChapterB.InternalThompsonAction.action_apply]
      exact mul_inv_eq_iff_eq_mul.mpr he
  have hCimage : C = (centralizer ({x} : Set J)).map f := by
    rw [←hCpre,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hfaith : C ⊓ q.ker = ⊥ := by
    rw [hk,hCimage]
    exact Theory.SpecificGroups.SmallRankTwoPointMotion.CentralCover.centralizer_seed_image_inf_center_eq_bot
      x f (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  obtain ⟨_,_,_,eA,eB,_,_⟩ := point_span_action_comparison d hH hB hZ hs hz
    horiginal hPv hinter hg x hx U hr (le_conjugateSpanBy _ _ (mem_zpowers x))
  let ea : (A.map f ⧸ pCore 2 (A.map f)) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans
      hg.primeToThreeCore_quotient_left.some
  let eb : (B.map f ⧸ pCore 2 (B.map f)) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans
      hg.symm.primeToThreeCore_quotient_left.some
  have hsol (M : Subgroup J) (h : Group.IsSolvable M) : Group.IsSolvable (M.map f) := by
    let := h
    exact Group.isSolvable_of_surjective (f.subgroupMap_surjective M)
  have hCS : C = (S' : Subgroup E) :=
    Theory.SpecificGroups.SmallRankTwoPointMotion.CentralCover.central_cover_point_stabilizer
      q hq hk.le S' (A.map f) (B.map f) C
      (map_mono (hS ▸ inf_le_left)) (map_mono (hS ▸ inf_le_right))
      (by rw [←Subgroup.map_sup,hg.generated,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)])
      (hsol A hg.local_solvable) (hsol B hg.symm.local_solvable) ea eb hSC haC hbC hfaith
  obtain ⟨c,hcS,_,hcv⟩ := sections_cubic ρ N (generalizedFitting N)
    b.source.sectionData hsections S'
  exact hcS (show c ∈ (S' : Subgroup E) from hCS ▸ (hC c).mpr (hcv v hfixed))
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
/-- The faithful original comparison carries the cubic A₆ exclusion back
through the original map, without discarding its central kernel by assumption. -/
theorem point_not_triple_alternating_six_source
    {D E : Type*} [Group D] [Group E] [Finite D] [Finite E] {g : D →* E}
    (hfaith : ∀ _ : FSource.TripleAlternating D 6,
      ∃ e : D ≃* E, ∀ x, e x = g x)
    (hne : ¬ FSource.TripleAlternating E 6) : ¬ FSource.TripleAlternating D 6 := by
  intro h
  obtain ⟨e,_⟩ := hfaith h
  exact hne (Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.tripleAlternating_of_equiv
    e.symm h)
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
/-- With two-group quotient, order 1080 forces the small offender actor to
be the whole cubic A₆ cover. Thus the cover exclusion also removes that order. -/
theorem point_card_ne_1080_of_not_cubic
    {E : Type*} [Group E] [Finite E] (N : Subgroup E) [N.Normal]
    (hq : IsPGroup 2 (E ⧸ N)) (hmodel : QuasisimpleComparison.SmallActorModel N)
    (hne : ¬ FSource.TripleAlternating E 6) : Nat.card E ≠ 1080 := by
  intro hc
  have hb : Nat.card N ≤ 1080 := by
    rw [←hc]
    exact Nat.card_le_card_of_injective N.subtype N.subtype_injective
  have h27 : 27 ∣ Nat.card N := by
    obtain ⟨k,hk⟩ := hq.exists_card_eq
    have hh : Nat.card E = Nat.card N * 2^k := by
      rw [←hk,←index_eq_card,card_mul_index]
    have hd : 27 ∣ Nat.card N * 2^k := by rw [←hh,hc]; decide
    exact ((by decide : Nat.Coprime 27 2).pow_right k).dvd_of_dvd_mul_right hd
  have hperm {n : ℕ} (e : N ≃* Equiv.Perm (Fin n)) : Nat.card N = n.factorial := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  have halt {n : ℕ} [Nontrivial (Fin n)] (e : N ≃* alternatingGroup (Fin n)) :
      Nat.card N = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
  cases hmodel with
  | linearThree e =>
    rw [Nat.card_congr (e.trans Matrix.PSL3Two.equiv).toEquiv,Matrix.PSL3Two.card_PSL] at h27
    norm_num at h27
  | alternatingSix e => rw [halt e] at h27; norm_num [Nat.factorial] at h27
  | symmetricSix e => rw [hperm e] at h27; norm_num [Nat.factorial] at h27
  | alternatingSeven e => rw [halt e] at h27; norm_num [Nat.factorial] at h27
  | symmetricSeven e => rw [hperm e] at h27; norm_num [Nat.factorial] at h27
  | tripleSix h =>
    have hn : Nat.card N = 1080 := by
      rw [card_eq_card_quotient_mul_card_subgroup (center N),
        Nat.card_congr h.2.2.some.toEquiv,Nat.card_congr h.2.1.some.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin]
      norm_num [GoldschmidtAlternatives.C,Nat.factorial]
    have hN : N = ⊤ := N.eq_top_of_card_eq (hn.trans hc.symm)
    let e : N ≃* E := (MulEquiv.subgroupCongr hN).trans topEquiv
    exact hne (Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.tripleAlternating_of_equiv
      e.symm ⟨h.1,h.2.1,h.2.2⟩)
  | g2Derived e =>
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hb
    omega
  | g2 e =>
    rw [Nat.card_congr e.toEquiv,Atlas.G2.LieAutomorphismExtensions.card_binaryFull] at hb
    omega
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
