module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointMotion
public import Theory.SpecificGroups.G2.BinaryPointMotion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.BinaryG2
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.TripleSix

/-!
# Excluding the full binary G₂ point action

Both original point groups move the same complementary point and the common
Baumann Sylow fixes it. The full G₂(2) subgroup interval forces its stabilizer
to be that Sylow subgroup. Every literal surviving B.5 section supplies a
nontrivial cubic fixer, including the exceptional G₂ and cubic-six sections.
The checked central-section and trivial-quotient lifts preserve nonsplit
extensions. Their witness contradicts the original point stabilizer.

The faithful original graph-extension comparison consequently excludes
F.6.18(11). The SourceAssembly/PointG2Motion consumer applies these results
after every original rechoice with the multiple-overgroup guard intact.
No outside-Sylow fixed-space premise is assumed.
Source: Aschbacher--Smith 13.2.12, printed p.882; B.5.1 and F.6.18(11).
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
/-- The original two point groups exclude the actual full G₂(2) quotient.
Its parabolic lattice forces the point stabilizer to be Sylow, while the
literal source section supplies a cubic fixer outside it. -/
theorem point_action_not_binaryG2
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
        ¬ Nonempty (E ≃* Atlas.G2.Model (ZMod 2)) := by
  intro P₂ J hg x hx hr
  let := hr.normal
  let := hr.elementary
  intro U E ρ N σ hns b hsections hmodel
  obtain ⟨e⟩ := hmodel
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
    Theory.SpecificGroups.G2.BinaryPointMotion.sylow_overgroup_eq_of_avoids_generators
      e S' (A.map f) (B.map f) C
      (map_mono (hS ▸ inf_le_left)) (map_mono (hS ▸ inf_le_right))
      (by rw [←Subgroup.map_sup,hg.generated,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)])
      (hproper A hg.local_solvable) (hproper B hg.symm.local_solvable) hSC haC hbC
  obtain ⟨c,hcS,_,hcv⟩ := sections_cubic ρ N (generalizedFitting N)
    b.source.sectionData hsections S'
  exact hcS (show c ∈ (S' : Subgroup E) from hCS ▸ (hC c).mpr (hcv v hfixed))
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- The existing injectivity comparison transports the original graph-extension
row to the excluded actual G₂ action quotient. Both quotients remain distinct. -/
theorem point_not_graph_extension
    {D E W : Type*} [Group D] [Group E] [Finite D] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) E W} {g : D →* E}
    (c : PointDegreeThreeComparison ρ g) (hg : Function.Surjective g)
    (hne : ¬ Nonempty (E ≃* Atlas.G2.Model (ZMod 2))) :
    ¬ Nonempty (FSource.GraphExtensionRow (D := D)) := by
  rintro ⟨r⟩
  obtain ⟨_,hi,⟨e⟩⟩ := c.graph_extension r
  exact hne ⟨(MulEquiv.ofBijective g ⟨hi,hg⟩).symm.trans e⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
