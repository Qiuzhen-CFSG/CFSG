module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.FullyMoved
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.SuzukiRadical

/-!
# Both Ree residuals in the original point configuration

The full-Sylow embedding theorem marks the actual smaller component as
one of the two Ree parabolic residuals. The Suzuki residual centralizes
its two-core center, contradicting the noncentral core center of the
original local image. The linear residual has trivial involutory
pointwise automorphism fixer, so the opposite moved factor centralizes
the containing component, contradicting its escape.

This closes the Ree and hence the whole rank-two containing-carrier
family without any assumption on the original quotient or irreducibility
of the moved module. Source: Aschbacher--Smith A.3.12, F.1.12(I)(5),
and 10.2.9, printed pp.47--48,263--264,750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
include D c

/-- Literal placement in either residual, without a cubic divisor premise. -/
theorem ree_placement_both
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) :
    ∃ (f : (I ⧸ center I) ≃* ReeF4.Model m) (s : ReeF4.LargeLocalSeeds.Side),
      (L.subgroupOf I).map (f.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        ReeF4.Parabolics.localFactor m s := by
  obtain ⟨S,_,hB,_,_,hproper,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let A := B.map eI.toMonoidHom
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup (ReeF4.Model m) := eI.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective
    (f := eI.toMonoidHom) eI.surjective
  let : IsQuasisimple (ReeF4.Model m) := IsQuasisimple.of_surjective
    (eI.toMonoidHom.comp q) (eI.surjective.comp (QuotientGroup.mk'_surjective _))
  have htop : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent :=
    (show IsComponent (ReeF4.Model m) ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  let : Group.IsSolvable eI.toMonoidHom.ker := by
    rw [eI.toMonoidHom.ker_eq_bot_iff.mpr eI.injective]
    infer_instance
  have hA : A ∈ localCComponents (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB eI.toMonoidHom
  have hp : A ≠ ⊤ := by
    intro ht
    apply hproper
    apply map_injective (f := eI.toMonoidHom) eI.injective
    rw [map_top_of_surjective _ eI.surjective]
    exact ht
  obtain ⟨g,s,hg⟩ := SourceEmbeddings.ReeLocal.local_placement hm htop
    (R.mapSurjective (f := eI.toMonoidHom) eI.surjective) A hA hp
  refine ⟨eI.trans (MulAut.conj g),s,?_⟩
  have he : (eI.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp eI.toMonoidHom := by ext; rfl
  simpa only [A,B,q,map_map,he,MonoidHom.comp_assoc] using hg

/-- Both residuals contradict the original escaping configuration. -/
theorem not_ree
    {m : ℕ} (hm : 1 ≤ m) (eI : (I ⧸ center I) ≃* ReeF4.Model m) : False := by
  obtain ⟨f,s,hf⟩ := ree_placement_both D c hm eI
  cases s with
  | suzuki =>
    let B := (L.subgroupOf I).map (f.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    let e := (MulEquiv.subgroupCongr hf).trans
      (ReeF4.Parabolics.localFactorStandardSeedEquiv m .suzuki)
    let k := e.toMonoidHom.comp (markedLocalHom c.strict.le f)
    have hk : Function.Surjective k := e.surjective.comp (markedLocalHom_surjective c.strict.le f)
    have hker : k.ker ≤ center L := by
      intro l hl
      apply markedLocalHom_ker_le_center c.strict.le f
      exact e.injective (hl.trans e.map_one.symm)
    apply central_image_core_center_not_central D k hk hker
    rintro _ ⟨z,hz,rfl⟩
    apply ReeF4.NormalizedRootCentralizers.CenterExponent.suzuki_seed_core_centralizer_le_center hm
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨r,hr⟩)
  | linear =>
    let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
    let : IsSimpleGroup (ReeF4.Model m) := f.symm.isSimpleGroup
    let : Group.IsPerfect (ReeF4.Model m) := Group.IsPerfect.ofSurjective
      (f := f.toMonoidHom) f.surjective
    apply source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer I c.escapes
    apply Other.common_centralizer_of_marked_fixer D c f
    rw [hf]
    exact ReeF4.LinearLocalFixer.eq_one_of_fixes_linearLocal hm

/-- Every rank-two containing carrier is excluded, retaining all module rows. -/
theorem not_rank_two
    (hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) : False := by
  obtain ⟨m,hm,⟨e⟩⟩ := remaining_ree_models D c hm
  exact not_ree D c hm e
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
