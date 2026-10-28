module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldClassification
public import CFSG.Quasithin.ChapterG.Section03.TwoCore

/-!
# Transvections on the literal field-plane quotient

If the original fixed plane and commutator plane meet nontrivially, their
intersection has order two and the commutator image is a line. Quadraticity
and faithfulness put the actual conjugate four-group inside its root group.
The full faithful image has trivial two-core, so the repaired G.3 theorem
supplies the canonical full linear blocks, their internal decomposition,
and the local rank assertions. The line is the image of the original
commutator plane, and the original quotient coordinates are retained.

This is the recognition step in the moved-line branch of 6.2.7. The cubic
action and component restrictions must still exclude these blocks. No
LocalAnalysis or later M₂₂ recognition is assumed. The companion Chapter12
module applies the result to its actual whole reduced commutator layer.

Source: Aschbacher--Smith, 6.2.7, printed pp.682--683; G.3.1, pp.337--338,
with the faithful-image two-core supplied by 6.2.4(4).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryLinear BinaryTransvectionGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction

/-- Full G.3 recognition on the actual linear image of a faithful section,
with the prescribed commutator line and the literal actor image. -/
@[expose] def LineRecognition
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (I : Subgroup D)
    (C : Submodule (ZMod 2) W) : Prop :=
    let f : D →* BinaryLinear.GL W :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom
    ∃ x : W, x ≠ 0 ∧ C = centerLine x ∧
      I.map f ≤ rootGroup f.range x ∧ pCore 2 f.range = ⊥ ∧
      ChapterG.Section03.Hypotheses f.range (MulAction.orbit f.range x) ∧
      ChapterG.Section03.FullAction f.range (MulAction.orbit f.range x) ∧
      ChapterG.Section03.Decomposition f.range (MulAction.orbit f.range x) ∧
      ChapterG.Section03.LocalStructure f.range (MulAction.orbit f.range x)

private theorem line_recognition
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (I : Subgroup D) (hIc : Nat.card I = 4)
    (hquad : IsQuadratic ρ I) (hdim : Module.finrank (ZMod 2) (moved ρ I) = 1) :
    LineRecognition ρ I (moved ρ I) := by
  let f : D →* BinaryLinear.GL W :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom
  have hf : Function.Injective f := by
    intro a b he
    apply hfaith
    ext w
    exact congrArg (fun k : BinaryLinear.GL W => k w) he
  have hcore' : pCore 2 f.range = ⊥ := by
    let e := MonoidHom.ofInjective hf
    rw [← pCore_map_iso 2 e, hcore, Subgroup.map_bot]
  have hne : moved ρ I ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hdim
    contradiction
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hline : moved ρ I = centerLine x := by
    apply (Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) ?_).symm
    exact (finrank_span_singleton hx0).trans hdim.symm
  have hfix : moved ρ I ≤ fixedSpace ρ I := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, hb, w, _, rfl⟩ a
    exact hquad a a.property b hb w
  have hroot : I.map f ≤ rootGroup f.range x := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨⟨a,rfl⟩, ?_, ?_⟩
    · intro w hw
      exact hfix (hline.symm ▸ hw) ⟨a,ha⟩
    · intro w
      rw [← hline]
      exact Submodule.subset_span ⟨a,ha,w,Submodule.mem_top,rfl⟩
  have hrcard : 2 < Nat.card (rootGroup f.range x) := by
    have hc := card_le_of_le hroot
    rw [card_map_of_injective hf,hIc] at hc
    omega
  have hG3 : ChapterG.Section03.Hypotheses f.range (MulAction.orbit f.range x) := by
    refine ⟨?_,⟨x,rfl⟩,?_⟩
    · rintro y ⟨g,rfl⟩
      exact fun he => hx0 (g.val.injective (he.trans g.val.map_zero.symm))
    · intro y hy
      obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hy
      change 1 < Group.rank (ChapterG.Section03.rootQuotientImage f.range (g.val x))
      have hr : 2 < Nat.card (rootGroup f.range (g.val x)) := by
        rw [← rootGroup_conjugate g.property x,card_map_of_injective (MulAut.conj g.val).injective]
        exact hrcard
      let q := QuotientGroup.mk' (pCore 2 f.range)
      have hi : Function.Injective q := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        rw [QuotientGroup.ker_mk',hcore']
      have hcq : Nat.card (ChapterG.Section03.rootQuotientImage f.range (g.val x)) =
          Nat.card (rootGroup f.range (g.val x)) :=
        (Nat.card_congr (((rootGroup f.range (g.val x)).subgroupOf f.range).equivMapOfInjective q hi).toEquiv).symm.trans
          (Nat.card_congr (subgroupOfEquivOfLe (rootGroup_le f.range (g.val x))).toEquiv)
      let := ChapterG.Section03.rootQuotientImage_elementaryAbelian f.range (g.val x)
      have hbound : Nat.card (ChapterG.Section03.rootQuotientImage f.range (g.val x)) ≤
          2 ^ Group.rank (ChapterG.Section03.rootQuotientImage f.range (g.val x)) :=
        Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' _
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _)))
      by_contra hn
      have hp := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (not_lt.mp hn)
      rw [hcq] at hbound
      omega
  exact ⟨x,hx0,hline,hroot,hcore',hG3,
    ChapterG.Section03.source_conclusions_of_twoCore_eq_bot hG3 hcore'⟩

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- G.3 on the literal quotient when the two original planes meet nontrivially.
The original conjugate four-group lies in the root group at the moved line. -/
theorem exists_line_recognition
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G))
    (hmeet : (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)) ⊓
      ⁅(layer L R).map (MulAut.conj g).toMonoidHom, layer L R⁆ ≠ ⊥) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    letI := (reduced_space h hnatural hE hfactor
      (local_one_sided_field_plane h hnatural hE hfactor g hBA hnon).2.1
      (local_one_sided_field_plane h hnatural hE hfactor g hBA hnon).1.ge).elementary
    let W := Additive (space B U)
    let H := Centralizer U
    let J := conjugateSpanBy B H
    let π := (action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (action B U).range W)
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ Nat.card I = 4 ∧
      LineRecognition ρ I (c.imageSpace ⁅A,B⁆) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, projection U ⟨j, hj⟩ =
        ((c.coordinates j).toAdd.toMul : Ambient U) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h hnatural hE hfactor g hBA hnon
  let := (reduced_space h hnatural hE hfactor hfield hUc.ge).elementary
  obtain ⟨ρ,c,hfaith,hI,hIc,hmark⟩ := exists_faithful_offender h hnatural hE hfactor g hBA hnon
  obtain ⟨hquad,hm,_,_,hcases,_⟩ := section_plane_geometry h hnatural hE hfactor g hBA hnon ρ c
  have hdim := (hcases.resolve_left (fun he => hmeet he.1)).2
  have hrec :=
    line_recognition ρ hfaith (action_range_core h hnatural hE hfactor hfield hUc.ge)
      _ hIc hquad hdim
  rw [hm] at hrec
  exact ⟨ρ,c,hfaith,hI,hIc,hrec,hmark⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
