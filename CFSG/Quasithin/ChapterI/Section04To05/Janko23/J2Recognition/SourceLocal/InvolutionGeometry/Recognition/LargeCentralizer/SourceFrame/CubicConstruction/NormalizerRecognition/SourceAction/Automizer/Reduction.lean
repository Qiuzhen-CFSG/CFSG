module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Action
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.RootQuotient
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Center
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerInvariants

/-!
# Transporting the source normalizer invariants to root coordinates

The preimage of the inner automorphisms under literal normalizer conjugation
is precisely R: the image of R is the inner subgroup, and the kernel is E ≤ R.
Thus a central cubic coset modulo R becomes a central cubic coset modulo inner
automorphisms. The kernel also converts normalizer order 1152 to image order 288.
Transport of the center action uses the actual center equivalence induced by
the supplied root coordinates.

`SourceInvariants` records three earlier-source obligations, not the desired
image equality. `exists_adjustment_of_source_invariants` is conditional on their
construction and on an independent classification of concrete subgroups of
Aut(UT₃(F₄)). Neither existence assertion is proved in this module.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(5–6), 46.3(2),
and 46.14, printed pp.29–30, 251, and 257–258.
-/

@[expose] public section

open Subgroup Matrix.PSL3Four
open scoped commutatorElement
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

/-- The source order and the two action properties used by the independent
root-automorphism calculation. The intrinsic center is the literal E by
`SourceAction.E_center`. The cubic is a coset witness, not a chosen complement. -/
structure SourceInvariants : Prop where
  normalizer_card : Nat.card (normalizer (P.R : Set G)) = 1152
  full_center_action : ∀ b : MulAut (center P.R),
    ∃ n : normalizer (P.R : Set G),
      ∀ z : center P.R, P.R.normalizerMonoidHom n z = (b z : P.R)
  central_cubic : ∃ c : normalizer (P.R : Set G),
    (c : G) ∉ P.R ∧ (c : G) ^ 3 ∈ P.R ∧
    ∀ n : normalizer (P.R : Set G), ⁅(c : G), (n : G)⁆ ∈ P.R

variable (e : P.R ≃* RootNormalizerModel.Root)

/-- Coordinate change acts by the corresponding automorphism congruence. -/
theorem conjugation_change_coordinates (a : MulAut RootNormalizerModel.Root) :
    conjugation P (e.trans a) =
      (MulAut.congr a).toMonoidHom.comp (conjugation P e) := by
  apply MonoidHom.ext
  intro n
  apply MulEquiv.ext
  intro x
  rfl

/-- The exact image transport used in the adjustment contract. -/
theorem range_change_coordinates (a : MulAut RootNormalizerModel.Root) :
    (conjugation P (e.trans a)).range =
      (conjugation P e).range.map (MulAut.congr a).toMonoidHom := by
  rw [conjugation_change_coordinates, MonoidHom.range_comp]

/-- The actual embedded root subgroup has precisely the inner image. -/
theorem root_image :
    (P.R.subgroupOf (normalizer (P.R : Set G))).map (conjugation P e) =
      (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range := by
  rw [← rootEmbedding_range P e, ← MonoidHom.range_comp]
  congr 1
  apply MonoidHom.ext
  intro r
  exact conjugation_rootEmbedding P e r

/-- Self-centralization rules out any additional preimages of inner actors. -/
theorem inner_preimage :
    ((MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range).comap
      (conjugation P e) = P.R.subgroupOf (normalizer (P.R : Set G)) := by
  rw [← root_image P e]
  apply comap_map_eq_self
  rw [conjugation_kernel P e]
  exact fun _ hx => P.E_le_R hx

/-- Membership formulation for transporting literal cubic and commutator bounds. -/
theorem conjugation_mem_inner_iff (n : normalizer (P.R : Set G)) :
    conjugation P e n ∈
      (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ↔
      (n : G) ∈ P.R := by
  exact SetLike.ext_iff.mp (inner_preimage P e) n

/-- The four-element action kernel gives the required image order. -/
theorem range_card (h : Nat.card (normalizer (P.R : Set G)) = 1152) :
    Nat.card (conjugation P e).range = 288 := by
  have heN : P.E ≤ normalizer (P.R : Set G) := P.E_le_R.trans le_normalizer
  have hk : Nat.card (conjugation P e).ker = 4 := by
    rw [conjugation_kernel P e]
    exact (Nat.card_congr (subgroupOfEquivOfLe heN).toEquiv).trans P.E_card
  have hc := (conjugation P e).ker.card_mul_index
  rw [index_ker, hk, h] at hc
  omega

/-- Every source invariant is transported along the supplied root isomorphism. -/
theorem image_invariants (h : SourceInvariants P) :
    RootNormalizerModel.AutomizerInvariants (conjugation P e).range := by
  refine ⟨inner_le_conjugation_range P e, range_card P e h.normalizer_card, ?_, ?_⟩
  · intro b
    let ec := centerCongr e
    obtain ⟨n, hn⟩ := h.full_center_action (MulAut.congr ec.symm b)
    refine ⟨conjugation P e n, ⟨n, rfl⟩, ?_⟩
    intro z
    have hz := congrArg e (hn (ec.symm z))
    change e (P.R.normalizerMonoidHom n (e.symm (z : RootNormalizerModel.Root))) =
      e (e.symm (b (ec (ec.symm z)) : RootNormalizerModel.Root)) at hz
    rw [ec.apply_symm_apply, e.apply_symm_apply] at hz
    exact hz
  · obtain ⟨c, hc, hc3, hcomm⟩ := h.central_cubic
    refine ⟨conjugation P e c, ⟨c, rfl⟩,
      (conjugation_mem_inner_iff P e c).not.mpr hc, ?_, ?_⟩
    · rw [← map_pow, conjugation_mem_inner_iff]
      exact hc3
    · rintro a ⟨n, rfl⟩
      rw [← map_commutatorElement, conjugation_mem_inner_iff]
      exact hcomm n

/-- Conditional assembly: the model subgroup-classification theorem is still
an explicit input, as are the independently constructed source invariants. -/
theorem exists_adjustment_of_source_invariants
    (h : SourceInvariants P)
    (recognize : ∀ H : Subgroup (MulAut RootNormalizerModel.Root),
      RootNormalizerModel.AutomizerInvariants H →
      ∃ a : MulAut RootNormalizerModel.Root,
        H.map (MulAut.congr a).toMonoidHom =
          (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ⊔
            RootNormalizerModel.actor) :
    ∃ a : MulAut RootNormalizerModel.Root,
      (conjugation P (e.trans a)).range =
        (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ⊔
          RootNormalizerModel.actor := by
  obtain ⟨a, ha⟩ := recognize (conjugation P e).range (image_invariants P e h)
  exact ⟨a, (range_change_coordinates P e a).trans ha⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
