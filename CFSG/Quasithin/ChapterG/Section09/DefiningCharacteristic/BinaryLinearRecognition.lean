module

public import CFSG.Quasithin.ChapterG.Section09.Basic
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap
public import Theory.Representation.BinaryLinearRecognition
public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank

/-!
# Binary linear alternatives in G.9.3

The natural-degree branches identify the whole ambient group by faithfulness
and the order of its represented component. The six-dimensional branch uses
the actual A₈ action preserving the split quadratic form. For the exterior
branches, a self-normalizing image implies that the component is the whole
ambient group. Every conclusion retains the rank of the original actor.

The final recognition theorems discharge the automorphism-rank bounds,
small-degree exhaustion and exterior-image normalizers using the imported
proofs. Thus `four_alternatives` establishes cases (11)--(12) without extra
premises, and `five_degree_parameters` gives the degrees and actor bounds in
case (13) independently of module identification. The whole-group recognition
`five_alternatives_of_ten_classification` retains precisely the universal
ten-dimensional SL₅ classification as the separate I.1.6 input; its caller
must discharge that input to obtain the unconditional source case (13).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(11)--(13),
printed pp.354,356--357. This is the single-component stage H = L of the proof.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition

open scoped MatrixGroups
open Representation.BinaryLinearRecognition
open Representation.SL5TenDimensional

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- Source cases (11) and (12), with ambient and component identifications
kept in their respective alternatives. -/
def FourAlternatives (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (m : ℕ) : Prop :=
  (Quasiequivalent ρ (naturalAction 4 (by decide)) ∧
    Module.finrank (ZMod 2) V = 4 ∧ 1 ≤ m) ∨
  (Quasiequivalent (ρ.comp L.subtype) orthogonalEightAction ∧
    Module.finrank (ZMod 2) V = 6 ∧ 2 ≤ m)

/-- Source case (13), recording actual natural/exterior module identifications
in addition to the printed ambient-group and degree conclusions. -/
def FiveAlternatives (ρ : Representation (ZMod 2) G V) (m : ℕ) : Prop :=
  (Quasiequivalent ρ (naturalAction 5 (by decide)) ∧
    Module.finrank (ZMod 2) V = 5 ∧ 2 ≤ m) ∨
  (Nonempty (G ≃* PSL(5, ZMod 2)) ∧
    (Quasiequivalent ρ (exteriorAction 2) ∨ Quasiequivalent ρ (exteriorAction 3)) ∧
    Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m)

/-- Case (11) follows once the degree-four branch has been reached. No
module-recognition or overgroup premise is needed in this degree. -/
theorem four_natural_case (h : ComponentHypothesis K ρ A L L m)
    (e : L ≃* PSL(4, ZMod 2)) (hd : Module.finrank (ZMod 2) V = 4) :
    L = ⊤ ∧ Quasiequivalent ρ (naturalAction 4 (by decide)) ∧ 1 ≤ m := by
  obtain ⟨hL, hq⟩ := natural_of_dimension ρ h.faithful L (by decide) e hd
  exact ⟨hL, hq, h.actor_rank_pos⟩

/-- The natural degree-five branch similarly determines the whole group,
with the original actor of rank at least two. -/
theorem five_natural_case (h : ComponentHypothesis K ρ A L L m)
    (e : L ≃* PSL(5, ZMod 2)) (hd : Module.finrank (ZMod 2) V = 5) :
    L = ⊤ ∧ Quasiequivalent ρ (naturalAction 5 (by decide)) ∧ 2 ≤ m := by
  obtain ⟨hL, hq⟩ := natural_of_dimension ρ h.faithful L (by decide) e hd
  exact ⟨hL, hq, by have := h.degree_le; omega⟩

/-- A literal orthogonal identification supplies the source degree and actor
bound; its group is H = L, with no assertion that H is the whole G. -/
theorem four_orthogonal_parameters (h : ComponentHypothesis K ρ A L L m)
    (hq : Quasiequivalent (ρ.comp L.subtype) orthogonalEightAction) :
    Module.finrank (ZMod 2) V = 6 ∧ 2 ≤ m := by
  obtain ⟨e, f, hf⟩ := hq
  have hd := f.finrank_eq.trans finrank_orthogonalEight
  exact ⟨hd, by have := h.degree_le; omega⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem extend_quasiequivalent {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] {σ : Representation (ZMod 2) D W}
    (hL : L = ⊤) (hq : Quasiequivalent (ρ.comp L.subtype) σ) :
    Quasiequivalent ρ σ := by
  obtain ⟨e, f, hf⟩ := hq
  have hs : Function.Surjective L.subtype := by
    intro g
    exact ⟨⟨g, by rw [hL]; trivial⟩, rfl⟩
  let E : L ≃* G := MulEquiv.ofBijective L.subtype ⟨L.subtype_injective, hs⟩
  refine ⟨E.symm.trans e, f, ?_⟩
  intro g v
  have hh := hf (E.symm g) v
  change f (ρ (E (E.symm g)) v) = σ (e (E.symm g)) (f v) at hh
  simpa only [MulEquiv.apply_symm_apply, MulEquiv.trans_apply] using hh

/-- Transfer a concrete exterior-image normalizer calculation back to the
original represented group, and retain its actual module equivalence. -/
theorem five_exterior_case_of_normalizer
    (h : ComponentHypothesis K ρ A L L m) {r : ℕ} (hr : r = 2 ∨ r = 3)
    (hq : Quasiequivalent (ρ.comp L.subtype) (exteriorAction r))
    (hn : Subgroup.normalizer ((exteriorAction r).asGroupHom.range :
        Set (ExteriorModule r →ₗ[ZMod 2] ExteriorModule r)ˣ) =
      (exteriorAction r).asGroupHom.range) :
    L = ⊤ ∧ Quasiequivalent ρ (exteriorAction r) ∧
      Nonempty (G ≃* PSL(5, ZMod 2)) ∧ Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m := by
  obtain ⟨e, f, hf⟩ := hq
  let : L.Normal := h.normal_H
  have hL := eq_top_of_self_normalizing_image ρ (exteriorAction r) h.faithful L e f hf hn
  have hqG := extend_quasiequivalent hL ⟨e, f, hf⟩
  have hd : Module.finrank (ZMod 2) V = 10 := by
    have hh := f.finrank_eq
    rcases hr with rfl | rfl
    · exact hh.trans finrank_exteriorModule_two
    · exact hh.trans finrank_exteriorModule_three
  obtain ⟨E, F, hF⟩ := hqG
  exact ⟨hL, ⟨E, F, hF⟩, ⟨E.trans projectiveEquiv⟩, hd,
    by have := h.degree_le; omega⟩

private theorem degree_bound_of_model_rank {D : Type*} [Group D]
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* D) {r : ℕ}
    (hr : primeRank 2 (MulAut D) ≤ r) :
    m ≤ r ∧ Module.finrank (ZMod 2) V ≤ 2 * (r + 1) := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  let : Finite D := Finite.of_equiv L e.toEquiv
  have hn : A ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
    exact le_top
  have hm := h.toSetup.rank_le_automorphisms hn
  rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)] at hm
  exact ⟨hm.trans hr, h.degree_le.trans (Nat.mul_le_mul_left 2
    (Nat.add_le_add_right (hm.trans hr) 1))⟩

/-- Assembly of cases (11)--(12) from the genuine universal small-module
classification and the independent model automorphism-rank estimate. -/
theorem four_alternatives_of_small_modules
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* PSL(4, ZMod 2))
    (hr : primeRank 2 (MulAut PSL(4, ZMod 2)) ≤ 4)
    (hsmall : ∀ σ : Representation (ZMod 2) PSL(4, ZMod 2) V,
      Function.Injective σ → Representation.IsIrreducible σ →
      Module.finrank (ZMod 2) V ≤ 10 →
      Module.finrank (ZMod 2) V = 4 ∨ Quasiequivalent σ orthogonalEightAction) :
    FourAlternatives ρ L m := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  have hi : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hd : Module.finrank (ZMod 2) V ≤ 10 := (degree_bound_of_model_rank h e hr).2
  rcases hsmall σ hf hi hd with hn | ho
  · have hn' := four_natural_case h e hn
    exact Or.inl ⟨hn'.2.1, hn, hn'.2.2⟩
  · obtain ⟨E, f, hf⟩ := ho
    have hq : Quasiequivalent (ρ.comp L.subtype) orthogonalEightAction := by
      refine ⟨e.trans E, f, ?_⟩
      intro l v
      simpa [σ] using hf (e l) v
    exact Or.inr ⟨hq, four_orthogonal_parameters h hq⟩

/-- G.9.3(11)--(12) for a component actually isomorphic to PSL₄(2).
The intrinsic automorphism bound gives the cutoff ten; the exhaustive
small-module theorem then identifies the ambient natural action or the
component's literal orthogonal A₈ action. The actor is the original `A`. -/
theorem four_alternatives
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* PSL(4, ZMod 2)) :
    FourAlternatives ρ L m :=
  four_alternatives_of_small_modules h e
    _root_.BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
    FourSmallModules.small_modules

/-- Assembly of case (13). The degree gap and the normalizers are independent
of the universal degree-ten classification owned by the I.1.6 development. -/
theorem five_alternatives_of_degree_gap
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* PSL(5, ZMod 2))
    (hr : primeRank 2 (MulAut PSL(5, ZMod 2)) ≤ 6)
    (hgap : ∀ σ : Representation (ZMod 2) Group V,
      Function.Injective σ → Representation.IsIrreducible σ →
      Module.finrank (ZMod 2) V ≤ 14 →
      Module.finrank (ZMod 2) V = 5 ∨ Module.finrank (ZMod 2) V = 10)
    (hten : ∀ σ : Representation (ZMod 2) Group V,
      Representation.IsIrreducible σ → Module.finrank (ZMod 2) V = 10 →
      Nonempty (σ.Equiv (exteriorAction 2)) ∨ Nonempty (σ.Equiv (exteriorAction 3)))
    (hnorm : ∀ r, r = 2 ∨ r = 3 →
      Subgroup.normalizer ((exteriorAction r).asGroupHom.range :
        Set (ExteriorModule r →ₗ[ZMod 2] ExteriorModule r)ˣ) =
      (exteriorAction r).asGroupHom.range) :
    FiveAlternatives ρ m := by
  let E := e.trans projectiveEquiv.symm
  let σ := (ρ.comp L.subtype).comp E.symm.toMonoidHom
  have hi : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp E.symm.injective)
  have hd : Module.finrank (ZMod 2) V ≤ 14 := (degree_bound_of_model_rank h e hr).2
  rcases hgap σ hf hi hd with h5 | h10
  · have hn := five_natural_case h e h5
    exact Or.inl ⟨hn.2.1, h5, hn.2.2⟩
  · have hmodel : ∃ r, (r = 2 ∨ r = 3) ∧ Nonempty (Representation.Equiv σ (exteriorAction r)) := by
      rcases hten σ hi h10 with hs | hc
      · exact ⟨2, Or.inl rfl, hs⟩
      · exact ⟨3, Or.inr rfl, hc⟩
    obtain ⟨r, hr, ⟨f⟩⟩ := hmodel
    have hq : Quasiequivalent (ρ.comp L.subtype) (exteriorAction r) := by
      refine ⟨E, f.toLinearEquiv, ?_⟩
      intro l v
      have hh := congrArg (fun T : V →ₗ[ZMod 2] ExteriorModule r => T v)
        (f.isIntertwining' (E l))
      simpa [σ] using hh
    obtain ⟨hL, hqG, heG, hd10, hm⟩ := five_exterior_case_of_normalizer h hr hq (hnorm r hr)
    refine Or.inr ⟨heG, ?_, hd10, hm⟩
    rcases hr with rfl | rfl
    · exact Or.inl hqG
    · exact Or.inr hqG

/-- The degree and original-actor bounds of G.9.3(13), without any module
identification premise. The bound six on the automorphism two-rank restricts
the degree to at most fourteen, where the exhaustive degree gap applies. -/
theorem five_degree_parameters
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* PSL(5, ZMod 2)) :
    m ≤ 6 ∧ ((Module.finrank (ZMod 2) V = 5 ∧ 2 ≤ m) ∨
      (Module.finrank (ZMod 2) V = 10 ∧ 4 ≤ m)) := by
  have hb := degree_bound_of_model_rank h e
    _root_.BinaryLinear.AutomorphismTwoRank.psl5_two_rank_le
  let E := e.trans projectiveEquiv.symm
  let σ := (ρ.comp L.subtype).comp E.symm.toMonoidHom
  have hi : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp E.symm.injective)
  refine ⟨hb.1, ?_⟩
  rcases FiveDegreeGap.finrank_eq_five_or_ten σ hf hi hb.2 with h5 | h10
  · exact Or.inl ⟨h5, by have := h.degree_le; omega⟩
  · exact Or.inr ⟨h10, by have := h.degree_le; omega⟩

/-- G.9.3(13) with only the explicitly separate universal degree-ten
classification as input. Both exterior images are proved self-normalizing,
so the identified normal component equals the whole faithful ambient group.
The natural branch uses full binary linear-image recognition instead.

The I.1.6 classification owner supplies `hten`; no rank estimate, degree gap,
absolute-irreducibility assumption or normalizer premise remains. -/
theorem five_alternatives_of_ten_classification
    (h : ComponentHypothesis K ρ A L L m) (e : L ≃* PSL(5, ZMod 2))
    (hten : ∀ σ : Representation (ZMod 2) Group V,
      Representation.IsIrreducible σ → Module.finrank (ZMod 2) V = 10 →
      Nonempty (σ.Equiv (exteriorAction 2)) ∨ Nonempty (σ.Equiv (exteriorAction 3))) :
    FiveAlternatives ρ m :=
  five_alternatives_of_degree_gap h e
    _root_.BinaryLinear.AutomorphismTwoRank.psl5_two_rank_le
    FiveDegreeGap.finrank_eq_five_or_ten hten ExteriorNormalizer.normalizer_eq_self

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition
