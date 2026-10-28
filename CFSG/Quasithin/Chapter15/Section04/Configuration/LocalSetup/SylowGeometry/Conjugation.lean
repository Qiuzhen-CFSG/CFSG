module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.MaximalChoice
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.Placement
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.SylowKernelCore

/-!
# Placing the maximal contrary Sylow subgroup

Choose a contrary local overgroup of maximal Sylow two-order. Baumann
normalizer control supplies a conjugating element in both maximal locals
which moves its Sylow subgroup into the specified `T`. The actual factor
permutations force the conjugate of `T₀` into `T₀`, and finite cardinality
then gives equality. Thus the generated group moves to another of the four
factor choices. Transport of intrinsic cores and Sylow images preserves the
maximal-choice consequence in all subsequent `H`-overgroups.

The resulting two-group lies strictly between `T₀` and `T`, has both indices
two, and is Sylow in the normalizer of the contrary overgroup's two-core.
This proves the corrected first paragraph of the 15.4.20 contradiction;
the two printed occurrences of `T₀` in that normalizer claim must denote
the larger subgroup instead. A moved factor generates the whole product
under this larger subgroup's conjugation action.

The factor permutations are explicit raw conjugation witnesses, to be
constructed from the source 15.4.12 factors. No final Sylow conclusion for
`T₀`, embedding classification, or later group identification is assumed.
The remaining intrinsic Ξ input and generalized-Fitting case eliminations
are separate obligations of the 15.4.20 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1163–1164, proof of Lemma 15.4.20.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- A two-subgroup in an overgroup of `T` can be conjugated into `T` by an
element of that same overgroup. -/
theorem conjugate_into_sylow_inside_overgroup (T : Sylow 2 G) {H U : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hUH : U ≤ H) (hU : IsPGroup 2 U) :
    ∃ g ∈ H, U.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) := by
  obtain ⟨P, hP⟩ := (hU.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P (T.subtype hTH)
  refine ⟨g, g.property, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  have huP : (⟨u, hUH hu⟩ : H) ∈ (P : Subgroup H) := hP hu
  have hconj : (MulAut.conj g) ⟨u, hUH hu⟩ ∈ ((g • P : Sylow 2 H) : Subgroup H) :=
    ⟨⟨u, hUH hu⟩, huP, rfl⟩
  rw [hg] at hconj
  exact hconj

/-- Conjugation into `T` preserves the common stabilizer, provided the actual
factor sets are permuted. Containment gives one direction, and equal finite
orders give equality; no normalization of `T` by the conjugating element is
assumed. -/
theorem common_stabilizer_preserved_by_factor_permutation
    (d : Source.Geometry G)
    (hnX : ∀ i, d.T₀ ≤ normalizer (d.X i : Set G))
    (hnY : ∀ j, d.T₀ ≤ normalizer (d.Y j : Set G))
    (g : G) (σ τ : Equiv.Perm Bool)
    (hgX : ∀ i, (d.X i).map (MulAut.conj g).toMonoidHom = d.X (σ i))
    (hgY : ∀ j, (d.Y j).map (MulAut.conj g).toMonoidHom = d.Y (τ j))
    (hinto : d.T₀.map (MulAut.conj g).toMonoidHom ≤ (d.T : Subgroup G)) :
    d.T₀.map (MulAut.conj g).toMonoidHom = d.T₀ := by
  have hn (L : Subgroup G) (hL : d.T₀ ≤ normalizer (L : Set G)) :
      d.T₀.map (MulAut.conj g).toMonoidHom ≤
        normalizer (L.map (MulAut.conj g).toMonoidHom : Set G) :=
    (map_mono hL).trans (L.le_normalizer_map _)
  have hnX₀ : d.T₀.map (MulAut.conj g).toMonoidHom ≤ normalizer (d.X false : Set G) := by
    have h := hn (d.X (σ.symm false)) (hnX _)
    simpa only [hgX, σ.apply_symm_apply] using h
  have hnY₀ : d.T₀.map (MulAut.conj g).toMonoidHom ≤ normalizer (d.Y false : Set G) := by
    have h := hn (d.Y (τ.symm false)) (hnY _)
    simpa only [hgY, τ.apply_symm_apply] using h
  apply eq_of_le_of_card_ge (le_inf (le_inf hinto hnX₀) hnY₀)
  exact (card_map_of_injective (MulAut.conj g).injective).ge

/-- The normalizer of the Baumann subgroup supplies a conjugating element in
both maximal locals. The factor permutations then preserve `T₀` and transport
each generated pair to another of the four pairs in the same geometry. -/
theorem conjugate_two_overgroup_preserving_geometry
    (d : Source.Geometry G)
    (hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀)
    (hM₁ : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M₁)
    (hM₂ : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M₂)
    (hnX : ∀ i, d.T₀ ≤ normalizer (d.X i : Set G))
    (hnY : ∀ j, d.T₀ ≤ normalizer (d.Y j : Set G))
    (hpermX : ∀ g ∈ d.M₁, ∃ σ : Equiv.Perm Bool,
      ∀ i, (d.X i).map (MulAut.conj g).toMonoidHom = d.X (σ i))
    (hpermY : ∀ g ∈ d.M₂, ∃ τ : Equiv.Perm Bool,
      ∀ j, (d.Y j).map (MulAut.conj g).toMonoidHom = d.Y (τ j))
    {U : Subgroup G} (hU : IsPGroup 2 U) (hTU : d.T₀ ≤ U) :
    ∃ g ∈ d.M₁ ⊓ d.M₂, ∃ σ τ : Equiv.Perm Bool,
      U.map (MulAut.conj g).toMonoidHom ≤ (d.T : Subgroup G) ∧
      d.T₀.map (MulAut.conj g).toMonoidHom = d.T₀ ∧
      (∀ i, (d.X i).map (MulAut.conj g).toMonoidHom = d.X (σ i)) ∧
      (∀ j, (d.Y j).map (MulAut.conj g).toMonoidHom = d.Y (τ j)) ∧
      (∀ i j, (d.I i j).map (MulAut.conj g).toMonoidHom = d.I (σ i) (τ j)) := by
  let N := normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G)
  have hTN : (d.T : Subgroup G) ≤ N :=
    le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann _)
  have hUN : U ≤ N := Stellmacher.twoSubgroup_le_normalizer_baumann d.T U hU (hS.trans hTU)
  obtain ⟨g, hg, hinto⟩ := conjugate_into_sylow_inside_overgroup d.T hTN hUN hU
  obtain ⟨σ, hgX⟩ := hpermX g (hM₁ hg)
  obtain ⟨τ, hgY⟩ := hpermY g (hM₂ hg)
  have hT₀ := common_stabilizer_preserved_by_factor_permutation d hnX hnY g σ τ hgX hgY
    ((map_mono hTU).trans hinto)
  refine ⟨g, ⟨hM₁ hg, hM₂ hg⟩, σ, τ, hinto, hT₀, hgX, hgY, ?_⟩
  intro i j
  change ((d.X i ⊔ d.T₀) ⊔ (d.Y j ⊔ d.T₀)).map _ = _
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, hgX, hgY, hT₀]
  rfl


omit [Finite G] in
/-- Membership in the genuine `H`-overgroup family is preserved by an actual
ambient automorphism, including the intrinsic two-core condition. -/
theorem HOver_map_equiv (e : G ≃* G) {I H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (I : Set G)) :
    H.map e.toMonoidHom ∈ Chapter1.HOver G (I.map e.toMonoidHom : Set G) := by
  refine ⟨?_, map_mono hH.2⟩
  change (H.map e.toMonoidHom).pCoreIn 2 ≠ ⊥
  rw [← map_pCoreIn_of_injective 2 H e.toMonoidHom e.injective]
  exact fun hb => hH.1 (((H.pCoreIn 2).map_eq_bot_iff_of_injective e.injective).mp hb)

/-- Transport a Sylow subgroup with its ambient image, without changing the
intrinsic subgroup inclusion used by the source statements. -/
theorem sylow_image_map_equiv (e : G ≃* G) {H U : Subgroup G}
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U) :
    ∃ Q : Sylow 2 (H.map e.toMonoidHom),
      (Q : Subgroup (H.map e.toMonoidHom)).map (H.map e.toMonoidHom).subtype = U.map e.toMonoidHom := by
  let eH := equivMapOfInjective H e.toMonoidHom e.injective
  let Q : Sylow 2 (H.map e.toMonoidHom) := P.mapSurjective (f := eH.toMonoidHom) eH.surjective
  refine ⟨Q, ?_⟩
  change ((P : Subgroup H).map eH.toMonoidHom).map (H.map e.toMonoidHom).subtype = _
  rw [Subgroup.map_map, ← hP, Subgroup.map_map]
  rfl

omit [Finite G] in
private theorem map_inverse_cancel (e : G ≃* G) (H : Subgroup G) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  rw [he, Subgroup.map_id]

/-- The maximal-choice consequence is invariant under conjugation. Thus the
larger Sylow subgroup remains Sylow in every subsequent `H`-overgroup after
it is moved into the specified `T`. -/
theorem overgroup_sylow_property_map_equiv (e : G ≃* G) {I₀ U : Subgroup G}
    (h : ∀ H ∈ Chapter1.HOver G (I₀ : Set G),
      ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = U) :
    ∀ H ∈ Chapter1.HOver G (I₀.map e.toMonoidHom : Set G),
      ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = U.map e.toMonoidHom := by
  intro H hH
  have hback := HOver_map_equiv e.symm hH
  rw [map_inverse_cancel] at hback
  obtain ⟨P, hP⟩ := h _ hback
  have hforward := sylow_image_map_equiv e P hP
  rw [show (H.map e.symm.toMonoidHom).map e.toMonoidHom = H from
    map_inverse_cancel e.symm H] at hforward
  exact hforward


/-- The corrected first paragraph of the 15.4.20 contradiction. Maximize the
Sylow order before conjugating. The resulting larger subgroup lies properly
inside `T`, has both indices two, moves a factor, and remains Sylow in the
normalizer of the intrinsic two-core. The two printed occurrences of `T₀`
in that normalizer assertion are therefore replaced by this `U`. -/
theorem exists_placed_maximal_sylow_counterexample
    (d : Source.Geometry G)
    (hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀)
    (hM₁ : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M₁)
    (hM₂ : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M₂)
    (hnX : ∀ i, d.T₀ ≤ normalizer (d.X i : Set G))
    (hnY : ∀ j, d.T₀ ≤ normalizer (d.Y j : Set G))
    (hpermX : ∀ g ∈ d.M₁, ∃ σ : Equiv.Perm Bool,
      ∀ i, (d.X i).map (MulAut.conj g).toMonoidHom = d.X (σ i))
    (hpermY : ∀ g ∈ d.M₂, ∃ τ : Equiv.Perm Bool,
      ∀ j, (d.Y j).map (MulAut.conj g).toMonoidHom = d.Y (τ j))
    (hNX : ∀ i, (d.T : Subgroup G) ⊓ normalizer (d.X i : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.X false : Set G))
    (hNY : ∀ j, (d.T : Subgroup G) ⊓ normalizer (d.Y j : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G))
    (hindex : d.T₀.relIndex (d.T : Subgroup G) ≤ 4)
    (hXgen : ∀ i, d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G))
    (hYgen : ∀ j, d.Y j ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂)
    (hne : d.M₁ ≠ d.M₂)
    (hfail : ∃ i j, ∃ H ∈ Chapter1.HOver G (d.I i j : Set G),
      ¬ ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = d.T₀) :
    ∃ i j, ∃ I₀ ∈ Chapter1.HOver G (d.I i j : Set G), ∃ U : Subgroup G,
      d.T₀ < U ∧ U < (d.T : Subgroup G) ∧ U ≤ I₀ ∧ IsPGroup 2 U ∧
      (∃ P : Sylow 2 I₀, (P : Subgroup I₀).map I₀.subtype = U) ∧
      (∀ H ∈ Chapter1.HOver G (d.I i j : Set G), ∀ P : Sylow 2 H,
        Nat.card ((P : Subgroup H).map H.subtype) ≤ Nat.card U) ∧
      (∀ H ∈ Chapter1.HOver G (I₀ : Set G),
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = U) ∧
      (∃ P : Sylow 2 (normalizer (I₀.pCoreIn 2 : Set G)),
        (P : Subgroup (normalizer (I₀.pCoreIn 2 : Set G))).map
          (normalizer (I₀.pCoreIn 2 : Set G)).subtype = U) ∧
      U.relIndex (d.T : Subgroup G) = 2 ∧ d.T₀.relIndex U = 2 ∧
      (¬ U ≤ normalizer (d.X i : Set G) ∨ ¬ U ≤ normalizer (d.Y j : Set G)) := by
  obtain ⟨i, j, hfail⟩ := hfail
  obtain ⟨I₀, hI₀, U, hstrict, hUI, hUp, ⟨P, hP⟩, hmax, hstable⟩ :=
    exists_maximal_sylow_counterexample (d.T.isPGroup'.to_le d.T₀_le_T) (d.T₀_le_I i j) hfail
  obtain ⟨g, _, σ, τ, hinto, hT₀, _, _, hI⟩ :=
    conjugate_two_overgroup_preserving_geometry d hS hM₁ hM₂ hnX hnY hpermX hpermY hUp hstrict.le
  let e : G ≃* G := MulAut.conj g
  let I' := I₀.map e.toMonoidHom
  let U' := U.map e.toMonoidHom
  have hI' : I' ∈ Chapter1.HOver G (d.I (σ i) (τ j) : Set G) := by
    have h := HOver_map_equiv e hI₀
    rw [hI i j] at h
    exact h
  have hstrict' : d.T₀ < U' := by
    refine lt_of_le_of_ne ((map_mono hstrict.le).trans' hT₀.ge) ?_
    intro heq
    apply hstrict.ne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact hT₀.trans heq
  have hUI' : U' ≤ I' := map_mono hUI
  have hproper : U' < (d.T : Subgroup G) := lt_of_le_of_ne hinto (by
    intro heq
    exact sylow_not_le_HOver d hXgen hYgen huniqueX huniqueY hne (σ i) (τ j) hI'
      (heq ▸ hUI'))
  have hmax' : ∀ H ∈ Chapter1.HOver G (d.I (σ i) (τ j) : Set G),
      ∀ Q : Sylow 2 H, Nat.card ((Q : Subgroup H).map H.subtype) ≤ Nat.card U' := by
    intro H hH Q
    have hback : H.map e.symm.toMonoidHom ∈ Chapter1.HOver G (d.I i j : Set G) := by
      have hh := HOver_map_equiv e.symm hH
      rw [← hI i j, map_inverse_cancel] at hh
      exact hh
    obtain ⟨Qback,hQback⟩ := sylow_image_map_equiv e.symm Q rfl
    have hh := hmax _ hback Qback
    rw [hQback, card_map_of_injective e.symm.injective] at hh
    simpa only [U', card_map_of_injective (f := e.toMonoidHom) e.injective] using hh
  have hstable' := overgroup_sylow_property_map_equiv e hstable
  obtain ⟨hi₁, hi₂⟩ := indices_two_of_intermediate hstrict' hproper hindex
  exact ⟨σ i, τ j, I', hI', U', hstrict', hproper, hUI', hUp.map e.toMonoidHom,
    sylow_image_map_equiv e P hP, hmax', hstable',
    hstable' _ (core_normalizer_mem_HOver hI'.1), hi₁, hi₂,
    larger_subgroup_moves_factor d hNX hNY hstrict' hproper.le (σ i) (τ j)⟩


/-- The placed counterexample with its established overgroup and core-normalizer
Sylow properties. The stronger variant also retains global maximality for
subsequent replacement of the local overgroup. -/
theorem exists_placed_sylow_counterexample
    (d : Source.Geometry G)
    (hS : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀)
    (hM₁ : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M₁)
    (hM₂ : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M₂)
    (hnX : ∀ i, d.T₀ ≤ normalizer (d.X i : Set G))
    (hnY : ∀ j, d.T₀ ≤ normalizer (d.Y j : Set G))
    (hpermX : ∀ g ∈ d.M₁, ∃ σ : Equiv.Perm Bool,
      ∀ i, (d.X i).map (MulAut.conj g).toMonoidHom = d.X (σ i))
    (hpermY : ∀ g ∈ d.M₂, ∃ τ : Equiv.Perm Bool,
      ∀ j, (d.Y j).map (MulAut.conj g).toMonoidHom = d.Y (τ j))
    (hNX : ∀ i, (d.T : Subgroup G) ⊓ normalizer (d.X i : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.X false : Set G))
    (hNY : ∀ j, (d.T : Subgroup G) ⊓ normalizer (d.Y j : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G))
    (hindex : d.T₀.relIndex (d.T : Subgroup G) ≤ 4)
    (hXgen : ∀ i, d.X i ⊔ (d.T : Subgroup G) = d.wholeX ⊔ (d.T : Subgroup G))
    (hYgen : ∀ j, d.Y j ⊔ (d.T : Subgroup G) = d.wholeY ⊔ (d.T : Subgroup G))
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ M → M = d.M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      d.wholeY ⊔ (d.T : Subgroup G) ≤ M → M = d.M₂)
    (hne : d.M₁ ≠ d.M₂)
    (hfail : ∃ i j, ∃ H ∈ Chapter1.HOver G (d.I i j : Set G),
      ¬ ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = d.T₀) :
    ∃ i j, ∃ I₀ ∈ Chapter1.HOver G (d.I i j : Set G), ∃ U : Subgroup G,
      d.T₀ < U ∧ U < (d.T : Subgroup G) ∧ U ≤ I₀ ∧ IsPGroup 2 U ∧
      (∃ P : Sylow 2 I₀, (P : Subgroup I₀).map I₀.subtype = U) ∧
      (∀ H ∈ Chapter1.HOver G (I₀ : Set G),
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = U) ∧
      (∃ P : Sylow 2 (normalizer (I₀.pCoreIn 2 : Set G)),
        (P : Subgroup (normalizer (I₀.pCoreIn 2 : Set G))).map
          (normalizer (I₀.pCoreIn 2 : Set G)).subtype = U) ∧
      U.relIndex (d.T : Subgroup G) = 2 ∧ d.T₀.relIndex U = 2 ∧
      (¬ U ≤ normalizer (d.X i : Set G) ∨ ¬ U ≤ normalizer (d.Y j : Set G)) := by
  obtain ⟨i,j,I₀,hI₀,U,hstrict,hproper,hUI,hUp,hP,_,hstable,hcore,hindices⟩ :=
    exists_placed_maximal_sylow_counterexample d hS hM₁ hM₂ hnX hnY hpermX hpermY
      hNX hNY hindex hXgen hYgen huniqueX huniqueY hne hfail
  exact ⟨i,j,I₀,hI₀,U,hstrict,hproper,hUI,hUp,hP,hstable,hcore,hindices⟩


omit [Finite G] in
/-- If a two-factor permutation action moves one factor, that factor's orbit
generates the whole product. This is the `X = ⟨L₁^{T_I}⟩` step, and it also
places that whole product in the contrary local overgroup. -/
theorem moved_factor_generates_whole (L : Bool → Subgroup G) {U H : Subgroup G}
    (i : Bool) (hUH : U ≤ H) (hLH : L i ≤ H)
    (hperm : ∀ u ∈ U, ∃ σ : Equiv.Perm Bool,
      ∀ k, (L k).map (MulAut.conj u).toMonoidHom = L (σ k))
    (hmove : ¬ U ≤ normalizer (L i : Set G)) :
    (⨆ u : U, (L i).map (MulAut.conj (u : G)).toMonoidHom) = L false ⊔ L true ∧
      L false ⊔ L true ≤ H := by
  classical
  have hLle (k : Bool) : L k ≤ L false ⊔ L true := by
    cases k
    · exact le_sup_left
    · exact le_sup_right
  have hex : ∃ u ∈ U, u ∉ normalizer (L i : Set G) := by
    by_contra h
    push Not at h
    exact hmove h
  obtain ⟨u, hu, hnu⟩ := hex
  obtain ⟨σ, hσ⟩ := hperm u hu
  have hσi : σ i ≠ i := by
    intro heq
    apply hnu
    rw [mem_normalizer_iff_map_conj_eq]
    exact (hσ i).trans (congrArg L heq)
  have hswap : σ i = !i := Bool.eq_not_iff.mpr hσi
  let O := ⨆ u : U, (L i).map (MulAut.conj (u : G)).toMonoidHom
  have hiO : L i ≤ O := by
    intro l hl
    exact (le_iSup (fun u : U => (L i).map (MulAut.conj (u : G)).toMonoidHom) 1)
      ⟨l, hl, by simp⟩
  have hnO : L (!i) ≤ O := by
    rw [← hswap, ← hσ i]
    exact le_iSup (fun u : U => (L i).map (MulAut.conj (u : G)).toMonoidHom) ⟨u, hu⟩
  have hOeq : O = L false ⊔ L true := by
    apply le_antisymm
    · apply iSup_le
      intro v
      obtain ⟨τ, hτ⟩ := hperm v v.property
      exact (hτ i).le.trans (hLle (τ i))
    · cases i
      · exact sup_le hiO hnO
      · exact sup_le hnO hiO
  refine ⟨hOeq, ?_⟩
  rw [← hOeq]
  apply iSup_le
  intro v
  rintro x ⟨l, hl, rfl⟩
  exact H.mul_mem (H.mul_mem (hUH v.property) (hLH hl)) (H.inv_mem (hUH v.property))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
