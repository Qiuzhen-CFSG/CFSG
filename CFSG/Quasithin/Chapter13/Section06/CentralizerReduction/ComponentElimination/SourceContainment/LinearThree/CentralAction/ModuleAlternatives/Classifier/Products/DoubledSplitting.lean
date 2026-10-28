module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.Selection
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Generation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Doubled.SeedGeneration
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.Representation.NormalInvariants
public import Theory.Representation.GeneralLinearNatural
public import Theory.GroupTheory.PrimeRankCubeFree

/-!
# Recovering the doubled component module from the fixed quotient

The complementary quotient images and perfectness of C force the opposite
space to be fixed by C. The actual product inclusions then show that the
complementary factor fixes [V,C]. Consequently the faithful C-action on
[V,C] is offender-generated. Its order-168 model supplies strong quasithinness;
the original SQTK cover supplies the unchanged K-group hypothesis.

Apply the full B.5.1 implication to this actual restricted action. Perfectness
makes its moved space the whole space. The universal row extraction leaves a
natural central quotient or a doubled whole module. The former would map a
three-dimensional quotient onto the given six-dimensional image, which is
impossible. In the latter case the fixed quotient map is a surjection between
six-dimensional spaces, hence an isomorphism. Composing it with the supplied
coordinates preserves one actor equivalence for both copies.

The only earlier-source premises are the authorized full B.5.1 implication
and universal row extraction. Their final discharge belongs to the classifier
assembly; no splitting or offender generation on C is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1,
printed pp.99–103; B.5.6(3b), p.105; and 13.6.20, p.931 (PDF p.948).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.DoubledSplitting
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

private theorem other_moved_le (c : SelectedTwoFactorCase ρ C) :
    moved ρ c.other ≤ c.otherSpace.toSubmodule := by
  cases c.otherCase with
  | natural h _ => exact h.ge
  | doubleNatural _ _ h _ => exact h.ge
  | exceptional h _ => exact h

private theorem other_fixed (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C) :
    c.otherSpace.toSubmodule ≤ fixedSpace ρ C := by
  let : IsQuasisimple C := component_quasisimple e
  apply le_fixedSpace_of_commutator_le_fixedSpace ρ C _
    (le_subspaceStabilizer ρ _ (fun g _ v hv => c.otherSpace.apply_mem_toSubmodule g hv))
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, hv, rfl⟩
  have hU : ρ g v - v ∈ c.space.toSubmodule := by
    rw [hm]
    exact Submodule.subset_span ⟨g, hg, v, Submodule.mem_top, rfl⟩
  have hW := c.otherSpace.toSubmodule.sub_mem (c.otherSpace.apply_mem_toSubmodule g hv) hv
  have hz : ρ.invariants.mkQ (ρ g v - v) = 0 :=
    (disjoint_iff.mp c.decomposition.disjoint).le ⟨⟨_, hU, rfl⟩, ⟨_, hW, rfl⟩⟩
  have hi := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact fun g => hi g

private theorem product_commute (c : SelectedTwoFactorCase ρ C) (g : C) (b : c.other) :
    (g : D) * b = (b : D) * g := by
  have h := (swapProduct c.product).apply_eq b g
  change c.product.equiv (g, b) = (b : D) * g at h
  exact (c.product.apply_eq g b).symm.trans h

/-- The other factor centralizes the original selected moved space. -/
theorem space_fixed (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C) :
    c.space.toSubmodule ≤ fixedSpace ρ c.other := by
  rw [hm]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, _, rfl⟩ b
  have hv : ρ b v - v ∈ c.otherSpace.toSubmodule :=
    other_moved_le c (Submodule.subset_span ⟨b, b.property, v, Submodule.mem_top, rfl⟩)
  have h := other_fixed e c hm hv ⟨g, hg⟩
  have hc : ρ g (ρ b v) = ρ b (ρ g v) := by
    change (ρ g * ρ b) v = (ρ b * ρ g) v
    rw [← map_mul, ← map_mul, product_commute c ⟨g, hg⟩ b]
  change ρ g (ρ b v - v) = ρ b v - v at h
  rw [map_sub, hc] at h
  change ρ b (ρ g v - v) = ρ g v - v
  rw [map_sub]
  exact sub_eq_sub_iff_add_eq_add.mpr
    ((sub_eq_sub_iff_add_eq_add.mp h).trans (add_comm _ _))

-- To append to Probe.lean after public import preparation finishes.
/-- Perfectness generates the whole selected space under its restricted action. -/
theorem space_moved (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C) :
    moved (c.space.toRepresentation.comp C.subtype) ⊤ = ⊤ := by
  let : IsQuasisimple C := component_quasisimple e
  have hi := ComponentReduction.PreliminaryActions.perfect_seed_idempotent ρ C ⊤
    (le_subspaceStabilizer ρ ⊤ (by simp))
  apply Submodule.map_injective_of_injective c.space.toSubmodule.subtype_injective
  rw [Submodule.map_top, Submodule.range_subtype]
  apply le_antisymm (Submodule.map_subtype_le _ _)
  conv_lhs => rw [hm]; unfold moved; rw [← hi]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, hv, rfl⟩
  have hv' : v ∈ c.space.toSubmodule := hm.symm ▸ hv
  exact ⟨c.space.toRepresentation g ⟨v, hv'⟩ - ⟨v, hv'⟩,
    Submodule.subset_span ⟨⟨g, hg⟩, mem_top _, ⟨v, hv'⟩, Submodule.mem_top, rfl⟩, rfl⟩

/-- The literal quotient map onto the selected image modulo C_V(D). -/
noncomputable def imageMap (c : SelectedTwoFactorCase ρ C) :
    c.space.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage c.space).toSubmodule where
  toFun v := ⟨ρ.invariants.mkQ v, ⟨v, v.property, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The quotient image is the range of the literal restricted quotient map. -/
theorem imageMap_surjective (c : SelectedTwoFactorCase ρ C) :
    Function.Surjective (imageMap c) := by
  rintro ⟨q, v, hv, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩

/-- Component-fixed vectors in the moved space are globally fixed. -/
theorem imageMap_fixed (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C)
    (v : c.space.toSubmodule)
    (hv : v ∈ Representation.invariants (c.space.toRepresentation.comp C.subtype)) :
    imageMap c v = 0 := by
  apply Subtype.ext
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  intro g
  obtain ⟨a, b, rfl⟩ := c.product.exists_mul g
  have hb : ρ b (v : V) = v := space_fixed e c hm v.property b
  rw [map_mul, Module.End.mul_apply, hb]
  exact congrArg Subtype.val (hv a)

/-- Faithfulness of the doubled quotient lifts to the original moved space. -/
theorem space_faithful (c : SelectedTwoFactorCase ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2)) :
    Function.Injective (c.space.toRepresentation.comp C.subtype) := by
  intro g h he
  apply a.groupEquiv.injective
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  have hi (q : ((fixed ρ).quotientImage c.space).toSubmodule) :
      ((fixed ρ).quotientImage c.space).toRepresentation g q =
        ((fixed ρ).quotientImage c.space).toRepresentation h q := by
    obtain ⟨w, rfl⟩ := imageMap_surjective c q
    exact congrArg (imageMap c) (LinearMap.congr_fun he w)
  obtain ⟨q, hq⟩ := a.linearEquiv.surjective (fun _ => v)
  have h' := (a.intertwines g q).symm.trans
    ((congrArg a.linearEquiv (hi q)).trans (a.intertwines h q))
  rw [hq] at h'
  exact congrFun h' 0

private theorem component_stronglyQuasithin [Finite D] (e : C ≃* Matrix.PSL3Two.PSL) :
    IsStronglyQuasithin C := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_PSL]
  intro hd
  have hpd : p ∣ 2 ^ 3 * 3 * 7 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  rcases hp.dvd_mul.mp hpd with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have he : p = 2 := (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one
      subst p
      exact ho.not_two_dvd_nat (dvd_refl 2)
    · have he : p = 3 := (Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one
      subst p
      norm_num at hd
  · have he : p = 7 := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp h |>.resolve_left hp.ne_one
    subst p
    norm_num at hd

/-- All B.5.1 hypotheses hold on the literal component action, with the original K. -/
theorem space_hypothesis [Finite D] {𝒦 : GroupClass.{u}}
    (hyp : FFHypothesis 𝒦 ρ) (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2)) :
    QuasisimpleSourceHypothesis (c.space.toRepresentation.comp C.subtype) 𝒦 ⊤ := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  let : IsQuasisimple C := component_quasisimple e
  have hf := space_faithful c a
  have hgen := second_generated ρ (swapProduct c.product) c.space
    (space_fixed e c hm) hf hyp.generated
  have hs : IsSQTK 𝒦 C := by
    obtain ⟨q⟩ := hyp.quotient
    exact ⟨component_stronglyQuasithin e,
      ((IsKGroup.equiv q.equiv).mp (q.sqtk.isKGroup.quotient q.kernel)).subgroup C⟩
  exact {
    finite_module := inferInstance
    faithful := hf
    quasisimple := IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
    sqtk := (IsSQTK.equiv Subgroup.topEquiv.symm).mp hs
    fitting := by rw [generalizedFitting_eq_top_of_quasisimple, top_sup_eq]
    twoCore := (swapProduct c.product).second_twoCore hyp.twoCore
    generated := hgen }

private theorem image_dimension (c : SelectedTwoFactorCase ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2)) :
    Module.finrank (ZMod 2) ((fixed ρ).quotientImage c.space).toSubmodule = 6 := by
  rw [a.linearEquiv.finrank_eq]
  simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_pi_fintype]

private theorem natural_impossible [Module.Finite (ZMod 2) V]
    (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2))
    (s : MovedSection (c.space.toRepresentation.comp C.subtype) ⊤)
    (b : ActionEquiv (s.action.comp (⊤ : Subgroup C).subtype) BinaryLinearThree.W) : False := by
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans (space_moved e c hm)
  let f := (imageMap c).comp s.space.toSubmodule.subtype
  have hk : s.central.toSubmodule ≤ f.ker := by
    intro v hv
    rw [s.central_eq] at hv
    apply imageMap_fixed e c hm
    intro g
    exact congrArg Subtype.val (hv ⟨g, mem_top _⟩)
  let q := s.central.toSubmodule.liftQ f hk
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨w, hw⟩ := imageMap_surjective c v
    have hw' : w ∈ s.space.toSubmodule := hs ▸ Submodule.mem_top
    exact ⟨s.central.toSubmodule.mkQ ⟨w, hw'⟩, hw⟩
  have hd := LinearMap.finrank_le_finrank_of_surjective hq
  have hb : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 3 := by
    rw [b.linearEquiv.finrank_eq]
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]
  rw [image_dimension c a, hb] at hd
  omega

/-- The fixed quotient map on the selected moved space is bijective. Its
surjectivity is literal; B.5.1 excludes the natural row and bounds the domain
by six, the dimension already attained by the given doubled quotient. -/
theorem imageMap_bijective [Finite D] {𝒦 : GroupClass.{u}}
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} 𝒦)
    (rows : QuasisimpleRowExtraction.{u,v})
    (hyp : FFHypothesis 𝒦 ρ) (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2)) : Function.Bijective (imageMap c) := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  obtain ⟨h⟩ := earlier C c.space.toSubmodule (c.space.toRepresentation.comp C.subtype) ⊤
    (space_hypothesis hyp e c hm a)
  have hc := rows C c.space.toSubmodule (c.space.toRepresentation.comp C.subtype) ⊤
    (Subgroup.topEquiv.trans e) h
  cases hc with
  | natural s _ b => exact (natural_impossible e c hm a s b).elim
  | doubled s b =>
    have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans (space_moved e c hm)
    have hd : Module.finrank (ZMod 2) c.space.toSubmodule = 6 := by
      have hb := b.linearEquiv.finrank_eq
      rw [hs, finrank_top] at hb
      simpa [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_pi_fintype] using hb
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (image_dimension c a).symm)).mpr (imageMap_surjective c), imageMap_surjective c⟩

/-- Recover the original whole moved-space representation, with the same
actor isomorphism controlling both coordinates of the supplied quotient. -/
theorem exists_doubled_section [Finite D] [C.Normal] {𝒦 : GroupClass.{u}}
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} 𝒦)
    (rows : QuasisimpleRowExtraction.{u,v})
    (hyp : FFHypothesis 𝒦 ρ) (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2)) :
    ∃ s : MovedSection ρ C, Nonempty (ActionEquiv
      (s.space.toRepresentation.comp C.subtype) (repeated BinaryLinearThree.W 2)) := by
  let s : MovedSection ρ C := ⟨c.space, hm,
    fixedSubrepresentationOfNormal c.space.toRepresentation C, rfl⟩
  let f := LinearEquiv.ofBijective (imageMap c) (imageMap_bijective earlier rows hyp e c hm a)
  refine ⟨s, ⟨⟨a.groupEquiv, f.trans a.linearEquiv, ?_⟩⟩⟩
  intro g v
  exact a.intertwines g (imageMap c v)

/-- The doubled B.5.6(3b) branch gives the doubled alternative in 13.6.20. -/
theorem selected_doubled [Finite D] [C.Normal] {𝒦 : GroupClass.{u}}
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,v} 𝒦)
    (rows : QuasisimpleRowExtraction.{u,v})
    (hyp : FFHypothesis 𝒦 ρ) (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2)) : LinearThreeModuleCase ρ C := by
  obtain ⟨s, ⟨b⟩⟩ := exists_doubled_section earlier rows hyp e c hm a
  exact .doubled s b

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.DoubledSplitting
