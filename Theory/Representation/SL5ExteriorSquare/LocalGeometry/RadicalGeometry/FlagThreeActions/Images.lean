module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FlagThreeActions.Geometry

/-!
# Genuine images on the flag three-spaces

We conjugate the actual restricted action image by the explicit exterior chart.
Faithfulness lets the upper-unitriangular calculation bound its binary rank.
Displacements in these coordinates map to the literal ambient commutator.
The pointwise kernel has relative index equal to the image cardinality, so the
small-index fixed-space equality gives the A₃ centralizations and the A₂
noncentral rank-two alternatives.

Source: Aschbacher--Smith 12.5.7/10, printed pp.820--821; E.3.8, printed p.232.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare.FlagThreeActions
open SL5TenDimensional
open BinaryOffender

/-- Relative index of the literal pointwise kernel equals the genuine image order. -/
lemma kernel_relIndex_eq_card_image {G U : Type*} [Group G] [AddCommGroup U]
    [Module (ZMod 2) U] (ρ : Representation (ZMod 2) G U) (W : Submodule (ZMod 2) U)
    (A : Subgroup G) (hA : A ≤ BinaryOffender.subspaceStabilizer ρ W) :
    (subspaceKernel ρ W A).relIndex A = Nat.card (restrictedSubgroup ρ W A) := by
  rw [Subgroup.relIndex, subspaceKernel_subgroupOf_eq_ker ρ W A hA,
    Subgroup.index_ker, subgroupActionHom_range]

lemma stable (s : Bool) : flagGroup ≤ BinaryOffender.subspaceStabilizer (exteriorAction 2) (space s) := by
  apply le_subspaceStabilizer
  intro g hg w hw
  obtain ⟨v, hv⟩ := embedding_surjective s ⟨w,hw⟩
  change embedding s v = w at hv
  rw [← hv, action_embedding s hg]
  exact embedding_mem _ _

/-- The genuine image subgroup supplied by the subspace-action construction. -/
noncomputable abbrev Image (s : Bool) (A : Subgroup Group) :=
  restrictedSubgroup (exteriorAction 2) (space s) A

/-- The faithful action of the actual image, in the marked three-dimensional chart. -/
noncomputable def imageRepresentation (s : Bool) (A : Subgroup Group) :
    Representation (ZMod 2) (Image s A) Three :=
  (chart s).symm.conjRingEquiv.toMonoidHom.comp
    ((subspaceImageRepresentation (exteriorAction 2) (space s)).comp (Image s A).subtype)

lemma imageRepresentation_injective (s : Bool) (A : Subgroup Group) :
    Function.Injective (imageRepresentation s A) := by
  intro g h he
  apply Subtype.ext
  apply subspaceImageRepresentation_injective (exteriorAction 2) (space s)
  exact (chart s).symm.conjRingEquiv.injective he

lemma imageRepresentation_apply (s : Bool) (A : Subgroup Group) (x : Image s A) (v : Three) :
    imageRepresentation s A x v =
      (chart s).symm (subspaceImageRepresentation (exteriorAction 2) (space s) x (chart s v)) := rfl

lemma exists_image_upper (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup) (x : Image s A) :
    ∃ p : Three, ∀ v, imageRepresentation s A x v = upper p v := by
  rcases x with ⟨x, g, hg, rfl⟩
  refine ⟨parameters s g, ?_⟩
  intro v
  apply (chart s).injective
  apply Subtype.ext
  rw [imageRepresentation_apply, LinearEquiv.apply_symm_apply]
  exact action_embedding s (hA hg) v

/-- Upper-unitriangular coordinates selected from an actual acting representative. -/
noncomputable def imageCode (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup) : Image s A → Three :=
  fun x => (exists_image_upper s A hA x).choose

lemma imageCode_action (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup) (x : Image s A) (v : Three) :
    imageRepresentation s A x v = upper (imageCode s A hA x) v :=
  (exists_image_upper s A hA x).choose_spec v

lemma image_rank_le_two (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup)
    [IsElementaryAbelian 2 A] : rank (Image s A) ≤ 2 := by
  let : IsElementaryAbelian 2 (A.subgroupOf (BinaryOffender.subspaceStabilizer
      (exteriorAction 2) (space s))) := IsElementaryAbelian.subgroupOf (hA.trans (stable s))
  let : IsElementaryAbelian 2 (Image s A) := IsElementaryAbelian.map _
  have hc := card_le_six (imageRepresentation s A) (imageCode s A hA)
    (imageCode_action s A hA) (imageRepresentation_injective s A) (fun x => by
      simpa [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Image s A)) x)
  have hl := Nat.log_lt_of_lt_pow' (b := 2) (x := 3) (by decide) (show Nat.card (Image s A) < 2^3 by omega)
  exact Nat.le_of_lt_succ hl

lemma first_mem_commutator (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup)
    (hr : rank (Image s A) = 2) :
    basis 0 ∈ subspaceCommutator (exteriorAction 2) (space s) A := by
  let C := (subspaceCommutator (exteriorAction 2) (space s) A).comap (embedding s)
  have hC (x : Image s A) (v : Three) : imageRepresentation s A x v - v ∈ C := by
    rcases x with ⟨x,g,hg,rfl⟩
    change embedding s (imageRepresentation s A _ v - v) ∈
      subspaceCommutator (exteriorAction 2) (space s) A
    rw [map_sub]
    have he : embedding s (imageRepresentation s A
        ⟨subspaceActionHom (exteriorAction 2) (space s) g, ⟨g,hg,rfl⟩⟩ v) =
        exteriorAction 2 g (embedding s v) := by
      change ((chart s) ((chart s).symm _) : V) = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [he]
    exact Submodule.subset_span ⟨g,hg,embedding s v,embedding_mem s v,rfl⟩
  have hh := first_mem_of_rank_two (imageRepresentation s A) (imageCode s A hA)
    (imageCode_action s A hA) (imageRepresentation_injective s A) hr C hC
  change embedding s ![1,0,0] ∈ subspaceCommutator (exteriorAction 2) (space s) A at hh
  simpa [embedding] using hh

lemma line_le_commutator (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup)
    (hr : rank (Image s A) = 2) :
    V₁ ≤ subspaceCommutator (exteriorAction 2) (space s) A := by
  change Submodule.span _ _ ≤ _
  apply Submodule.span_le.mpr
  rintro v ⟨i,hi,rfl⟩
  have hi' : i = 0 := by simpa using hi
  subst i
  exact first_mem_commutator s A hA hr

lemma kernel_relIndex (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup) :
    (subspaceKernel (exteriorAction 2) (space s) A).relIndex A = Nat.card (Image s A) := by
  exact kernel_relIndex_eq_card_image (exteriorAction 2) (space s) A (hA.trans (stable s))

lemma fixed_of_image_rank_lt (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup)
    (k : ℕ) (hk : HasSmallIndexFixedSpaceProperty k A) (hr : rank (Image s A) < k) :
    space s ≤ BinaryOffender.fixedSpace (exteriorAction 2) A := by
  have he := hk (subspaceKernel (exteriorAction 2) (space s) A)
    (subspaceKernel_le _ _ _) (by rwa [kernel_relIndex s A hA])
  rw [he]
  exact le_fixedSpace_subspaceKernel _ _ _

lemma fixed_of_property_three (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup)
    [IsElementaryAbelian 2 A] (hk : HasSmallIndexFixedSpaceProperty 3 A) :
    space s ≤ BinaryOffender.fixedSpace (exteriorAction 2) A :=
  fixed_of_image_rank_lt s A hA 3 hk (by have := image_rank_le_two s A hA; omega)

lemma image_ne_bot_iff (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup) :
    Image s A ≠ ⊥ ↔ ¬ space s ≤ BinaryOffender.fixedSpace (exteriorAction 2) A := by
  constructor
  · intro hn hf
    apply hn
    apply le_antisymm _ bot_le
    rintro x ⟨g,hg,rfl⟩
    apply Subgroup.mem_bot.mpr
    apply subspaceImageRepresentation_injective (exteriorAction 2) (space s)
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact hf w.property ⟨g,hg⟩
  · exact restrictedSubgroup_ne_bot _ _ (hA.trans (stable s))

lemma rank_two_of_property_two (s : Bool) (A : Subgroup Group) (hA : A ≤ flagGroup)
    [IsElementaryAbelian 2 A] (hk : HasSmallIndexFixedSpaceProperty 2 A)
    (hn : ¬ space s ≤ BinaryOffender.fixedSpace (exteriorAction 2) A) : rank (Image s A) = 2 := by
  have hb := image_rank_le_two s A hA
  have hh : ¬ rank (Image s A) < 2 := fun h => hn (fixed_of_image_rank_lt s A hA 2 hk h)
  omega
end Representation.SL5ExteriorSquare.FlagThreeActions
