module

public import Theory.PGroupCore
public import Theory.GroupTheory.PermutationWreathEmbedding
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Quotient and action transports for the swapped `L₃(2)` branch

The two-block action gives an isomorphism from the literal quotient by
`O₂(H₁)` to `S₃ ≀ C₂`, provided its kernel and image order have been computed.
Conjugation on `L₁/O₂(L₁)` restricts along actual subgroup inclusions, giving
the image inclusion used in the final order-four/order-eight contradiction.

These are intermediate transports for Aschbacher--Smith 13.8.16(1), printed
p.952 (PDF p.969). They do not construct the source solvable subgroup `H₁`,
identify `L₁` with its two-residual, prove the three-rank restriction, or
compute the source automizers. Those obligations remain with the branch
assembly; the abstract image contradiction alone does not prove 13.8.16.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree

public abbrev C2 := Multiplicative (ZMod 2)

/-- The concrete `S₃ ≀ C₂` carrier used for the two-block action. -/
public abbrev S3Wreath := RegularWreathProduct (Equiv.Perm (Fin 3)) C2

/-- The elementary four and dihedral-eight carriers used for the two
automizer images. -/
public abbrev E4 := Fin 2 → C2
public abbrev D8 := DihedralGroup 4

section WreathQuotient

variable {H₁ : Type*} [Group H₁]

/-- Data for the *actual* two-block action on the six points.  The kernel is
recorded as the intrinsic two-core and the final cardinality is an arithmetic
consequence to be proved by the source assembly.  No quotient isomorphism or
wreath structure is assumed in this record. -/
public structure TwoBlockQuotientData where
  X : Type*
  action : H₁ →* Equiv.Perm X
  labels : X ≃ (Fin 3 × C2)
  block_preserved : ∀ a : H₁, ∃ q : C2, ∀ x : X,
    (labels (action a x)).2 = q * (labels x).2
  kernel_eq_core : action.ker = pCore 2 H₁
  quotient_card : Nat.card (H₁ ⧸ pCore 2 H₁) = Nat.card S3Wreath

namespace TwoBlockQuotientData

/-- The quotient of the actual action is the concrete regular wreath product.
The proof first embeds the action image in the wreath product, then uses the
kernel equality and the supplied order calculation to upgrade the embedding
to an isomorphism. -/
public noncomputable def quotientEquiv (d : TwoBlockQuotientData (H₁ := H₁))
    : H₁ ⧸ pCore 2 H₁ ≃* S3Wreath := by
  let hex := RegularWreathProduct.exists_embedding_range_of_two_blocks d.action d.labels
      d.block_preserved
  let f := Classical.choose hex
  have hf : Function.Injective f := Classical.choose_spec hex
  let esl := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  let ew : RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) C2 ≃*
      S3Wreath :=
    RegularWreathProduct.congr esl (MulEquiv.refl C2)
  let f' : d.action.range →* S3Wreath := ew.toMonoidHom.comp f
  have hf' : Function.Injective f' := ew.injective.comp hf
  let efull : H₁ ⧸ pCore 2 H₁ ≃* d.action.range :=
    (QuotientGroup.quotientMulEquivOfEq d.kernel_eq_core.symm).trans
      (QuotientGroup.quotientKerEquivRange d.action)
  let φ : H₁ ⧸ pCore 2 H₁ →* S3Wreath := f'.comp efull.toMonoidHom
  have hφ : Function.Injective φ := hf'.comp efull.injective
  apply MulEquiv.ofBijective φ
  exact (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφ, d.quotient_card⟩

end TwoBlockQuotientData

end WreathQuotient

section AutomizerContradiction

variable {A M J : Type*} [Group A] [Group M] [Group J]

/-- The image of a restricted group action is contained in the original image. -/
theorem range_le_of_restricted_action
    (αM : M →* MulAut A) (αJ : J →* MulAut A) (ι : J →* M)
    (hrestrict : αJ = αM.comp ι) :
    αJ.range ≤ αM.range := by
  intro x hx
  rcases hx with ⟨j, rfl⟩
  refine ⟨ι j, ?_⟩
  simpa using congrArg (fun f : J →* MulAut A => f j) hrestrict.symm

/-- The terminal order obstruction for two compatible actions. The source
assembly must construct both image isomorphisms before applying this lemma. -/
public theorem no_restricted_e4_dihedral_images
    (αM : M →* MulAut A) (αJ : J →* MulAut A) (ι : J →* M)
    (hrestrict : αJ = αM.comp ι)
    (hM : Nonempty (αM.range ≃* E4))
    (hJ : Nonempty (αJ.range ≃* D8)) : False := by
  obtain ⟨eM⟩ := hM
  obtain ⟨eJ⟩ := hJ
  have hfinM : Finite αM.range := Finite.of_injective eM.toEquiv eM.injective
  have hle : Nat.card αJ.range ≤ Nat.card αM.range := by
    let hrange : αJ.range ≤ αM.range := range_le_of_restricted_action αM αJ ι hrestrict
    let f : αJ.range → αM.range := fun x => ⟨x, hrange x.property⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hxy
    exact @Nat.card_le_card_of_injective _ _ hfinM f hf
  have hMcard : Nat.card αM.range = 4 := by
    rw [Nat.card_congr eM.toEquiv]
    simp [E4, C2]
  have hJcard : Nat.card αJ.range = 8 := by
    rw [Nat.card_congr eJ.toEquiv, DihedralGroup.nat_card]
  rw [hJcard, hMcard] at hle
  omega

end AutomizerContradiction

section LiteralActions
variable {G : Type*} [Group G]

/-- Literal conjugation on the intrinsic two-core quotient of `L₁`. -/
noncomputable def quotientAction (L₁ M : Subgroup G)
    (hn : M ≤ normalizer (L₁ : Set G)) : M →* MulAut (L₁ ⧸ pCore 2 L₁) :=
  (quotientAut (pCore 2 L₁)).comp
    (L₁.normalizerMonoidHom.comp (inclusion hn))

/-- The action on a quotient representative is induced by conjugation in `G`. -/
theorem quotientAction_mk (L₁ M : Subgroup G)
    (hn : M ≤ normalizer (L₁ : Set G)) (m : M) (l : L₁) :
    quotientAction L₁ M hn m (QuotientGroup.mk' (pCore 2 L₁) l) =
      QuotientGroup.mk' (pCore 2 L₁) (L₁.normalizerMonoidHom (inclusion hn m) l) :=
  quotientAut_apply_mk _ _ _

/-- Actual subgroup containment forces containment of the induced automizers;
no compatibility hypothesis on independently chosen actions is needed. -/
theorem quotientAction_range_mono (L₁ J M : Subgroup G) (hJM : J ≤ M)
    (hn : M ≤ normalizer (L₁ : Set G)) :
    (quotientAction L₁ J (hJM.trans hn)).range ≤ (quotientAction L₁ M hn).range := by
  apply range_le_of_restricted_action _ _ (inclusion hJM)
  rfl

/-- The conventional `Aut_M(L₁/O₂(L₁))` action has domain `N_M(L₁)`.
The whole group `M` need not normalize its marked parabolic `L₁`. -/
noncomputable def automizerAction (L₁ M : Subgroup G) :
    (M ⊓ normalizer (L₁ : Set G) : Subgroup G) →* MulAut (L₁ ⧸ pCore 2 L₁) :=
  quotientAction L₁ (M ⊓ normalizer (L₁ : Set G)) inf_le_right

/-- Automizers of the same literal section are monotone in the actor. -/
theorem automizer_image_mono (L₁ J M : Subgroup G) (hJM : J ≤ M) :
    (automizerAction L₁ J).range ≤ (automizerAction L₁ M).range :=
  quotientAction_range_mono L₁ _ _ (inf_le_inf_right _ hJM) inf_le_right

/-- The actual induced image for `H ∩ M` lies in the induced image for `M`. -/
theorem overlap_automizer_image_le (L₁ H M : Subgroup G) :
    (automizerAction L₁ (H ⊓ M)).range ≤ (automizerAction L₁ M).range :=
  automizer_image_mono L₁ (H ⊓ M) M inf_le_right

end LiteralActions


end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree

end
