module
public import Theory.GroupTheory.ReducedNormal.Representation
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms
/-!
# Literal subgroup coordinates for a reduced binary subspace

The original ambient inclusion identifies a binary subspace of R₂(H)
with the additive group of its actual subgroup of G. Under invariance,
this identification intertwines the original H-conjugation actions.
Fixed vectors are exactly relative centralizer elements. The actual
centralizer quotient projection has that fixed space as its kernel,
so its first-isomorphism map gives canonical quotient coordinates,
with the original conjugation formula on every quotient representative.

Source: Aschbacher–Smith, Lemmas D.3.4(3) and 3.2.2(3), combined
manuscript of 1 March 2004, printed pp.193 and 579.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] (H : Subgroup G)
  (W : Submodule (ZMod 2) (Additive (ModuleGroup H)))

instance subspaceImage_elementary_instance : IsElementaryAbelian 2 (subspaceImage H W) :=
  subspaceImage_elementary H W

/-- The original inclusion, with its codomain restricted to its ambient image. -/
noncomputable def subspaceLinearMap : W →ₗ[ZMod 2] Additive (subspaceImage H W) :=
  ({ toFun v := Additive.ofMul ⟨v.val.toMul.val.val,
       ⟨_, ⟨v.val.toMul, v.property, rfl⟩, rfl⟩⟩
     map_zero' := rfl
     map_add' := fun _ _ => rfl } : W →+ Additive (subspaceImage H W)).toZModLinearMap 2

theorem subspaceLinearMap_bijective : Function.Bijective (subspaceLinearMap H W) := by
  constructor
  · intro v w he
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : Additive (subspaceImage H W) => u.toMul.val) he
  · intro u
    obtain ⟨_, ⟨v, hv, rfl⟩, he⟩ := u.toMul.property
    refine ⟨⟨Additive.ofMul v, hv⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext he

/-- The subspace and its actual subgroup of G have the same binary coordinates. -/
noncomputable def subspaceEquiv : W ≃ₗ[ZMod 2] Additive (subspaceImage H W) :=
  LinearEquiv.ofBijective _ (subspaceLinearMap_bijective H W)

@[simp] theorem subspaceEquiv_apply (w : W) :
    ((subspaceEquiv H W w).toMul : G) = w.val.toMul.val.val := rfl

abbrev subspaceSubrepresentation
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W) :
    Subrepresentation (representation H) :=
  ⟨W, fun h _ hw => (hW (mem_top h) _).mpr hw⟩

theorem subspaceImage_normalized
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W) :
    H ≤ normalizer (subspaceImage H W : Set G) := by
  apply subspaceImage_normalizes H H le_rfl W
  rwa [subgroupOf_self]

/-- The original H-conjugation action on the actual ambient subgroup. -/
def subspaceConjugation
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W) :
    H →* MulAut (subspaceImage H W) :=
  (subspaceImage H W).normalizerMonoidHom.comp
    (inclusion (subspaceImage_normalized H W hW))

noncomputable def subspaceRepresentation
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W) :
    Representation (ZMod 2) H (Additive (subspaceImage H W)) :=
  Representation.elementaryRepresentation (subspaceConjugation H W hW)

theorem subspaceEquiv_equivariant
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (h : H) (w : W) :
    subspaceEquiv H W ((subspaceSubrepresentation H W hW).toRepresentation h w) =
      subspaceRepresentation H W hW h (subspaceEquiv H W w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

theorem subspaceRepresentation_apply
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (h : H) (w : Additive (subspaceImage H W)) :
    ((subspaceRepresentation H W hW h w).toMul : G) =
      (h : G) * (w.toMul : G) * (h : G)⁻¹ := rfl

/-- Fixed vectors are precisely the original relative centralizer. -/
theorem mem_subspace_fixedSpace_iff
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) (w : Additive (subspaceImage H W)) :
    w ∈ fixedSpace (subspaceRepresentation H W hW) (X.subgroupOf H) ↔
      (w.toMul : G) ∈ centralizer (X : Set G) := by
  constructor
  · intro hw x hx
    have he := congrArg (fun u : Additive (subspaceImage H W) => u.toMul.val)
      (hw ⟨⟨x, hXH hx⟩, hx⟩)
    change x * (w.toMul : G) * x⁻¹ = w.toMul at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hw x
    apply Additive.toMul.injective
    apply Subtype.ext
    change x.val.val * (w.toMul : G) * x.val.val⁻¹ = w.toMul
    rw [hw x.val.val x.property, mul_inv_cancel_right]

/-- The literal centralizer inside the original ambient image. -/
abbrev subspaceCentralizer (X : Subgroup G) : Subgroup (subspaceImage H W) :=
  (centralizer (X : Set G)).subgroupOf (subspaceImage H W)

/-- The original quotient projection, regarded as a binary linear map. -/
noncomputable def centralizerProjection (X : Subgroup G) :
    Additive (subspaceImage H W) →ₗ[ZMod 2]
      Additive ((subspaceImage H W) ⧸ subspaceCentralizer H W X) :=
  (QuotientGroup.mk' (subspaceCentralizer H W X)).toAdditive.toZModLinearMap 2

theorem centralizerProjection_surjective (X : Subgroup G) :
    Function.Surjective (centralizerProjection H W X) := by
  intro v
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (subspaceCentralizer H W X) v.toMul
  exact ⟨Additive.ofMul u, hu⟩

theorem centralizerProjection_ker
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) :
    (centralizerProjection H W X).ker =
      fixedSpace (subspaceRepresentation H W hW) (X.subgroupOf H) := by
  ext w
  change QuotientGroup.mk' (subspaceCentralizer H W X) w.toMul = 1 ↔ _
  exact (QuotientGroup.eq_one_iff w.toMul).trans
    (mem_subspace_fixedSpace_iff H W hW X hXH w).symm

/-- The fixed-space quotient is the actual ambient centralizer quotient. -/
noncomputable def fixedSpaceQuotientEquiv
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) :
    (Additive (subspaceImage H W) ⧸
      fixedSpace (subspaceRepresentation H W hW) (X.subgroupOf H)) ≃ₗ[ZMod 2]
      Additive ((subspaceImage H W) ⧸ subspaceCentralizer H W X) :=
  (Submodule.quotEquivOfEq _ _ (centralizerProjection_ker H W hW X hXH).symm).trans
    ((centralizerProjection H W X).quotKerEquivOfSurjective
      (centralizerProjection_surjective H W X))

@[simp] theorem fixedSpaceQuotientEquiv_mk
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) (w : Additive (subspaceImage H W)) :
    fixedSpaceQuotientEquiv H W hW X hXH (Submodule.Quotient.mk w) =
      Additive.ofMul (QuotientGroup.mk' (subspaceCentralizer H W X) w.toMul) := rfl

/-- Conjugation on the literal centralizer quotient, through its canonical
quotient coordinates. The next formula specifies the original quotient action. -/
noncomputable def centralizerQuotientRepresentation
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) :
    Representation (ZMod 2) (X.subgroupOf H)
      (Additive ((subspaceImage H W) ⧸ subspaceCentralizer H W X)) :=
  (fixedSpaceQuotientEquiv H W hW X hXH).conjRingEquiv.toMonoidHom.comp
    (fixedQuotientRepresentation (subspaceRepresentation H W hW) (X.subgroupOf H))

theorem centralizerQuotientRepresentation_mk
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) (x : X.subgroupOf H) (u : subspaceImage H W) :
    centralizerQuotientRepresentation H W hW X hXH x
      (Additive.ofMul (QuotientGroup.mk' (subspaceCentralizer H W X) u)) =
        Additive.ofMul (QuotientGroup.mk' (subspaceCentralizer H W X)
          (subspaceConjugation H W hW x.val u)) := by
  let e := fixedSpaceQuotientEquiv H W hW X hXH
  change e ((fixedQuotientRepresentation (subspaceRepresentation H W hW)
    (X.subgroupOf H)) x (e.symm (e (Submodule.Quotient.mk (Additive.ofMul u))))) = _
  rw [e.symm_apply_apply]
  rfl

end Theory.GroupTheory.ReducedNormal
