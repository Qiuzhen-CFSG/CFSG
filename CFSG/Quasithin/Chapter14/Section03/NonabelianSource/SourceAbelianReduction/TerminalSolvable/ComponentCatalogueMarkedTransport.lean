module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogue
public import CFSG.Quasithin.ChapterG.Section09.ConstituentAction

/-!
# Literal constituent-image transport for the marked component branch

A faithful component orbit remains the same group on an irreducible
constituent. Its subgroups therefore have concrete isomorphisms with their
images in Aut_HX(I), and equality of image component and image orbit lifts
to equality before quotienting. This gives ambient normality in the large
rows; normality merely inside HX would not suffice.

The same linear intertwiner descends self-duality for the fixed H-action.
Schur's lemma at the nonzero marked point also identifies C_X(I) with
C_X(H), without assuming that X acts faithfully on I. The two source
applications in ComponentCatalogueMarked use these exact quotient maps.

Source: Aschbacher--Smith, G.10.15(I), G.11.7 and the paragraph preceding
G.11.8, printed pp.361,366--368; original 14.3.15, printed p.994.
These are transport theorems, not an exhaustive component classification.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

/-- Recognition on the faithful constituent image retains the equality of
its component with the entire normal component orbit in the large rows. -/
def ComponentOrbitImageCases {D : Type*} [Group D] (L H : Subgroup D) : Prop :=
  (H = L ∧ ExcludedComponentImage L) ∨ SmallComponentImage L ∨
  (H = L ∧ Nonempty (L ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)))

namespace MarkedAction
variable {D W : Type*} [Group D] [AddCommGroup W]
  [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H X : Subgroup D)
  (I : Submodule (ZMod 2) W) (hH : H ≤ subspaceStabilizer ρ I)
  (hX : X ≤ subspaceStabilizer ρ I)

abbrev action := ChapterG.Section09.constituentAction ρ H X I hH hX
abbrev quotient := (H ⊔ X : Subgroup D) ⧸ (action ρ H X I hH hX).ker
abbrev projection : (H ⊔ X : Subgroup D) →* quotient ρ H X I hH hX :=
  QuotientGroup.mk' (action ρ H X I hH hX).ker
abbrev image (J : Subgroup D) : Subgroup (quotient ρ H X I hH hX) :=
  (J.subgroupOf (H ⊔ X)).map (projection ρ H X I hH hX)

variable (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)

/-- The constituent quotient is injective on its original component orbit. -/
theorem projection_injective_on_orbit (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation) (a b : H)
    (he : projection ρ H X I hH hX ⟨a,(show H ≤ H ⊔ X from le_sup_left) a.property⟩ =
      projection ρ H X I hH hX ⟨b,(show H ≤ H ⊔ X from le_sup_left) b.property⟩) : a = b := by
  apply hfH
  exact congrArg (kerRepresentation (action ρ H X I hH hX)) he

/-- Every subgroup of the faithful component orbit is the actual same group
in the constituent action quotient, regardless of the kernel on X. -/
def subgroupEquiv [Finite D] [FiniteDimensional (ZMod 2) W] (J : Subgroup D) (hJ : J ≤ H) :
    J ≃* image ρ H X I hH hX J := by
  let eJ := subgroupOfEquivOfLe (hJ.trans (show H ≤ H ⊔ X from le_sup_left))
  refine eJ.symm.trans (ChapterG.Section09.actionImageEquiv
    (action ρ H X I hH hX) (kerRepresentation (action ρ H X I hH hX))
    (projection ρ H X I hH hX) rfl (J.subgroupOf (H ⊔ X)) ?_)
  intro a b hab
  have he : (⟨(a : (H ⊔ X : Subgroup D)),hJ a.property⟩ : H) = ⟨(b : (H ⊔ X : Subgroup D)),hJ b.property⟩ :=
    hfH hab
  exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : D)) he))

/-- Equality of the literal image component and image orbit lifts before
passing to the constituent action quotient. -/
theorem image_eq_iff (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation) (J : Subgroup D) (hJ : J ≤ H) :
    image ρ H X I hH hX H = image ρ H X I hH hX J ↔ H = J := by
  constructor
  · intro he
    apply le_antisymm ?_ hJ
    intro a ha
    have hm : projection ρ H X I hH hX ⟨a,(show H ≤ H ⊔ X from le_sup_left) ha⟩ ∈
        image ρ H X I hH hX H := mem_map.mpr ⟨_,ha,rfl⟩
    rw [he] at hm
    obtain ⟨b,hb,hba⟩ := mem_map.mp hm
    have hab := projection_injective_on_orbit ρ H X I hH hX hfH
      ⟨b,hJ hb⟩ ⟨a,ha⟩ hba
    have hba : (b : D) = a := congrArg (fun z : H => (z : D)) hab
    change (b : D) ∈ J at hb
    simpa only [hba] using hb
  · rintro rfl
    rfl

/-- Self-duality descends for the fixed component-orbit action, using its
literal quotient map and the same linear intertwiner. -/
theorem selfDual_image
    (hs : Nonempty (Representation.Equiv
      (invariantSubspace ρ H I hH).toRepresentation
      (invariantSubspace ρ H I hH).toRepresentation.dual)) :
    Nonempty (Representation.Equiv
      ((kerRepresentation (action ρ H X I hH hX)).comp
        (image ρ H X I hH hX H).subtype)
      (Representation.dual ((kerRepresentation (action ρ H X I hH hX)).comp
        (image ρ H X I hH hX H).subtype))) := by
  obtain ⟨e⟩ := hs
  refine ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
  intro a
  obtain ⟨b,rfl⟩ := (projection ρ H X I hH hX).subgroupMap_surjective
    (H.subgroupOf (H ⊔ X)) a
  exact e.isIntertwining' ⟨b,b.property⟩

/-- Large rows retain ambient normality by lifting equality with the normal
component orbit; normality merely inside HX is not used. -/
theorem componentImageCases [Finite D] [FiniteDimensional (ZMod 2) W] (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation) [H.Normal] (J : Subgroup D) (hJ : J ≤ H)
    (hc : ComponentOrbitImageCases (image ρ H X I hH hX J)
      (image ρ H X I hH hX H)) : ComponentImageCases J := by
  let e := subgroupEquiv ρ H X I hH hX hfH J hJ
  have hn (he : image ρ H X I hH hX H = image ρ H X I hH hX J) : J.Normal :=
    (image_eq_iff ρ H X I hH hX hfH J hJ).mp he ▸ inferInstance
  rcases hc with ⟨he,ha | ha | ha | ha⟩ | (ha | ha) | ⟨he,ha⟩
  · exact Or.inl ⟨hn he,Or.inl (ha.map e.trans)⟩
  · exact Or.inl ⟨hn he,Or.inr (Or.inl (ha.map e.trans))⟩
  · exact Or.inl ⟨hn he,Or.inr (Or.inr (Or.inl (ha.map e.trans)))⟩
  · exact Or.inl ⟨hn he,Or.inr (Or.inr (Or.inr (ha.map e.trans)))⟩
  · exact Or.inr (Or.inl (Or.inl (ha.map e.trans)))
  · exact Or.inr (Or.inl (Or.inr (ha.map e.trans)))
  · exact Or.inr (Or.inr ⟨hn he,ha.map e.trans⟩)

/-- On an irreducible faithful normal-orbit constituent through a fixed
nonzero point, the actor kernel is exactly the orbit centralizer. This is
the equality C_X(I) = C_X(H) used before G.11.8. -/
theorem fixes_iff_centralizes (hX : X ≤ subspaceStabilizer ρ I) (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation) [H.Normal]
    (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation)
    (v : I) (hv : v ≠ 0) (x : X) (hvx : ρ x v = v) :
    (∀ w : I, ρ x w = w) ↔ (x : D) ∈ centralizer (H : Set D) := by
  let σ := action ρ H X I hH hX
  let R : Representation (ZMod 2) H I := (invariantSubspace ρ H I hH).toRepresentation
  let xP : (H ⊔ X : Subgroup D) := ⟨x,(show X ≤ H ⊔ X from le_sup_right) x.property⟩
  constructor
  · intro hx
    have hs : σ xP = 1 := by
      ext w
      exact hx w
    apply mem_centralizer_iff.mpr
    intro a ha
    have hxa : (x : D) * a * (x : D)⁻¹ ∈ H := (inferInstance : H.Normal).conj_mem a ha x
    have he : (⟨(x : D) * a * (x : D)⁻¹,hxa⟩ : H) = ⟨a,ha⟩ := by
      apply hfH
      change σ (xP * ⟨a,(show H ≤ H ⊔ X from le_sup_left) ha⟩ * xP⁻¹) = σ ⟨a,(show H ≤ H ⊔ X from le_sup_left) ha⟩
      rw [map_mul,map_mul,hs,one_mul]
      have hsinv : σ xP⁻¹ = 1 := by
        have hm := map_mul σ xP xP⁻¹
        rw [mul_inv_cancel,map_one,hs,one_mul] at hm
        exact hm.symm
      rw [hsinv,mul_one]
    have he' := congrArg Subtype.val he
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro hx
    let : IsIrreducible R := hi
    let f : IntertwiningMap R R := {
      toLinearMap := σ xP - 1
      isIntertwining' a := by
        ext w
        change ρ x (ρ a w) - ρ a w = ρ a (ρ x w - w)
        rw [map_sub]
        have hc := congrArg (fun z : D => ρ z (w : W))
          ((mem_centralizer_iff.mp hx) a a.property)
        simpa only [map_mul,Module.End.mul_apply] using
          congrArg (fun z : W => z - ρ a w) hc.symm }
    have hfv : f v = 0 := by
      apply Subtype.ext
      exact sub_eq_zero.mpr hvx
    have hf0 : f = 0 := by
      rcases IsIrreducible.injective_or_eq_zero f with hf | hf
      · exact (hv (hf (hfv.trans (map_zero f).symm))).elim
      · exact hf
    intro w
    have he := congrArg (fun t : IntertwiningMap R R => (t w : W)) hf0
    exact sub_eq_zero.mp he


/-- Faithfulness of the original actor on the constituent is equivalent to
a trivial intersection with the actual normal-orbit centralizer. -/
theorem actor_faithful_iff (hX : X ≤ subspaceStabilizer ρ I)
    (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    [H.Normal] (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation)
    (v : I) (hv : v ≠ 0) (hvX : ∀ x : X, ρ x v = v) :
    Function.Injective (fun x : X => (ρ (x : D)).comp I.subtype) ↔
      X ⊓ centralizer (H : Set D) = ⊥ := by
  constructor
  · intro hf
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hxfix := (fixes_iff_centralizes ρ H X I hH hX hfH hi v hv
      ⟨x,hx.1⟩ (hvX ⟨x,hx.1⟩)).mpr hx.2
    have hx1 : (⟨x,hx.1⟩ : X) = 1 := by
      apply hf
      ext w
      change ρ x (w : W) = ρ 1 (w : W)
      rw [map_one]
      exact hxfix w
    exact congrArg Subtype.val hx1
  · intro hc
    let τ : Representation (ZMod 2) X I := (invariantSubspace ρ X I hX).toRepresentation
    have ht : Function.Injective τ := by
      apply τ.ker_eq_bot_iff.mp
      apply _root_.eq_bot_iff.mpr
      intro x hx
      have hfix : ∀ w : I, ρ x w = w := by
        intro w
        exact congrArg Subtype.val (LinearMap.congr_fun hx w)
      have hcent := (fixes_iff_centralizes ρ H X I hH hX hfH hi v hv x (hvX x)).mp hfix
      apply Subtype.ext
      exact hc.le ⟨x.property,hcent⟩
    intro a b hab
    apply ht
    ext w
    exact LinearMap.congr_fun hab w

end MarkedAction

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
