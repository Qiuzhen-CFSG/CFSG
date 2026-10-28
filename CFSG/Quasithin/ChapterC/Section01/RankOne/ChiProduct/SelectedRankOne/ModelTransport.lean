module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Coordinates
public import Theory.Representation.NormalElementaryQuotient
/-!
# Original moved coordinates transported to the local model

Equality of the selected and residual action images identifies their fixed
subgroups on the original moved module. Its actual inclusion therefore
transports the original quotient coordinates, including their intertwining
formula, to the literal C.1.17 model.

Source: Aschbacher–Smith C.1.26, p.132.
-/
public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open GlaubermanNiles
variable {G H B : Type*} [Group G] [Finite G] [Group H] [Group B]

theorem naturalModel_of_original_moved_coordinates
    (U X N : Subgroup G) [U.Normal] [X.Normal] [IsElementaryAbelian 2 U]
    (b : B →* N) (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (himage : N.map q = X.map q)
    (hmove : (moved b).map N.subtype = ⁅U,X⁆)
    (F : Type) [Field F] [CharP F 2] [IsQuasisimple SL(2,F)]
    (c : LocalStar b ≃* SL(2,F))
    (f : (⁅U,X⁆ : Subgroup G) →* Multiplicative (Fin 2 → F)) (hf : Function.Surjective f)
    (hk : ∀ w : (⁅U,X⁆ : Subgroup G), f w = 1 ↔ (w:G) ∈ centralizer (X : Set G))
    (he : ∀ (n : N) (w : (⁅U,X⁆ : Subgroup G)),
      Multiplicative.toAdd (f (MulAut.conjNormal (n:G) w)) =
        specialLinearNatural 2 (c (QuotientGroup.mk' (localKernel b) n))
          (Multiplicative.toAdd (f w))) : Nonempty (NaturalModel b F) := by
  let k := ((moved b).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr hmove)
  let g := f.comp k.toMonoidHom
  have hg : Function.Surjective g := hf.comp k.surjective
  have hkv (w : moved b) : (k w : G) = ((w:N):G) := rfl
  let : IsQuasisimple (LocalStar b) := IsQuasisimple.of_mulEquiv c.symm
  have hactor : actorLift b = ⊤ := by
    unfold actorLift
    rw [generalizedFitting_eq_top_of_quasisimple,comap_top]
  have hgk : g.ker = movedFixed b := by
    ext w
    change f (k w) = 1 ↔ (w:N) ∈ centralizer (actorLift b : Set N)
    rw [hk,hactor]
    let u : Additive U := Additive.ofMul ⟨(k w:G),commutator_le_left U X (k w).property⟩
    have hcent : (k w:G) ∈ centralizer (X : Set G) ↔
        (k w:G) ∈ centralizer (N : Set G) := by
      change (u.toMul:G) ∈ centralizer (X : Set G) ↔ (u.toMul:G) ∈ centralizer (N : Set G)
      rw [←NormalElementaryQuotient.mem_fixedSpace_image U q hq hker X u,
        ←NormalElementaryQuotient.mem_fixedSpace_image U q hq hker N u,himage]
    rw [hcent,hkv]
    constructor
    · intro h n _
      exact Subtype.ext (h n n.property)
    · intro h n hn
      exact congrArg (fun a : N => (a:G)) (h ⟨n,hn⟩ (mem_top _))
  apply naturalModel_of_star_coordinates b F c g hg hgk
  intro a w
  have hkc : k (movedConjugate b a w) = MulAut.conjNormal ((a:N):G) (k w) := by
    apply Subtype.ext
    rfl
  change Multiplicative.toAdd (f (k (movedConjugate b a w))) = _
  rw [hkc]
  exact he a (k w)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
