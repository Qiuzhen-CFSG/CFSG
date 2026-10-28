module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Quotients

/-!
# The faithful actor quotient in the source rank identity

The actual map X → Xdot/Z(U)^g-dot is surjective. The kernel E in
12.8.9(5) identifies its kernel with EZ(U)^g. This proves relative
normality and constructs X/EZ(U)^g ≃ Xdot/Z(U)^g-dot, retaining the
quotient evaluation formula and giving the corresponding order identity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the last
equality in the proof of Lemma 12.8.11(5), printed p.854 / PDF p.871.
The rank calculation uses this equivalence after the earlier geometric
center and hyperplane inputs have been supplied.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Restricting the actual projection preserves the exact subgroup image. -/
theorem dotMap_image (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat)
    (A Z : Subgroup G) (hA : A ≤ F.H) (hZ : Z ≤ A) :
    (Z.subgroupOf A).map (dotMap F ρ A hA) =
      (dotImage F ρ Z).subgroupOf (dotImage F ρ A) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hA a.property⟩, ha, rfl⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨⟨z, hZ hz⟩, hz, Subtype.ext he⟩

/-- The genuine quotient in the source rank identity. Normality follows from
commutativity of Xdot, established above from 12.8.9(2). -/
abbrev XdotCenterQuotient (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G)
    [IsMulCommutative (dotImage F ρ (F.X g))] :=
  dotImage F ρ (F.X g) ⧸
    (dotImage F ρ (conjugate F.ZU g)).subgroupOf (dotImage F ρ (F.X g))

/-- The rank quotient map, before quotienting X by its kernel. -/
def centerQuotientMap (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) (hX : F.X g ≤ F.H)
    [IsMulCommutative (dotImage F ρ (F.X g))] :
    F.X g →* XdotCenterQuotient F ρ g :=
  (QuotientGroup.mk' ((dotImage F ρ (conjugate F.ZU g)).subgroupOf
    (dotImage F ρ (F.X g)))).comp (dotMap F ρ (F.X g) hX)

theorem centerQuotientMap_surjective (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) (hX : F.X g ≤ F.H)
    [IsMulCommutative (dotImage F ρ (F.X g))] :
    Function.Surjective (centerQuotientMap F ρ g hX) :=
  (QuotientGroup.mk'_surjective _).comp (dotMap_surjective F ρ (F.X g) hX)

/-- The source kernel E from 12.8.9(5) gives precisely EZ(U)^g, with the
original maps, as the kernel of the map to Xdot/Z(U)^g-dot. -/
theorem centerQuotientMap_ker (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) (hX : F.X g ≤ F.H)
    [IsMulCommutative (dotImage F ρ (F.X g))]
    (hker : (ρ.comp (inclusion hX)).ker = (F.E g).subgroupOf (F.X g)) :
    (centerQuotientMap F ρ g hX).ker =
      (F.E g ⊔ conjugate F.ZU g).subgroupOf (F.X g) := by
  change ((QuotientGroup.mk' _).comp (dotMap F ρ (F.X g) hX)).ker = _
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
    ← dotMap_image F ρ (F.X g) (conjugate F.ZU g) hX (F.conjugate_ZU_le_X g),
    comap_map_eq, dotMap_ker, hker, sup_comm,
    ← subgroupOf_sup (show F.E g ≤ F.X g from inf_le_right) (F.conjugate_ZU_le_X g)]

/-- This is relative normality inside X, not normality in the ambient group. -/
theorem E_sup_conjugate_center_normal (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) (hX : F.X g ≤ F.H)
    [IsMulCommutative (dotImage F ρ (F.X g))]
    (hker : (ρ.comp (inclusion hX)).ker = (F.E g).subgroupOf (F.X g)) :
    ((F.E g ⊔ conjugate F.ZU g).subgroupOf (F.X g)).Normal := by
  rw [← centerQuotientMap_ker F ρ g hX hker]
  infer_instance

/-- The exact isomorphism used by the last equality in the source rank calculation. -/
noncomputable def centerQuotientEquiv (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) (hX : F.X g ≤ F.H)
    [IsMulCommutative (dotImage F ρ (F.X g))]
    (hker : (ρ.comp (inclusion hX)).ker = (F.E g).subgroupOf (F.X g)) :
    letI := E_sup_conjugate_center_normal F ρ g hX hker
    (F.X g ⧸ (F.E g ⊔ conjugate F.ZU g).subgroupOf (F.X g)) ≃*
      XdotCenterQuotient F ρ g := by
  letI := E_sup_conjugate_center_normal F ρ g hX hker
  exact (QuotientGroup.quotientMulEquivOfEq (centerQuotientMap_ker F ρ g hX hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (centerQuotientMap F ρ g hX)
      (centerQuotientMap_surjective F ρ g hX))

theorem centerQuotientEquiv_apply (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) (hX : F.X g ≤ F.H)
    [IsMulCommutative (dotImage F ρ (F.X g))]
    (hker : (ρ.comp (inclusion hX)).ker = (F.E g).subgroupOf (F.X g)) (x : F.X g) :
    letI := E_sup_conjugate_center_normal F ρ g hX hker
    centerQuotientEquiv F ρ g hX hker (QuotientGroup.mk' _ x) =
      centerQuotientMap F ρ g hX x := rfl

/-- The actual quotient order, expressed using the ambient subgroup EZ(U)^g. -/
theorem card_centerQuotient_mul_card (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) (hX : F.X g ≤ F.H)
    [IsMulCommutative (dotImage F ρ (F.X g))]
    (hker : (ρ.comp (inclusion hX)).ker = (F.E g).subgroupOf (F.X g)) :
    Nat.card (XdotCenterQuotient F ρ g) * Nat.card (F.E g ⊔ conjugate F.ZU g : Subgroup G) =
      Nat.card (F.X g) := by
  have hc := (centerQuotientMap F ρ g hX).ker.index_mul_card
  rw [index_ker, MonoidHom.range_eq_top.mpr (centerQuotientMap_surjective F ρ g hX),
    card_top, centerQuotientMap_ker F ρ g hX hker,
    Nat.card_congr (subgroupOfEquivOfLe (sup_le (show F.E g ≤ F.X g from inf_le_right)
      (F.conjugate_ZU_le_X g))).toEquiv] at hc
  exact hc

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
