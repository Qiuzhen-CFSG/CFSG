module

public import CFSG.Quasithin.ChapterB.Section02.BaumannNormalizerImage
public import Theory.SpecificGroups.PSL3Two.Parabolics.ShearNormalizer

/-!
# Cubic subgroup selection from a shear-radical image

An isomorphism from a subgroup C to SL₃(2) carries the restriction of an
ambient normalizer to the normalizer of the marked shear radical. The latter
has order 24. The literal Baumann normalizer image therefore has a cubic
factor. Its embedded two-residual has an image of order 12, and hence is a
two-perfect subgroup with order divisible by three inside the original
normal subgroup and Baumann normalizer.

The Chapter 13 source action supplies the actor isomorphism and the conjugate
shear marking. All normalizer intersections and image maps below retain their
actual subgroup inclusions.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
Lemma 13.7.4(1), printed p.938.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {G D : Type*} [Group G] [Group D] [Finite G]

private noncomputable def restricted_normalizer_equiv_shear
    (A B : Subgroup D) (hB : B ≤ A) (e : A ≃* Matrix.PSL3Two.SL)
    (g : Matrix.PSL3Two.SL)
    (hR : (B.subgroupOf A).map e.toMonoidHom =
      BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom) :
    (A ⊓ normalizer (B : Set D) : Subgroup D) ≃*
      normalizer (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom :
        Set Matrix.PSL3Two.SL) := by
  let H := (A ⊓ normalizer (B : Set D)).subgroupOf A
  have hlocal : H = normalizer (B.subgroupOf A : Set A) := by
    change (A ⊓ normalizer (B : Set D)).subgroupOf A = _
    rw [inf_subgroupOf_left, subgroupOf_normalizer_eq hB]
  have hmap : H.map e.toMonoidHom =
      normalizer (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom :
        Set Matrix.PSL3Two.SL) := by
    rw [hlocal, map_equiv_normalizer_eq, hR]
  exact (subgroupOfEquivOfLe (show A ⊓ normalizer (B : Set D) ≤ A from
    inf_le_left)).symm.trans
      ((H.equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap))

/-- Restricting an ambient normalizer to a marked binary linear-three actor
has order 24. -/
theorem card_restricted_normalizer_of_shear_image
    (C B : Subgroup D) (hBC : B ≤ C) (e : C ≃* Matrix.PSL3Two.SL)
    (g : Matrix.PSL3Two.SL)
    (hB : (B.subgroupOf C).map e.toMonoidHom =
      BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom) :
    Nat.card (C ⊓ normalizer (B : Set D) : Subgroup D) = 24 := by
  rw [Nat.card_congr (restricted_normalizer_equiv_shear C B hBC e g hB).toEquiv]
  exact Matrix.PSL3Two.card_normalizer_shear_conjugate g

theorem three_dvd_card_restricted_normalizer_of_shear_image
    (C B : Subgroup D) (hBC : B ≤ C) (e : C ≃* Matrix.PSL3Two.SL)
    (g : Matrix.PSL3Two.SL)
    (hB : (B.subgroupOf C).map e.toMonoidHom =
      BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom) :
    3 ∣ Nat.card (C ⊓ normalizer (B : Set D) : Subgroup D) := by
  rw [card_restricted_normalizer_of_shear_image C B hBC e g hB]
  decide

/-- The literal restricted Baumann normalizer image has order 24 when its
Baumann subgroup is marked as a conjugate of the shear radical. -/
theorem normal_baumann_normalizer_image_card_of_shear
    (P : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hNP : N ⊔ (P : Subgroup G) = ⊤) (f : G →* D)
    (e : N.map f ≃* Matrix.PSL3Two.SL)
    (hB : (baumann (P : Subgroup G)).map f ≤ N.map f)
    (g : Matrix.PSL3Two.SL)
    (hR : (((baumann (P : Subgroup G)).map f).subgroupOf (N.map f)).map
      e.toMonoidHom = BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom) :
    Nat.card ((N ⊓ normalizer (baumann (P : Subgroup G) : Set G)).map f) = 24 := by
  rw [normal_baumann_normalizer_image P N hNP f]
  rw [Nat.card_congr (restricted_normalizer_equiv_shear _ _ hB e g hR).toEquiv]
  exact Matrix.PSL3Two.card_normalizer_shear_conjugate g

/-- Source subgroup selection with the literal normalizer map and marking.
The chosen embedded residual has an image of order 12, so its order is
divisible by three. -/
theorem exists_twoPerfect_cubic_le_normal_baumann_normalizer_of_shear_image
    (P : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hNP : N ⊔ (P : Subgroup G) = ⊤) (f : G →* D)
    (e : N.map f ≃* Matrix.PSL3Two.SL)
    (hB : (baumann (P : Subgroup G)).map f ≤ N.map f)
    (g : Matrix.PSL3Two.SL)
    (hR : (((baumann (P : Subgroup G)).map f).subgroupOf (N.map f)).map
      e.toMonoidHom = BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom) :
    ∃ K : Subgroup G, K ≤ N ⊓ normalizer (baumann (P : Subgroup G) : Set G) ∧
      IsPPerfect 2 K ∧ 3 ∣ Nat.card K ∧ Nat.card (K.map f) = 12 := by
  let M := N ⊓ normalizer (baumann (P : Subgroup G) : Set G)
  let A := N.map f ⊓ normalizer ((baumann (P : Subgroup G)).map f : Set D)
  let K := (pResidual 2 M).map M.subtype
  let a := restricted_normalizer_equiv_shear (N.map f)
    ((baumann (P : Subgroup G)).map f) hB e g hR
  have hres : Nat.card ((pResidual 2 A).map A.subtype) = 12 := by
    rw [card_map_of_injective A.subtype_injective]
    rw [← card_map_of_injective (K := pResidual 2 A)
      (f := a.toMonoidHom) a.injective, map_pResidual 2 a]
    rw [← card_map_of_injective (K := pResidual 2 (normalizer
      (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom :
        Set Matrix.PSL3Two.SL)))
      (normalizer (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom :
        Set Matrix.PSL3Two.SL)).subtype_injective]
    exact Matrix.PSL3Two.card_residual_normalizer_shear_conjugate g
  have himage : Nat.card (K.map f) = 12 := by
    have he := normal_baumann_normalizer_residual_image P N hNP f
    change K.map f = (pResidual 2 A).map A.subtype at he
    rw [he]
    exact hres
  refine ⟨K, map_subtype_le _, isPPerfect_embedded_pResidual 2 M, ?_, himage⟩
  have h3 : 3 ∣ Nat.card (K.map f) := by rw [himage]; decide
  exact h3.trans (card_map_dvd K f)

end CFSG.Quasithin.ChapterB
