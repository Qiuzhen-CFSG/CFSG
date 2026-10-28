module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.FaithfulMoved.BaumannPair
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The marked symmetric-three product in the binary orthogonal group

The subgroup preserving both definite planes acts as the full product of the
permutation groups on their three nonzero vectors. The equivalence below retains
that literal action and identifies reflection parity with the permutation sign.
A nontrivial elementary subgroup with equal signs has order at most two and
fixes at most four vectors. This is the strict bound used to recover independent
reflections in the original 15.4.12 setup, and then the marked product in 15.4.20.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 15.4.12(6),
printed pp.1160--1161, and the quotient preceding 15.4.20, printed pp.1163--1164.
-/

@[expose] public section
open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
open FamilySource.ModuleStructure.BaumannPair
abbrev S3 := Equiv.Perm (Fin 3)
def planeCoordinates : Plane ≃ₗ[F] BinaryFourPlus.Plane := (LinearEquiv.finTwoArrow F F).symm

def planeTransport : (Plane ≃ₗ[F] Plane) ≃* (BinaryFourPlus.Plane ≃ₗ[F] BinaryFourPlus.Plane) where
  toFun a := planeCoordinates.symm.trans (a.trans planeCoordinates)
  invFun a := planeCoordinates.trans (a.trans planeCoordinates.symm)
  left_inv a := by apply LinearEquiv.ext; intro x; simp
  right_inv a := by apply LinearEquiv.ext; intro x; simp
  map_mul' a b := by apply LinearEquiv.ext; intro x; simp

def planeEquiv : (Plane ≃ₗ[F] Plane) ≃* S3 := planeTransport.trans BinaryFourPlus.planeAutEquiv

theorem plane_preserves (a : Plane ≃ₗ[F] Plane) (v : Plane) : planeForm (a v) = planeForm v := by
  simp only [planeForm_indicator, a.map_eq_zero_iff]

def productIsometry : (S3 × S3) →* OrthogonalFourBinary.IsometryGroup where
  toFun p := ⟨(planeEquiv.symm p.1).prodCongr (planeEquiv.symm p.2), by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup form _).mpr
    intro v
    change planeForm (planeEquiv.symm p.1 v.1) + planeForm (planeEquiv.symm p.2 v.2) =
      planeForm v.1 + planeForm v.2
    rw [plane_preserves, plane_preserves]⟩
  map_one' := by apply Subtype.ext; ext v <;> simp
  map_mul' a b := by apply Subtype.ext; ext v <;> simp

theorem productIsometry_apply (p : S3 × S3) (v : Space) :
    (productIsometry p).val v = (planeEquiv.symm p.1 v.1, planeEquiv.symm p.2 v.2) := rfl

theorem productIsometry_mem_base (p : S3 × S3) : productIsometry p ∈ base := by
  change firstPlane.map (vectorAction (productIsometry p)).toMonoidHom = firstPlane
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change planeEquiv.symm p.2 w.toAdd.2 = 0
    rw [show w.toAdd.2 = 0 from hw, map_zero]
  · intro hv
    let w := (vectorAction (productIsometry p)).symm v
    refine ⟨w, ?_, (vectorAction (productIsometry p)).apply_symm_apply v⟩
    change (planeEquiv.symm p.2).symm v.toAdd.2 = 0
    rw [show v.toAdd.2 = 0 from hv, map_zero]

def productBase : (S3 × S3) →* base := productIsometry.codRestrict base productIsometry_mem_base

theorem productBase_injective : Function.Injective productBase := by
  intro p q hpq
  have h (v : Space) : (productIsometry p).val v = (productIsometry q).val v :=
    congrArg (fun g : base => g.val.val v) hpq
  apply Prod.ext
  · apply planeEquiv.symm.injective
    apply LinearEquiv.ext
    intro v
    exact congrArg Prod.fst (h (v,0))
  · apply planeEquiv.symm.injective
    apply LinearEquiv.ext
    intro v
    exact congrArg Prod.snd (h (0,v))

theorem productIsometry_codes (i j : LineCode) :
    productIsometry (planeEquiv (planePermutation i), planeEquiv (planePermutation j)) =
      codeMap (i,j,false) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp [productIsometry, codeMap, candidate]

theorem productBase_surjective : Function.Surjective productBase := by
  intro g
  obtain ⟨⟨i,j,b⟩, hg⟩ := codeMap_bijective.surjective g.val
  have hb : b = false := by
    have hh := (base_iff g.val).mp g.property
    rw [←hg, show codeEquiv.symm (codeMap (i,j,b)) = (i,j,b) from codeEquiv.symm_apply_apply _] at hh
    exact hh
  subst b
  refine ⟨(planeEquiv (planePermutation i), planeEquiv (planePermutation j)), ?_⟩
  apply Subtype.ext
  exact (productIsometry_codes i j).trans hg

noncomputable def baseEquiv : base ≃* (S3 × S3) :=
  (MulEquiv.ofBijective productBase ⟨productBase_injective, productBase_surjective⟩).symm

theorem baseEquiv_symm_apply (p : S3 × S3) : baseEquiv.symm p = productBase p := rfl

theorem baseEquiv_codes (i j : LineCode) (h : codeMap (i,j,false) ∈ base) :
    baseEquiv ⟨codeMap (i,j,false),h⟩ =
      (planeEquiv (planePermutation i), planeEquiv (planePermutation j)) := by
  apply baseEquiv.symm.injective
  rw [baseEquiv.symm_apply_apply, baseEquiv_symm_apply]
  apply Subtype.ext
  exact (productIsometry_codes i j).symm

def codePermutation (i : LineCode) : S3 :=
  (Equiv.swap 0 1 * Equiv.swap 1 2) ^ i.1.val * Equiv.swap 0 1 ^ i.2.val

theorem planeEquiv_apply (a : Plane ≃ₗ[F] Plane) (i : Fin 3) :
    BinaryFourPlus.nonzeroVector (planeEquiv a i) =
      planeCoordinates (a (planeCoordinates.symm (BinaryFourPlus.nonzeroVector i))) :=
  BinaryFourPlus.planeAutPerm_apply (planeTransport a) i

theorem planeEquiv_code (i : LineCode) : planeEquiv (planePermutation i) = codePermutation i := by
  apply Equiv.ext
  intro n
  apply BinaryFourPlus.nonzeroVector_injective
  rw [planeEquiv_apply]
  exact (show ∀ i : LineCode, ∀ n : Fin 3,
    planeCoordinates (planePermutation i (planeCoordinates.symm (BinaryFourPlus.nonzeroVector n))) =
      BinaryFourPlus.nonzeroVector (codePermutation i n) by decide +kernel) i n

theorem planeEquiv_sign : ∀ i : LineCode,
    Equiv.Perm.sign (planeEquiv (planePermutation i)) = if i.2 = 0 then 1 else -1 := by
  intro i
  rw [planeEquiv_code]
  exact (show ∀ i : LineCode, Equiv.Perm.sign (codePermutation i) =
    if i.2 = 0 then 1 else -1 by decide +kernel) i

theorem baseEquiv_sign (g : base) :
    (Equiv.Perm.sign (baseEquiv g).1, Equiv.Perm.sign (baseEquiv g).2) =
      (if (codeEquiv.symm g.val).1.2 = 0 then 1 else -1,
       if (codeEquiv.symm g.val).2.1.2 = 0 then 1 else -1) := by
  obtain ⟨⟨i,j,b⟩, hg⟩ := codeMap_bijective.surjective g.val
  have hb : b = false := by
    have hh := (base_iff g.val).mp g.property
    rw [←hg, show codeEquiv.symm (codeMap (i,j,b)) = (i,j,b) from codeEquiv.symm_apply_apply _] at hh
    exact hh
  subst b
  have he : g = ⟨codeMap (i,j,false), hg ▸ g.property⟩ := Subtype.ext hg.symm
  rw [he, baseEquiv_codes]
  rw [show codeEquiv.symm (codeMap (i,j,false)) = (i,j,false) from codeEquiv.symm_apply_apply _]
  simp only [planeEquiv_sign]


noncomputable def firstSign : base →* ℤˣ where
  toFun g := Equiv.Perm.sign (baseEquiv g).1
  map_one' := by simp
  map_mul' a b := by simp

private theorem even_square_one : ∀ p : S3, p ^ 2 = 1 → Equiv.Perm.sign p = 1 → p = 1 := by
  decide +kernel

theorem base_equal_parity_sign (g : base)
    (h : (codeEquiv.symm g.val).1.2 = (codeEquiv.symm g.val).2.1.2) :
    Equiv.Perm.sign (baseEquiv g).1 = Equiv.Perm.sign (baseEquiv g).2 := by
  have hf := congrArg Prod.fst (baseEquiv_sign g)
  have hs := congrArg Prod.snd (baseEquiv_sign g)
  dsimp only [Prod.fst, Prod.snd] at hf hs
  rw [hf, hs, h]

theorem equal_parity_elementary_card_le_two
    (B : Subgroup OrthogonalFourBinary.IsometryGroup) [IsElementaryAbelian 2 B]
    (hB : B ≤ base)
    (hpar : ∀ b ∈ B, (codeEquiv.symm b).1.2 = (codeEquiv.symm b).2.1.2) :
    Nat.card B ≤ 2 := by
  let f : B →* ℤˣ := firstSign.comp (inclusion hB)
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro b hb
    let g : base := inclusion hB b
    have hg2 : g ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ b.property)
    have hpair2 : baseEquiv g ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
    have hsg : Equiv.Perm.sign (baseEquiv g).1 = 1 := hb
    have hsign := base_equal_parity_sign g (hpar b b.property)
    have h1 := even_square_one (baseEquiv g).1 (congrArg Prod.fst hpair2) hsg
    have h2 := even_square_one (baseEquiv g).2 (congrArg Prod.snd hpair2) (hsign.symm.trans hsg)
    have hg1 : g = 1 := baseEquiv.injective ((Prod.ext h1 h2).trans (map_one baseEquiv).symm)
    exact Subtype.ext (congrArg (fun x : base => (x : OrthogonalFourBinary.IsometryGroup)) hg1)
  have hc := Nat.card_le_card_of_injective f hinj
  have hu : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
  rwa [hu] at hc

set_option maxRecDepth 10000 in
private theorem finite_equal_parity_fixed : ∀ k : Code,
    (∃ v : Space, eval k v ≠ v) → k.1.2 = k.2.1.2 →
    (∀ v : Space, eval k (eval k v) = v) →
    Fintype.card {v : Space // eval k v = v} = 4 := by decide +kernel

theorem equal_parity_elementary_strict_fixed_bound
    (B : Subgroup OrthogonalFourBinary.IsometryGroup) [IsElementaryAbelian 2 B]
    (hB : B ≤ base)
    (hpar : ∀ b ∈ B, (codeEquiv.symm b).1.2 = (codeEquiv.symm b).2.1.2)
    (hne : B ≠ ⊥) : Nat.card (FixedVectors B) * Nat.card B < 16 := by
  have hcard := equal_parity_elementary_card_le_two B hB hpar
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨k, hk⟩ := codeMap_bijective.surjective g.val
  have hkB : codeMap k ∈ B := hk ▸ g.property
  have hkp : k.1.2 = k.2.1.2 := by
    have h := hpar (codeMap k) hkB
    rwa [show codeEquiv.symm (codeMap k) = k from codeEquiv.symm_apply_apply _] at h
  have hk2 : codeMap k ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hkB
  have hfix : Nat.card {v : Space // eval k v = v} = 4 := by
    rw [Nat.card_eq_fintype_card]
    refine finite_equal_parity_fixed k ?_ hkp ?_
    · by_contra! h
      apply hg
      apply Subtype.ext
      rw [← hk]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact (candidate_eval k v).trans (h v)
    · intro v
      have h := congrArg (fun a : OrthogonalFourBinary.IsometryGroup => a.val v) hk2
      change candidate k (candidate k v) = v at h
      simpa only [candidate_eval] using h
  have hle : Nat.card (FixedVectors B) ≤ 4 := by
    rw [← hfix]
    refine Nat.card_le_card_of_injective
      (fun v : FixedVectors B => (⟨v.val, ?_⟩ : {v : Space // eval k v = v}))
      (fun a b h => Subtype.ext (congrArg (fun x : {v : Space // eval k v = v} => x.val) h))
    exact (candidate_eval k v.val).symm.trans (v.property (codeMap k) hkB)
  exact lt_of_le_of_lt (Nat.mul_le_mul hle hcard) (by decide : 4 * 2 < 16)

theorem rotationHom_code (r : RotationCode) :
    rotationHom r = codeMap ((⟨r.toAdd.1.val, ZMod.val_lt _⟩,0),
      (⟨r.toAdd.2.val, ZMod.val_lt _⟩,0),false) := by
  apply Subtype.ext
  simp [rotationHom, rotation, codeMap, candidate, planePermutation]

theorem rotations_le_base : rotations ≤ base := by
  rintro _ ⟨r,rfl⟩
  apply (base_iff _).mpr
  rw [rotationHom_code]
  exact congrArg (fun k : Code => k.2.2) (codeEquiv.symm_apply_apply _)

theorem rotations_parity_zero (g : OrthogonalFourBinary.IsometryGroup) (hg : g ∈ rotations) :
    (codeEquiv.symm g).1.2 = 0 ∧ (codeEquiv.symm g).2.1.2 = 0 := by
  obtain ⟨r,rfl⟩ := hg
  rw [rotationHom_code]
  rw [show codeEquiv.symm (codeMap _) = _ from codeEquiv.symm_apply_apply _]
  exact ⟨rfl,rfl⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
