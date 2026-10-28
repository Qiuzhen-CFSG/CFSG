module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete.Generation
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The marked cubic axes

The alternating-three axes of the literal symmetric product are exactly the
cubic rotation subgroups fixing a nonzero vector. A rotation with both
coordinates nontrivial fixes only zero; a nonidentity generator therefore lies
on one axis. Cardinality three identifies its entire subgroup with that axis.
The axes generate the full rotation group and retain their exact markings.

Source: Aschbacher--Smith, 15.4.12(6) and the quotient before 15.4.20,
combined manuscript of 1 March 2004, printed pp.1160--1164.
-/

@[expose] public section
open Subgroup
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
open FamilySource.ModuleStructure.BaumannPair

/-- The two standard alternating-three axes in the marked symmetric product. -/
def standardAxis (b : Bool) : Subgroup (S3 × S3) :=
  if b then (⊥ : Subgroup S3).prod (alternatingGroup (Fin 3))
  else (alternatingGroup (Fin 3)).prod (⊥ : Subgroup S3)

/-- The same cubic axes in the actual quadratic isometry group. -/
def rotationAxis (b : Bool) : Subgroup OrthogonalFourBinary.IsometryGroup :=
  (standardAxis b).map productIsometry

theorem productIsometry_injective : Function.Injective productIsometry := by
  intro a b h
  exact productBase_injective (Subtype.ext h)

theorem rotationAxis_card (b : Bool) : Nat.card (rotationAxis b) = 3 := by
  rw [rotationAxis, card_map_of_injective productIsometry_injective]
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hprod (A B : Subgroup S3) : Nat.card (A.prod B) = Nat.card A * Nat.card B := by
    rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]
  cases b <;> simp only [standardAxis, Bool.false_eq_true, ↓reduceIte, hprod, card_bot, mul_one, one_mul] <;> exact hc

theorem rotationAxis_le_base (b : Bool) : rotationAxis b ≤ base := by
  rintro _ ⟨p, _, rfl⟩
  exact productIsometry_mem_base p

theorem rotationAxis_marked (b : Bool) :
    ((rotationAxis b).subgroupOf base).map baseEquiv.toMonoidHom = standardAxis b := by
  ext p
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨p,hp,hpg⟩ := hg
    have he : g = productBase p := Subtype.ext hpg.symm
    rw [he]
    change baseEquiv (baseEquiv.symm p) ∈ standardAxis b
    rwa [baseEquiv.apply_symm_apply]
  · intro hp
    refine ⟨productBase p, ⟨p,hp,rfl⟩, ?_⟩
    exact baseEquiv.apply_symm_apply p

theorem rotationAxis_le_rotations (b : Bool) : rotationAxis b ≤ rotations := by
  rintro _ ⟨p,hp,rfl⟩
  apply (pairSign_eq_one_iff (productBase p)).mp
  have he : baseEquiv (productBase p) = p := baseEquiv.apply_symm_apply p
  change (Equiv.Perm.sign (baseEquiv (productBase p)).1,
    Equiv.Perm.sign (baseEquiv (productBase p)).2) = 1
  rw [he]
  cases b <;>
    simp only [standardAxis, Bool.false_eq_true, ↓reduceIte] at hp
  · rw [hp.1, hp.2, map_one]; rfl
  · rw [hp.1, map_one, hp.2]; rfl

theorem rotation_fixed_coordinates (r : RotationCode) (v : Space)
    (hv : v ≠ 0) (hfix : rotation r v = v) : r.toAdd.1 = 0 ∨ r.toAdd.2 = 0 :=
  (show ∀ r : RotationCode, ∀ v : Space, v ≠ 0 → rotation r v = v →
    r.toAdd.1 = 0 ∨ r.toAdd.2 = 0 by decide +kernel) r v hv hfix

theorem rotationHom_baseEquiv (r : RotationCode) :
    baseEquiv ⟨rotationHom r, rotations_le_base ⟨r,rfl⟩⟩ =
      (codePermutation (⟨r.toAdd.1.val, ZMod.val_lt _⟩,0),
       codePermutation (⟨r.toAdd.2.val, ZMod.val_lt _⟩,0)) := by
  let i : LineCode := (⟨r.toAdd.1.val, ZMod.val_lt _⟩,0)
  let j : LineCode := (⟨r.toAdd.2.val, ZMod.val_lt _⟩,0)
  have hbase : codeMap (i,j,false) ∈ base := by
    rw [← productIsometry_codes i j]
    exact productIsometry_mem_base _
  have he : (⟨rotationHom r, rotations_le_base ⟨r,rfl⟩⟩ : base) =
      ⟨codeMap (i,j,false), hbase⟩ := by
    apply Subtype.ext
    exact rotationHom_code r
  rw [he, baseEquiv_codes, planeEquiv_code, planeEquiv_code]

theorem rotation_fixed_mem_axis (g : OrthogonalFourBinary.IsometryGroup) (hg : g ∈ rotations)
    (v : Space) (hv : v ≠ 0) (hfix : g.val v = v) : ∃ b : Bool, g ∈ rotationAxis b := by
  obtain ⟨r,rfl⟩ := hg
  have hrmem : rotationHom r ∈ rotations := ⟨r,rfl⟩
  let g' : base := ⟨rotationHom r, rotations_le_base hrmem⟩
  let p := baseEquiv g'
  have he : productIsometry p = rotationHom r :=
    congrArg Subtype.val (baseEquiv.symm_apply_apply g')
  have hs : Equiv.Perm.sign p.1 = 1 ∧ Equiv.Perm.sign p.2 = 1 := by
    have hh := (pairSign_eq_one_iff g').mpr ⟨r,rfl⟩
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  rcases rotation_fixed_coordinates r v hv hfix with hr | hr
  · refine ⟨true, ⟨p, ?_, he⟩⟩
    change p.1 = 1 ∧ p.2 ∈ alternatingGroup (Fin 3)
    refine ⟨?_, Equiv.Perm.mem_alternatingGroup.mpr hs.2⟩
    have hh := rotationHom_baseEquiv r
    change p = _ at hh
    rw [hh, hr]
    simp [codePermutation]
  · refine ⟨false, ⟨p, ?_, he⟩⟩
    change p.1 ∈ alternatingGroup (Fin 3) ∧ p.2 = 1
    refine ⟨Equiv.Perm.mem_alternatingGroup.mpr hs.1, ?_⟩
    have hh := rotationHom_baseEquiv r
    change p = _ at hh
    rw [hh, hr]
    simp [codePermutation]

theorem cubic_fixed_subgroup_eq_axis
    (B : Subgroup OrthogonalFourBinary.IsometryGroup) (hB : B ≤ rotations)
    (hcard : Nat.card B = 3) (v : Space) (hv : v ≠ 0)
    (hfix : ∀ g ∈ B, g.val v = v) : ∃ b : Bool, B = rotationAxis b := by
  have hne : B ≠ ⊥ := by intro h; rw [h,card_bot] at hcard; contradiction
  obtain ⟨g,hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨b,hb⟩ := rotation_fixed_mem_axis g (hB g.property) v hv (hfix g g.property)
  have horder : orderOf (g : OrthogonalFourBinary.IsometryGroup) = 3 := by
    obtain ⟨r,hr⟩ := hB g.property
    apply orderOf_eq_prime
    · rw [←hr]; exact rotation_cube r
    · exact fun h => hg (Subtype.ext h)
  have hz : Nat.card (zpowers (g : OrthogonalFourBinary.IsometryGroup)) = 3 := by
    rw [Nat.card_zpowers,horder]
  have hzb : zpowers (g : OrthogonalFourBinary.IsometryGroup) = B :=
    eq_of_le_of_card_ge (zpowers_le.mpr g.property) (by rw [hz,hcard])
  have hza : zpowers (g : OrthogonalFourBinary.IsometryGroup) = rotationAxis b :=
    eq_of_le_of_card_ge (zpowers_le.mpr hb) (by rw [hz,rotationAxis_card])
  exact ⟨b,hzb.symm.trans hza⟩


theorem rotations_card : Nat.card rotations = 9 := by
  rw [rotations, ←Nat.card_congr (MonoidHom.ofInjective rotationHom_injective).toEquiv,
    Nat.card_eq_fintype_card]
  decide +kernel

theorem rotationAxis_sup : rotationAxis false ⊔ rotationAxis true = rotations := by
  apply le_antisymm (sup_le (rotationAxis_le_rotations false) (rotationAxis_le_rotations true))
  intro g hg
  let g' : base := ⟨g,rotations_le_base hg⟩
  let p := baseEquiv g'
  have he : productIsometry p = g := congrArg Subtype.val (baseEquiv.symm_apply_apply g')
  have hs : Equiv.Perm.sign p.1 = 1 ∧ Equiv.Perm.sign p.2 = 1 := by
    have hh := (pairSign_eq_one_iff g').mpr hg
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  have hfirst : productIsometry (p.1,1) ∈ rotationAxis false :=
    ⟨(p.1,1), ⟨Equiv.Perm.mem_alternatingGroup.mpr hs.1,rfl⟩,rfl⟩
  have hsecond : productIsometry (1,p.2) ∈ rotationAxis true :=
    ⟨(1,p.2), ⟨rfl,Equiv.Perm.mem_alternatingGroup.mpr hs.2⟩,rfl⟩
  have hh := (rotationAxis false ⊔ rotationAxis true).mul_mem
    ((le_sup_left : rotationAxis false ≤ rotationAxis false ⊔ rotationAxis true) hfirst)
    ((le_sup_right : rotationAxis true ≤ rotationAxis false ⊔ rotationAxis true) hsecond)
  rw [← map_mul] at hh
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, he] using hh

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct.Concrete
