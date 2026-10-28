module
public import Theory.SpecificGroups.SymplecticFour.RadicalParabolics
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SL2.RadicalSubgroups
public import Theory.SpecificGroups.SL2.TwoCore

/-!
# Exact radical normalizers in binary symplectic four-space

The fixed-space radical places the normalizer in a point or plane parabolic.
Its determinant-one subgroup contains the original two-group, and remains
invariant under its normalizer. Radicality descends to the actual SL₂ quotient
of that subgroup. The image is either trivial or Sylow; the original radical
is accordingly the parabolic core or a full ambient Sylow subgroup. Thus its
normalizer is precisely a conjugate point parabolic, plane parabolic or Borel.

This includes the field with two elements and retains the Borel alternative.
Source: Aschbacher (1981), 8.2(7), used in Aschbacher–Smith C.2.7, pp.146–147.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem twoGroup_le_determinantKernel
    (R : Subgroup (Sp F)) (hR : IsPGroup 2 R)
    (W : Submodule F (Vector F)) (hRW : R ≤ stabilizer W) :
    R ≤ determinantKernel W := by
  intro r hr
  let x : stabilizer W := ⟨r,hRW hr⟩
  obtain ⟨k,hk⟩ := hR.exists_pow_pow_eq_one (⟨r,hr⟩ : R)
  have hx : x ^ (2 ^ k) = 1 := Subtype.ext (congrArg (fun y : R => (y : Sp F)) hk)
  have he : ((determinantCharacter W x : Fˣ) : F) ^ (2 ^ k) = 1 := by
    simpa only [map_pow,map_one,Units.val_pow_eq_pow_val,Units.val_one] using
      congrArg (fun a : Fˣ => (a : F)) (congrArg (determinantCharacter W) hx)
  refine ⟨x,?_,rfl⟩
  apply Units.ext
  exact (iterateFrobenius_inj F 2 k) (by simpa [iterateFrobenius_def] using he)

private theorem normalizer_eq_parabolic_or_sylow
    (R P L : Subgroup (Sp F)) (hR : R.IsPRadical 2)
    (hRL : R ≤ L) (hNP : normalizer (R : Set (Sp F)) ≤ P)
    (hPL : P ≤ normalizer (L : Set (Sp F)))
    (q : L →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (T : Sylow 2 (Sp F)) (hTL : (T : Subgroup (Sp F)) ≤ L) :
    normalizer (R : Set (Sp F)) = P ∨
      ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = R := by
  rcases Matrix.SpecialLinearGroup.radical_local_eq_kernel_or_sylow
    R L hR hRL (hNP.trans hPL) q hq hk T hTL with he | hs
  · left
    have hc : q.ker = pCore 2 L := by
      have hh := q.comap_pCore_of_ker_isPGroup hq hk (p := 2)
      rwa [Matrix.SL2.twoCore_eq_bot F,MonoidHom.comap_bot] at hh
    apply le_antisymm hNP
    rw [he,hc]
    exact hPL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  · exact Or.inr hs

/-- The Borel case arises only when the radical itself is an ambient Sylow subgroup. -/
theorem radical_normalizer_parabolic_or_sylow
    (R : Subgroup (Sp F)) (hR : R.IsPRadical 2)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    (∃ g : Sp F,
      (normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom = planeParabolic) ∨
      ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = R := by
  obtain ⟨g,hg⟩ := radical_normalizer_parabolic_cover R hR
  let e := MulAut.conj g
  let U := R.map e.toMonoidHom
  have hu : U.IsPRadical 2 := hR.map_equiv e
  have hmap : (normalizer (R : Set (Sp F))).map e.toMonoidHom =
      normalizer (U : Set (Sp F)) := map_equiv_normalizer_eq R e
  rw [hmap] at hg
  have hsyl (S : Sylow 2 (Sp F)) (hS : (S : Subgroup (Sp F)) = U) :
      ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = R := by
    refine ⟨S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,?_⟩
    change (S : Subgroup (Sp F)).map e.symm.toMonoidHom = R
    rw [hS]
    ext x
    constructor
    · rintro ⟨y,⟨r,hr,rfl⟩,rfl⟩
      simpa using hr
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
  rcases hg with hp | hp
  · have hPL : pointParabolic (F := F) ≤ normalizer (pointLocal (F := F) : Set (Sp F)) :=
      (normal_subgroupOf_iff_le_normalizer (pointLocal_le (F := F))).mp inferInstance
    have hc := normalizer_eq_parabolic_or_sylow U pointParabolic pointLocal hu
      (twoGroup_le_determinantKernel U hu.isPGroup (point F) (U.le_normalizer.trans hp))
      hp hPL pointQuotient pointQuotient_surjective
      (IsElementaryAbelian.isPGroup 2 pointRadical) (unipotentSylow hF hn) inf_le_left
    rcases hc with he | ⟨S,hS⟩
    · exact Or.inl ⟨g,Or.inl (hmap.trans he)⟩
    · exact Or.inr (hsyl S hS)
  · have hPL : planeParabolic (F := F) ≤ normalizer (planeLocal (F := F) : Set (Sp F)) :=
      (normal_subgroupOf_iff_le_normalizer (planeLocal_le (F := F))).mp inferInstance
    have hc := normalizer_eq_parabolic_or_sylow U planeParabolic planeLocal hu
      (twoGroup_le_determinantKernel U hu.isPGroup (plane F) (U.le_normalizer.trans hp))
      hp hPL Plane.quotientMap Plane.quotientMap_surjective
      (IsElementaryAbelian.isPGroup 2 Plane.radical) (unipotentSylow hF hn) inf_le_right
    rcases hc with he | ⟨S,hS⟩
    · exact Or.inl ⟨g,Or.inr (hmap.trans he)⟩
    · exact Or.inr (hsyl S hS)

/-- Every nontrivial two-radical normalizer is a full point or plane parabolic,
or the full Borel, up to actual symplectic conjugacy. -/
theorem radical_normalizer_eq_parabolic_or_borel
    (R : Subgroup (Sp F)) (hR : R.IsPRadical 2) :
    ∃ g : Sp F,
      (normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom = planeParabolic ∨
      (normalizer (R : Set (Sp F))).map (MulAut.conj g).toMonoidHom = borel := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n,_,hcard⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hn : 1 ≤ (n : ℕ) := by
    have hpos := Finite.one_lt_card (α := F)
    by_contra hn
    have hn0 : (n : ℕ) = 0 := by omega
    rw [hF,hn0,pow_zero] at hpos
    omega
  rcases radical_normalizer_parabolic_or_sylow R hR hF hn with ⟨g,hg⟩ | ⟨S,hS⟩
  · exact ⟨g,hg.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
  · obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF hn)
    refine ⟨g,Or.inr (Or.inr ?_)⟩
    rw [←hS,map_equiv_normalizer_eq]
    have hh : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
      congrArg Sylow.toSubgroup hg
    rw [hh,←borel_eq_normalizer_unipotent]
end Theory.SpecificGroups.SymplecticFour
