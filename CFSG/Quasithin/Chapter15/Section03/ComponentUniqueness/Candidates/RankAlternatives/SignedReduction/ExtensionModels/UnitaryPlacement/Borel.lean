module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.SU3.BorelTorus.EvenCenterAction

/-!
# Cubic elements and involutions in a unitary Borel

For the standard PSU₃(q), q = 2ⁿ congruent to -1 modulo three, every
order-three element of a Sylow normalizer centralizes every involution in
that Sylow subgroup. Squaring in the actual root coordinates puts the
involution in the central root group. The Borel acts there by scalars in
the fixed field, whose multiplicative group has order q - 1 prime to three.

The scalar action is proved for the full root--torus Borel, including its
projective scalar kernel. The actual root Sylow and Sylow conjugacy then
transport the conclusion to arbitrary coordinates in an isomorphic group.
The matrix field retains order q² and the supplied involution is q-Frobenius.

This is the intrinsic input to the local placement step in 15.3.43, printed
p.1139, of Aschbacher--Smith, combined manuscript (1 March 2004). The root
formulas and Sylow-normalizer identification are the existing Huppert
II.10.12 and F.1.3(1) calculations, not hypotheses on the local actor.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels.UnitaryPlacement

variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private def scalarActors : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) where
  carrier := {g | ∃ a : (fixedField J)ˣ, ∀ b : Multiplicative (fixedField J),
    g * centralMap J hJ b * g⁻¹ =
      centralMap J hJ (.ofAdd ((a : fixedField J) * b.toAdd))}
  one_mem' := ⟨1, by intro b; simp⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨c, hc⟩
    refine ⟨a * c, fun b => ?_⟩
    calc
      (g * h) * centralMap J hJ b * (g * h)⁻¹ =
          g * (h * centralMap J hJ b * h⁻¹) * g⁻¹ := by group
      _ = centralMap J hJ (.ofAdd (((a * c : (fixedField J)ˣ) : fixedField J) * b.toAdd)) := by
        rw [hc, ha]
        simp only [toAdd_ofAdd, Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, fun b => ?_⟩
    have hh := ha (.ofAdd (((a⁻¹ : (fixedField J)ˣ) : fixedField J) * b.toAdd))
    simp only [toAdd_ofAdd, ← mul_assoc, Units.mul_inv, one_mul] at hh
    have he := congrArg (fun z => g⁻¹ * z * g) hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, inv_inv, ofAdd_toAdd] using he.symm

private theorem borel_le_scalarActors : projectiveBorel J hJ ≤ scalarActors J hJ := by
  refine sup_le ?_ ?_
  · intro g hg
    refine ⟨1, fun b => ?_⟩
    have hc := mem_centralizer_iff.mp (root_centralizes J hJ hg)
      (centralMap J hJ b) ⟨b, rfl⟩
    simpa only [Units.val_one, one_mul, ofAdd_toAdd] using
      mul_inv_eq_iff_eq_mul.mpr hc.symm
  · rintro _ ⟨k, rfl⟩
    exact ⟨inverseNorm J k, projective_torus_central J hJ k⟩

private theorem root_square_one_mem_centralImage
    {w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw : w ∈ projectiveRoot J hJ) (hsq : w ^ 2 = 1) :
    w ∈ centralImage J hJ := by
  obtain ⟨z, rfl⟩ := hw
  have hz : z ^ 2 = 1 := (EvenInner.root_injective J hJ) (by
    rw [map_pow, map_one]; exact hsq)
  have he := congrArg (fun x : hermitianUnipotentCoord J => x.1.2) hz
  rw [pow_two] at he
  change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0 at he
  rw [CharTwo.add_self_eq_zero, zero_sub, neg_eq_zero] at he
  have hz0 : z.1.1 = 0 := (mul_eq_zero.mp he).elim id ((map_eq_zero J.conj).mp)
  have hfix : J.conj z.1.2 = z.1.2 := by
    have h := z.2
    rw [hz0, zero_mul, add_zero] at h
    exact (eq_neg_of_add_eq_zero_right h).trans (CharTwo.neg_eq _)
  refine ⟨.ofAdd ⟨z.1.2, hfix⟩, ?_⟩
  change hermitianUnipotentPSU J hJ (centralCoord J _) = _
  congr 1
  exact Subtype.ext (Prod.ext hz0.symm rfl)

private theorem standard_cubic_centralizes [Finite F] {q : ℕ}
    (hfixed : Nat.card {x : F // J.conj x = x} = q) (hq : q % 3 = 2)
    {y : ProjectiveSpecialUnitaryMatrixGroup J}
    (hy : y ∈ projectiveBorel J hJ) (hy3 : y ^ 3 = 1) :
    y ∈ centralizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨a, ha⟩ := borel_le_scalarActors J hJ hy
  have hpow (b : Multiplicative (fixedField J)) :
      y ^ 3 * centralMap J hJ b * (y ^ 3)⁻¹ =
        centralMap J hJ (.ofAdd ((a : fixedField J) ^ 3 * b.toAdd)) := by
    calc
      _ = y * (y * (y * centralMap J hJ b * y⁻¹) * y⁻¹) * y⁻¹ := by simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]; group
      _ = _ := by rw [ha, ha, ha]; congr 2; simp only [toAdd_ofAdd]; ring
  have hc := hpow (.ofAdd 1)
  rw [hy3, inv_one, one_mul, mul_one] at hc
  have ha3 : a ^ 3 = 1 := by
    apply Units.ext
    have hh := congrArg Multiplicative.toAdd ((centralMap_injective J hJ) hc)
    simpa only [toAdd_ofAdd, mul_one, Units.val_pow_eq_pow_val, Units.val_one] using hh.symm
  have hcard : Nat.card (fixedField J)ˣ = q - 1 := by
    rw [Nat.card_units]
    exact congrArg (fun k => k - 1) hfixed
  have hcop : Nat.Coprime 3 (Nat.card (fixedField J)ˣ) := by
    rw [hcard, Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)]
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  have ha1 : a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha3) (orderOf_dvd_natCard a))
  apply mem_centralizer_iff.mpr
  rintro _ ⟨b, rfl⟩
  have hh := ha b
  rw [ha1] at hh
  simpa only [Units.val_one, one_mul, ofAdd_toAdd] using
    (mul_inv_eq_iff_eq_mul.mp hh).symm


include hJ in
omit [CharP F 2] in
/-- An element of exponent three in the Borel fixes every involution of its Sylow. -/
theorem cubic_commutes_of_mem_sylowNormalizer
    [Finite F] {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hfrob : ∀ x, J.conj x = x ^ (2 ^ n)) (hq : (2 ^ n) % 3 = 2)
    (e : H ≃* ProjectiveSpecialUnitaryMatrixGroup J) (P : Sylow 2 H)
    {y w : H} (hy : y ∈ normalizer (P : Set H)) (hy3 : y ^ 3 = 1)
    (hw : w ∈ P) (hw2 : w ^ 2 = 1) : w * y = y * w := by
  let : CharP F 2 := ChapterF.Source.Unitary.charP_two n hn hcard
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective e e.surjective
  obtain ⟨_, _, T, hT, _⟩ := ChapterF.Source.Unitary.standard_su_borel_data J n hn hcard hfrob hJ
  let Q := T.mapSurjective (ChapterF.Source.Unitary.suProjection_surjective J)
  have hQ : (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = projectiveRoot J hJ := by
    change (T : Subgroup J.specialSubgroup).map (ChapterF.Source.Unitary.suProjection J) = _
    rw [hT]
    exact ChapterF.Source.Unitary.suRoot_map_projection J hJ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J)
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) Q
  let f := e.trans (MulAut.conj g)
  have hP : (P : Subgroup H).map f.toMonoidHom = projectiveRoot J hJ := by
    change (P : Subgroup H).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← Subgroup.map_map, ← hQ]
    exact congrArg Sylow.toSubgroup hg
  obtain ⟨_, _, _, _, _, _, hgen, hnorm, _⟩ :=
    ChapterF.Source.Unitary.standard_projective_matrix_borel J n hn hcard hfrob hJ
  have hN : (normalizer (P : Set H)).map f.toMonoidHom = projectiveBorel J hJ := by
    change (normalizer ((P : Subgroup H) : Set H)).map f.toMonoidHom = _
    rw [map_equiv_normalizer_eq, hP]
    exact hnorm.trans hgen.symm
  have hyB : f y ∈ projectiveBorel J hJ := hN ▸ mem_map_of_mem f.toMonoidHom hy
  have hwR : f w ∈ projectiveRoot J hJ := hP ▸ mem_map_of_mem f.toMonoidHom hw
  have hc := standard_cubic_centralizes J hJ
    (ChapterF.Source.Unitary.fixed_card J n hn hcard hfrob) hq hyB
    (by rw [← map_pow, hy3, map_one])
  have hwC := root_square_one_mem_centralImage J hJ hwR
    (by rw [← map_pow, hw2, map_one])
  apply f.injective
  simpa only [map_mul] using mem_centralizer_iff.mp hc (f w) hwC


end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels.UnitaryPlacement
