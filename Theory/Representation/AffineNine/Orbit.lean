module

public import Theory.Representation.AffineNine.Model
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Dual orbit covers for the affine-nine plane

The affine-nine model has nine dual weights.  This module supplies the finite
orbit input used by the strict cubic-ratio estimate: a nontrivial elementary
abelian 2-subgroup of `GL₂(3)` has at most six dual orbits in rank one and at
most four in rank two, with zero isolated as one representative.  The
fixed-point estimates are checked by the finite matrix certificate below, and
Burnside's identity turns them into the orbit bounds.

The complementary `SL₂(3)` fact is the source assertion that commuting
nonidentity involutions cannot be distinct; consequently an elementary
abelian subgroup of the special-linear complement has rank at most one.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 15.4.10, printed p.1159.
-/

open Matrix
open MulAction
open scoped MatrixGroups BigOperators
set_option linter.style.haveILetI false

public section
namespace Representation.AffineNine

def dualPermHom : LinearGroup →* Equiv.Perm Plane where
  toFun := dualPerm
  map_one' := by ext w i; simp [dualPerm]
  map_mul' := by
    intro g h
    ext w
    simp [dualPerm, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, _root_.mul_inv_rev]

@[instance_reducible] def dualSMul (B : Subgroup LinearGroup) : SMul B Plane where
  smul b w := dualPerm (b : LinearGroup) w

@[instance_reducible] def dualMulAction (B : Subgroup LinearGroup) : MulAction B Plane where
  smul := dualSMul B |>.smul
  one_smul w := by change dualPerm (1 : LinearGroup) w = w; simp [dualPerm]
  mul_smul b c w := by
    change dualPerm ((b : LinearGroup) * (c : LinearGroup)) w =
      dualPerm (b : LinearGroup) (dualPerm (c : LinearGroup) w)
    exact congrArg (fun e : Equiv.Perm Plane => e w) (dualPermHom.map_mul b c)

abbrev DualOrbitQuotient (B : Subgroup LinearGroup) :=
  @MulAction.orbitRel.Quotient B Plane _ (dualMulAction B)

theorem matrix_fixed_bound : ∀ m : Matrix (Fin 2) (Fin 2) (ZMod 3), m * m = 1 → m ≠ 1 →
    Fintype.card {w : Plane // m.transpose *ᵥ w = w} ≤ 3 := by
  decide +kernel

theorem dual_fixed_card_le_three (g : LinearGroup) (h2 : g ^ 2 = 1) (hne : g ≠ 1) :
    Fintype.card {w : Plane // dualPerm g w = w} ≤ 3 := by
  have hm : g.val * g.val = 1 := by
    simpa [pow_two] using congrArg (fun x : LinearGroup => x.val) h2
  have hmn : g.val ≠ 1 := by
    intro h
    apply hne
    exact Units.ext (by simpa using h)
  have h := matrix_fixed_bound g.val hm hmn
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
  simpa [dualPerm, hinv] using h

theorem exists_dual_orbit_cover (B : Subgroup LinearGroup) :
    ∃ S : Finset Plane, 0 ∈ S ∧
      (∀ w : Plane, ∃ b : B, dualPerm (b : LinearGroup) w ∈ S) ∧
      S.card ≤ Nat.card (DualOrbitQuotient B) := by
  letI : SMul B Plane := dualSMul B
  letI : MulAction B Plane := dualMulAction B
  classical
  let _ : Fintype (DualOrbitQuotient B) := Fintype.ofFinite _
  let U : Finset (DualOrbitQuotient B) := Finset.univ
  let S : Finset Plane := U.image (fun q => Quotient.out q)
  refine ⟨S, ?_, ?_, ?_⟩
  · let q : DualOrbitQuotient B := ⟦(0 : Plane)⟧
    have hmemq : Quotient.out q ∈ q.orbit :=
      orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' q)
    have hmem : Quotient.out q ∈ MulAction.orbit B (0 : Plane) := by
      simpa [q] using hmemq
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hmem
    have hz : b • (0 : Plane) = 0 := by
      change dualPerm (b : LinearGroup) 0 = 0
      simp [dualPerm]
    have hout : Quotient.out q = 0 := by simpa [hz] using hb.symm
    rw [← hout]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  · intro w
    let q : DualOrbitQuotient B := ⟦w⟧
    have hmemq : Quotient.out q ∈ q.orbit :=
      orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' q)
    have hmem : Quotient.out q ∈ MulAction.orbit B w := by
      simpa [q] using hmemq
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp hmem
    refine ⟨b, ?_⟩
    have hb' : dualPerm (b : LinearGroup) w = Quotient.out q := by
      change dualPerm (b : LinearGroup) w = Quotient.out q at hb
      exact hb
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hb'.symm⟩
  · rw [Nat.card_eq_fintype_card]
    simpa [S, U] using (Finset.card_image_le : (U.image (fun q => Quotient.out q)).card ≤ U.card)

theorem dual_orbit_quotient_card_bound (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B)
    (hcard : Nat.card B = 2 ∨ Nat.card B = 4) :
    Nat.card (DualOrbitQuotient B) ≤ 6 ∧
      (Nat.card B = 4 → Nat.card (DualOrbitQuotient B) ≤ 4) := by
  classical
  let ffix : ∀ b : B, Fintype (@MulAction.fixedBy B Plane _ (dualMulAction B) b) :=
    fun b => Fintype.ofFinite _
  let fq : Fintype (DualOrbitQuotient B) := Fintype.ofFinite _
  let fb : Fintype B := Fintype.ofFinite _
  have hterm (b : B) :
      Fintype.card (@MulAction.fixedBy B Plane _ (dualMulAction B) b) ≤
        if b = 1 then 9 else 3 := by
    by_cases hb : b = 1
    · rw [if_pos hb]
      have hle := Fintype.card_subtype_le (fun w : Plane => w ∈ @MulAction.fixedBy B Plane _ (dualMulAction B) b)
      simpa only [card_plane] using hle
    · rw [if_neg hb]
      have hb2 : (b : LinearGroup) ^ 2 = 1 := by
        letI : IsElementaryAbelian 2 B := hB.2
        exact elemPow_eq_one_of_isElementaryAbelian (b : LinearGroup) b.property
      have hhN : Nat.card {w : Plane // dualPerm (b : LinearGroup) w = w} ≤ 3 := by
        rw [Nat.card_eq_fintype_card]
        exact dual_fixed_card_le_three (b : LinearGroup) hb2 (by simpa using hb)
      have hfixN : Nat.card (@MulAction.fixedBy B Plane _ (dualMulAction B) b) ≤ 3 := by
        change Nat.card {w : Plane // dualPerm (b : LinearGroup) w = w} ≤ 3
        exact hhN
      simpa only [Nat.card_eq_fintype_card] using hfixN
  have hsum :
      (∑ b : B, Fintype.card (@MulAction.fixedBy B Plane _ (dualMulAction B) b)) ≤
        ∑ b : B, (if b = 1 then 9 else 3) :=
    Finset.sum_le_sum (fun b _ => hterm b)
  have hburn :
      (∑ b : B, Fintype.card (@MulAction.fixedBy B Plane _ (dualMulAction B) b)) =
        Fintype.card (DualOrbitQuotient B) * Fintype.card B :=
    @MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      B Plane _ (dualMulAction B) fb ffix fq
  have hq : Fintype.card (DualOrbitQuotient B) * Fintype.card B ≤
      ∑ b : B, (if b = 1 then 9 else 3) := by
    calc
      _ = ∑ b : B, Fintype.card (@MulAction.fixedBy B Plane _ (dualMulAction B) b) := hburn.symm
      _ ≤ _ := hsum
  have hsum' : (∑ b : B, (if b = 1 then 9 else 3)) =
      9 + 3 * (Fintype.card B - 1) := by
    let s : Finset B := Finset.univ
    change (s.sum (fun b => if b = 1 then 9 else 3)) = _
    have hs := Finset.sum_erase_add s (fun b : B => if b = 1 then 9 else 3)
      (show (1 : B) ∈ s by simp [s])
    rw [← hs]
    have he : (s.erase 1).sum (fun b : B => if b = 1 then 9 else 3) =
        (s.erase 1).card * 3 := by
      calc
        _ = (s.erase 1).sum (fun _ => 3) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hne : b ≠ (1 : B) := (Finset.mem_erase.mp hb).1
          simp [hne]
        _ = _ := by simp [Finset.sum_const]
    rw [he, Finset.card_erase_of_mem (show (1 : B) ∈ s by simp [s])]
    simp [s]
    omega
  rw [hsum'] at hq
  have hcard' : Fintype.card B = 2 ∨ Fintype.card B = 4 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hqcard6 : Fintype.card (DualOrbitQuotient B) ≤ 6 := by
    rcases hcard' with h | h
    · rw [h] at hq
      omega
    · rw [h] at hq
      omega
  have hqcard4 : Nat.card B = 4 → Nat.card (DualOrbitQuotient B) ≤ 4 := by
    intro h4
    have h4' : Fintype.card B = 4 := by
      simpa only [Nat.card_eq_fintype_card] using h4
    rw [h4'] at hq
    have hh : Fintype.card (DualOrbitQuotient B) ≤ 4 := by omega
    simpa only [Nat.card_eq_fintype_card] using hh
  exact ⟨by simpa only [Nat.card_eq_fintype_card] using hqcard6, hqcard4⟩


theorem dual_orbit_quotient_card_le_six (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B)
    (hcard : Nat.card B = 2) : Nat.card (DualOrbitQuotient B) ≤ 6 :=
  (dual_orbit_quotient_card_bound B hB (Or.inl hcard)).1

theorem dual_orbit_quotient_card_le_four (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B)
    (hcard : Nat.card B = 4) : Nat.card (DualOrbitQuotient B) ≤ 4 :=
  (dual_orbit_quotient_card_bound B hB (Or.inr hcard)).2 hcard


theorem exists_dual_orbit_cover_rank_one (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B)
    (hrank : Representation.BinaryOffender.rank B = 1) :
    ∃ S : Finset Plane, 0 ∈ S ∧
      (∀ w : Plane, ∃ b : B, dualPerm (b : LinearGroup) w ∈ S) ∧
      S.card ≤ 6 ∧ (S.erase 0).card ≤ 5 := by
  have hcard : Nat.card B = 2 := by
    rw [hB.card_eq_two_pow_rank, hrank]
    norm_num
  obtain ⟨S, h0, hcover, hScard⟩ := exists_dual_orbit_cover B
  have hS := hScard.trans (dual_orbit_quotient_card_le_six B hB hcard)
  refine ⟨S, h0, hcover, hS, ?_⟩
  rw [Finset.card_erase_of_mem h0]
  omega

theorem exists_dual_orbit_cover_rank_two (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B)
    (hrank : Representation.BinaryOffender.rank B = 2) :
    ∃ S : Finset Plane, 0 ∈ S ∧
      (∀ w : Plane, ∃ b : B, dualPerm (b : LinearGroup) w ∈ S) ∧
      S.card ≤ 4 ∧ (S.erase 0).card ≤ 3 := by
  have hcard : Nat.card B = 4 := by
    rw [hB.card_eq_two_pow_rank, hrank]
    norm_num
  obtain ⟨S, h0, hcover, hScard⟩ := exists_dual_orbit_cover B
  have hS := hScard.trans (dual_orbit_quotient_card_le_four B hB hcard)
  refine ⟨S, h0, hcover, hS, ?_⟩
  rw [Finset.card_erase_of_mem h0]
  omega



theorem matrix_commuting_involutions_card : ∀ m : Matrix (Fin 2) (Fin 2) (ZMod 3),
    m * m = 1 → m ≠ 1 → m ≠ -1 →
    Fintype.card {n : Matrix (Fin 2) (Fin 2) (ZMod 3) //
      n * n = 1 ∧ m * n = n * m} ≤ 4 := by
  decide +kernel

private theorem card_le_matrix_pred (B : Subgroup LinearGroup)
    (P : Matrix (Fin 2) (Fin 2) (ZMod 3) → Prop) [DecidablePred P]
    (hP : ∀ b : B, P (b : LinearGroup).val) :
    Nat.card B ≤ Fintype.card {m // P m} := by
  classical
  let : Fintype B := Fintype.ofFinite _
  let f : B → {m // P m} := fun b => ⟨(b : LinearGroup).val, hP b⟩
  have hf : Function.Injective f := by
    intro b c h
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

theorem elementary_linear_card_le_four (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B) : Nat.card B ≤ 4 := by
  classical
  let : IsElementaryAbelian 2 B := hB.2
  by_cases hs : ∀ b : B, (b : LinearGroup).val = 1 ∨ (b : LinearGroup).val = -1
  · have h := card_le_matrix_pred B (fun m => m = 1 ∨ m = -1) hs
    have hc : Fintype.card {m : Matrix (Fin 2) (Fin 2) (ZMod 3) //
        m = 1 ∨ m = -1} = 2 := by
      decide +kernel
    omega
  · obtain ⟨b, hb⟩ := not_forall.mp hs
    have hb2 : (b : LinearGroup).val * (b : LinearGroup).val = 1 := by
      have h := elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (b : LinearGroup) b.property
      simpa only [pow_two, Units.val_mul, Units.val_one] using
        congrArg (fun g : LinearGroup => g.val) h
    have hcomm (c : B) : (b : LinearGroup).val * (c : LinearGroup).val =
        (c : LinearGroup).val * (b : LinearGroup).val := by
      have h := (IsMulCommutative.is_comm (M := B)).comm b c
      exact congrArg (fun x : B => (x : LinearGroup).val) h
    have h := card_le_matrix_pred B
      (fun n => n * n = 1 ∧ (b : LinearGroup).val * n = n * (b : LinearGroup).val) (by
        intro c
        refine ⟨?_, hcomm c⟩
        have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2)
          (c : LinearGroup) c.property
        simpa only [pow_two, Units.val_mul, Units.val_one] using
          congrArg (fun g : LinearGroup => g.val) hh)
    exact h.trans (matrix_commuting_involutions_card (b : LinearGroup).val hb2
      (fun hh => hb (Or.inl hh)) (fun hh => hb (Or.inr hh)))

theorem elementary_linear_rank_one_or_two (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B) :
    Representation.BinaryOffender.rank B = 1 ∨
      Representation.BinaryOffender.rank B = 2 := by
  have hcard := elementary_linear_card_le_four B hB
  have hpos := hB.rank_pos
  have hrank : Representation.BinaryOffender.rank B ≤ 2 := by
    by_contra h
    have hh : 3 ≤ Representation.BinaryOffender.rank B := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hB.card_eq_two_pow_rank] at hp
    norm_num at hp
    omega
  omega

theorem exists_dual_orbit_cover_strict (B : Subgroup LinearGroup)
    (hB : Representation.BinaryOffender.IsElementaryTwo B) :
    ∃ S : Finset Plane, 0 ∈ S ∧
      (∀ w : Plane, ∃ b : B, dualPerm (b : LinearGroup) w ∈ S) ∧
      S.card ≤ 6 ∧ (S.erase 0).card ≤ 5 ∧
      S.card + 2 * Representation.BinaryOffender.rank B < 9 := by
  obtain hr | hr := elementary_linear_rank_one_or_two B hB
  · obtain ⟨S, h0, hcover, hcard, hnonzero⟩ :=
      exists_dual_orbit_cover_rank_one B hB hr
    refine ⟨S, h0, hcover, hcard, hnonzero, ?_⟩
    omega
  · obtain ⟨S, h0, hcover, hcard, hnonzero⟩ :=
      exists_dual_orbit_cover_rank_two B hB hr
    have hcard6 : S.card ≤ 6 := by omega
    have hnonzero5 : (S.erase 0).card ≤ 5 := by omega
    refine ⟨S, h0, hcover, hcard6, hnonzero5, ?_⟩
    omega

theorem special_linear_rank_map_toGL (A : Subgroup SpecialLinear) :
    Representation.BinaryOffender.rank (A.map SpecialLinearGroup.toGL) =
      Representation.BinaryOffender.rank A := by
  unfold Representation.BinaryOffender.rank
  congr 1
  let f := SpecialLinearGroup.toGL.comp A.subtype
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact Subtype.ext (congrArg Subtype.val (SpecialLinearGroup.toGL_injective h))
  have hr : f.range = A.map SpecialLinearGroup.toGL := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem special_linear_elementary_map_toGL {A : Subgroup SpecialLinear}
    (hA : Representation.BinaryOffender.IsElementaryTwo A) :
    Representation.BinaryOffender.IsElementaryTwo (A.map SpecialLinearGroup.toGL) := by
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map SpecialLinearGroup.toGL⟩
  intro hbot
  apply hA.1
  apply le_bot_iff.mp
  intro a ha
  have hm := Subgroup.mem_map_of_mem (SpecialLinearGroup.toGL) ha
  have hz : SpecialLinearGroup.toGL a = 1 := by
    rwa [hbot, Subgroup.mem_bot] at hm
  exact Subtype.ext (congrArg Subtype.val
    (SpecialLinearGroup.toGL_injective (by simpa using hz)))

theorem sl2_commuting_involutions_false : ∀ b c : SpecialLinear,
    b ^ 2 = 1 → c ^ 2 = 1 → b ≠ 1 → c ≠ 1 → b ≠ c →
    b * c = c * b → False := by
  decide +kernel

theorem special_linear_rank_le_one (A : Subgroup SpecialLinear)
    (hA : Representation.BinaryOffender.IsElementaryTwo A) :
    Representation.BinaryOffender.rank A ≤ 1 := by
  classical
  by_contra hr
  have hr2 : 2 ≤ Representation.BinaryOffender.rank A := by omega
  have hpow : Nat.card A = 2 ^ Representation.BinaryOffender.rank A :=
    hA.card_eq_two_pow_rank
  have hpowle : 2 ^ 2 ≤ 2 ^ Representation.BinaryOffender.rank A := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hr2
  have hcard4 : 4 ≤ Nat.card A := by omega
  letI : Fintype A := Fintype.ofFinite A
  let U : Finset A := Finset.univ
  have hcardU : 4 ≤ U.card := by
    simpa [U, Nat.card_eq_fintype_card] using hcard4
  have hone : (1 : A) ∈ U := by simp [U]
  obtain ⟨b, hbU, hbne⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) (1 : A)
  have hUerase : 0 < ((U.erase 1).erase b).card := by
    have hbUerase : b ∈ U.erase 1 := Finset.mem_erase.mpr ⟨hbne, hbU⟩
    rw [Finset.card_erase_of_mem hbUerase, Finset.card_erase_of_mem hone]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hUerase
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hcU : c ∈ U.erase 1 := (Finset.mem_erase.mp hc).2
  have hc1 : c ≠ 1 := (Finset.mem_erase.mp hcU).1
  letI : IsElementaryAbelian 2 A := hA.2
  have hb2 : (b : SpecialLinear) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (b : SpecialLinear) b.property
  have hc2 : (c : SpecialLinear) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (c : SpecialLinear) c.property
  have hcomm : b * c = c * b := (IsMulCommutative.is_comm (M := A)).comm b c
  have hcomm' : (b : SpecialLinear) * (c : SpecialLinear) =
      (c : SpecialLinear) * (b : SpecialLinear) :=
    congrArg Subtype.val hcomm
  exact sl2_commuting_involutions_false b c hb2 hc2 (by simpa using hbne)
    (by simpa using hc1) (by simpa using hcb.symm) hcomm'

end Representation.AffineNine
