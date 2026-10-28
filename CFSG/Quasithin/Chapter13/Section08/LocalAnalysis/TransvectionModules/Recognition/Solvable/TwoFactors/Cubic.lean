module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.FactorAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.Support
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# The incompatible Sylow action on cubic subgroups

A subgroup of order three in S₃ × S₃ normalized by a full Sylow two-subgroup
lies in a coordinate factor. After Sylow conjugacy, a coordinate involution
either fixes or inverts that subgroup; the two possibilities force one of
the cubic coordinates to be trivial. The finite permutation calculations
are checked in the kernel.

The coordinate-compatible B.1.8 factors transfer this assertion back to
the original group. A transvection belongs to one factor, and normal
generation forces the ambient Sylow two-subgroup to swap both factors.
Its restriction to the normal closure is Sylow. Hence no subgroup of order
three in the closure is invariant under the ambient Sylow two-subgroup.

This establishes the group-action half of the two-factor argument. The
source still has to place L₁* in the closure and construct its invariant
cubic subgroup from the marked local geometry.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.5, printed p.947 (PDF p.964).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
open ChapterB
local notation "S3" => Equiv.Perm (Fin 3)
private def flip : S3 := Equiv.swap 0 1
private def standard : Subgroup (S3 × S3) where
  carrier := {x | (x.1 = 1 ∨ x.1 = flip) ∧ (x.2 = 1 ∨ x.2 = flip)}
  one_mem' := by simp
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel
private instance : DecidablePred (· ∈ standard) := fun x =>
  inferInstanceAs (Decidable ((x.1 = 1 ∨ x.1 = flip) ∧ (x.2 = 1 ∨ x.2 = flip)))
private theorem standard_card : Nat.card standard = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private noncomputable def standardSylow : Sylow 2 (S3 × S3) := Sylow.ofCard standard (by
  rw [standard_card]
  have he : Nat.card (S3 × S3) = 36 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [he, show (36 : ℕ) = 2 ^ 2 * 3 ^ 2 from rfl,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization]
  norm_num)

private theorem cubic_axis_of_flip (x : S3 × S3) (hx : x ^ 3 = 1)
    (hf : Commute (flip, (1 : S3)) x ∨
      (flip, (1 : S3)) * x * (flip, (1 : S3))⁻¹ = x⁻¹) : x.1 = 1 ∨ x.2 = 1 := by
  revert x
  simp only [Commute, SemiconjBy]
  decide +kernel

private theorem cubic_le_coordinate_standard (C : Subgroup (S3 × S3))
    (hC : Nat.card C = 3) (hS : standard ≤ normalizer (C : Set (S3 × S3))) :
    C ≤ (⊤ : Subgroup S3).prod ⊥ ∨ C ≤ (⊥ : Subgroup S3).prod ⊤ := by
  have hcyc := isCyclic_of_prime_card hC
  obtain ⟨c, hc⟩ := C.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hcmem : c ∈ C := hc ▸ mem_zpowers c
  have hc3 : c ^ 3 = 1 := by
    have he := congrArg Subtype.val (pow_card_eq_one' (x := (⟨c, hcmem⟩ : C)))
    change c ^ (Nat.card C) = 1 at he
    rwa [hC] at he
  have hn : (flip, (1 : S3)) ∈ normalizer (C : Set (S3 × S3)) :=
    hS ⟨Or.inr rfl, Or.inl rfl⟩
  have hs : (flip, (1 : S3)) ^ 2 = 1 := by decide +kernel
  have hci := centralizes_or_inverts_prime_subgroup_of_sq_eq_one C
    (by rw [hC]; exact Nat.prime_three) (flip, (1 : S3)) hs hn
  have hx : c.1 = 1 ∨ c.2 = 1 := cubic_axis_of_flip c hc3
    (hci.imp (fun h => h c hcmem) (fun h => h c hcmem))
  rw [← hc]
  exact hx.elim (fun h => Or.inr (zpowers_le.mpr ⟨h, mem_top _⟩))
    (fun h => Or.inl (zpowers_le.mpr ⟨mem_top _, h⟩))

/-- A cubic subgroup normalized by a full Sylow two-subgroup of S₃ × S₃
lies on a coordinate axis. -/
theorem cubic_le_coordinate (C : Subgroup (S3 × S3)) (hC : Nat.card C = 3)
    (S : Sylow 2 (S3 × S3)) (hS : (S : Subgroup (S3 × S3)) ≤ normalizer (C : Set (S3 × S3))) :
    C ≤ (⊤ : Subgroup S3).prod ⊥ ∨ C ≤ (⊥ : Subgroup S3).prod ⊤ := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (S3 × S3) S standardSylow
  let f := (MulAut.conj a).toMonoidHom
  have hstd : standard ≤ normalizer (C.map f : Set (S3 × S3)) := by
    have he : (S : Subgroup (S3 × S3)).map f = standard :=
      congrArg (fun P : Sylow 2 (S3 × S3) => (P : Subgroup (S3 × S3))) ha
    rw [← he]
    exact (map_mono hS).trans (C.le_normalizer_map f)
  have hcard : Nat.card (C.map f) = 3 := by
    rw [card_map_of_injective (MulAut.conj a).injective, hC]
  have haxis := cubic_le_coordinate_standard (C.map f) hcard hstd
  have hback (B : Subgroup (S3 × S3)) [B.Normal] (h : C.map f ≤ B) : C ≤ B := by
    intro c hc
    have hb := (inferInstance : B.Normal).conj_mem _ (h (mem_map_of_mem f hc)) a⁻¹
    have he : a⁻¹ * (a * c * a⁻¹) * (a⁻¹)⁻¹ = c := by group
    exact he ▸ hb
  exact haxis.imp (hback _) (hback _)

private def firstCoordinateEquiv : ↥((⊤ : Subgroup S3).prod (⊥ : Subgroup S3)) ≃* S3 where
  toFun x := x.val.1
  invFun x := ⟨(x, 1), mem_top _, rfl⟩
  left_inv x := Subtype.ext (Prod.ext rfl x.property.2.symm)
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def secondCoordinateEquiv : ↥((⊥ : Subgroup S3).prod (⊤ : Subgroup S3)) ≃* S3 where
  toFun x := x.val.2
  invFun x := ⟨(1, x), rfl, mem_top _⟩
  left_inv x := Subtype.ext (Prod.ext x.property.1.symm rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E}

/-- Cubic-axis rigidity respects the original coordinate subgroups. -/
theorem cubic_le_factor (d : SolvableFFFactors ρ)
    (hJ : offenderSubgroup ρ = ⊤) (hc : d.count = 2)
    (C : Subgroup A) (hC : Nat.card C = 3) (S : Sylow 2 A)
    (hS : (S : Subgroup A) ≤ normalizer (C : Set A)) :
    ∃ i, C ≤ d.factor i := by
  let e := twoFactorModel d hJ hc
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card (C.map e.toMonoidHom) = 3 := by
    rw [card_map_of_injective e.injective, hC]
  have hn : (P : Subgroup _) ≤ normalizer (C.map e.toMonoidHom : Set (S3 × S3)) :=
    (map_mono hS).trans (C.le_normalizer_map e.toMonoidHom)
  have haxis := cubic_le_coordinate _ hcard P hn
  have hback (B : Subgroup (S3 × S3)) [B.Normal] (eB : B ≃* S3)
      (hB : C.map e.toMonoidHom ≤ B) : ∃ i, C ≤ d.factor i := by
    let N := B.map e.symm.toMonoidHom
    let : N.Normal := (inferInstance : B.Normal).map _ e.symm.surjective
    obtain ⟨i, hi⟩ := normal_symmetricThree_eq_factor d hJ hc N
      ((e.symm.subgroupMap B).symm.trans eB)
    refine ⟨i, ?_⟩
    rw [← hi]
    intro c hcm
    exact ⟨e c, hB (mem_map_of_mem _ hcm), e.symm_apply_apply c⟩
  exact haxis.elim (hback _ firstCoordinateEquiv) (hback _ secondCoordinateEquiv)

private theorem moves_all_of_moves_one {n : ℕ} (hn : n = 2)
    (p : Equiv.Perm (Fin n)) (i j : Fin n) (hi : p i ≠ i) : p j ≠ j := by
  subst n
  revert p i j
  decide

/-- Normal generation by a transvection forces a Sylow element to interchange
both actual factors. No transitivity premise is used. -/
theorem sylow_swaps_factors (t : A) (ht : IsTransvection ρ t)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) (T : Sylow 2 A) :
    ∃ a ∈ (T : Subgroup A), ∀ i,
      (factorAction t d hJ hc).permutation a i ≠ i := by
  let K := normalClosure ({t} : Set A)
  let tK : K := ⟨t, subset_normalClosure (Set.mem_singleton t)⟩
  have htK : IsTransvection (ρ.comp K.subtype) tK := ht
  have hm : tK ∈ offenderSubgroup (ρ.comp K.subtype) := by rw [hJ]; trivial
  obtain ⟨i, hi⟩ := transvection_mem_factor d tK htK hm
  have htF : t ∈ ambientFactor t d i := ⟨tK, hi, rfl⟩
  obtain ⟨a, ha, hmove⟩ := sylow_moves_factor t d hJ hc (factorAction t d hJ hc) i htF T
  exact ⟨a, ha, fun j => moves_all_of_moves_one hc _ i j hmove⟩

/-- The two-factor normal closure admits no T-invariant cubic subgroup.
The Sylow restriction is genuine, and the factor permutation and its
transitivity have both been constructed from the transvection and its closure. -/
theorem no_invariant_cubic (t : A) (ht : IsTransvection ρ t)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) (T : Sylow 2 A)
    (C : Subgroup A) (hCK : C ≤ normalClosure ({t} : Set A))
    (hC : Nat.card C = 3) (hTC : (T : Subgroup A) ≤ normalizer (C : Set A)) : False := by
  let K := normalClosure ({t} : Set A)
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hn : (S : Subgroup K) ≤ normalizer (C.subgroupOf K : Set K) := by
    rw [hS]
    intro s hs
    apply mem_normalizer_iff.mpr
    intro c
    change ((c : A) ∈ C ↔ (s : A) * (c : A) * (s : A)⁻¹ ∈ C)
    exact mem_normalizer_iff.mp (hTC hs) c
  have hcard : Nat.card (C.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCK).toEquiv, hC]
  obtain ⟨i, hi⟩ := cubic_le_factor d hJ hc (C.subgroupOf K) hcard S hn
  have hCF : C ≤ ambientFactor t d i := by
    intro c hcm
    exact ⟨⟨c, hCK hcm⟩, hi hcm, rfl⟩
  obtain ⟨a, ha, hmove⟩ := sylow_swaps_factors t ht d hJ hc T
  let α := factorAction t d hJ hc
  have hCj : C ≤ ambientFactor t d (α.permutation a i) := by
    rw [← α.map_factor, ← mem_normalizer_iff_map_conj_eq.mp (hTC ha)]
    exact map_mono hCF
  have hdis : Disjoint (ambientFactor t d (α.permutation a i)) (ambientFactor t d i) :=
    disjoint_map K.subtype_injective (d.factors_independent.pairwiseDisjoint (hmove i))
  have hbot : C = ⊥ := le_bot_iff.mp ((le_inf hCj hCF).trans (disjoint_iff.mp hdis).le)
  rw [hbot, card_bot] at hC
  norm_num at hC

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors

end
