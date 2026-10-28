module

public import Theory.SpecificGroups.Tits.FiveFrobenius.Words
public import Theory.SpecificGroups.Tits.FiveFrobenius.Collection
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The concrete five-kernel and its free complement

Cyclic collection gives 25 words in the commuting five-elements and 24 words
in the quaternion-by-three complement. Their permutation images distinguish
all words. Six conjugation identities imply normalization. Evaluation at point
zero detects every nontrivial fixed-point equation, proving freeness.
The generators and word source are documented in `Words` and `Tables`.
-/

namespace Tits.FiveFrobenius
open Subgroup Theory.GroupTheory
set_option maxRecDepth 20000

/-- The actual elementary abelian five-subgroup in the ATLAS group. -/
public def kernel : Subgroup Atlas1600Group := closure {v, u}
/-- The quaternion-by-three subgroup acting on the five-kernel. -/
public def complement : Subgroup Atlas1600Group := closure {t, s, r}

private def kNF (n : Fin 25) : Atlas1600Group := u ^ (n.val % 5) * v ^ (n.val / 5)
private def cNF (n : Fin 24) : Atlas1600Group :=
  r ^ (n.val % 4) * s ^ (n.val / 4 % 2) * t ^ (n.val / 8)
private def kPerm (n : Fin 25) : Equiv.Perm (Fin 1600) :=
  up ^ (n.val % 5) * vp ^ (n.val / 5)
private def cPerm (n : Fin 24) : Equiv.Perm (Fin 1600) :=
  rp ^ (n.val % 4) * sp ^ (n.val / 4 % 2) * tp ^ (n.val / 8)

private theorem kNF_val (n : Fin 25) : (kNF n).val = kPerm n := by
  change u.val ^ _ * v.val ^ _ = _
  rw [u_val, v_val]
  rfl
private theorem cNF_val (n : Fin 24) : (cNF n).val = cPerm n := by
  change r.val ^ _ * s.val ^ _ * t.val ^ _ = _
  rw [r_val, s_val, t_val]
  rfl

private theorem kNF_mem (n : Fin 25) : kNF n ∈ kernel := by
  apply mul_mem
  · exact pow_mem (subset_closure (by simp : u ∈ ({v,u} : Set Atlas1600Group))) _
  · exact pow_mem (subset_closure (by simp : v ∈ ({v,u} : Set Atlas1600Group))) _

private theorem cNF_mem (n : Fin 24) : cNF n ∈ complement := by
  apply mul_mem
  · apply mul_mem
    · exact pow_mem (subset_closure (by simp : r ∈ ({t,s,r} : Set Atlas1600Group))) _
    · exact pow_mem (subset_closure (by simp : s ∈ ({t,s,r} : Set Atlas1600Group))) _
  · exact pow_mem (subset_closure (by simp : t ∈ ({t,s,r} : Set Atlas1600Group))) _

private theorem kNF_surjective {a : Atlas1600Group} (ha : a ∈ kernel) :
    ∃ n : Fin 25, kNF n = a := by
  have hv : ∀ b ∈ ({u} : Set Atlas1600Group), v * b * v⁻¹ ∈ closure {u} := by
    rintro b (rfl : b = u)
    rw [← uv_comm, mul_assoc, mul_inv_cancel, mul_one]
    exact subset_closure (by simp)
  obtain ⟨a₁, h₁, j, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {u} v 5 (by decide) v_fifth hv ha
  obtain ⟨a₀, h₀, i, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert ∅ u 5 (by decide) u_fifth
      (by simp) (by simpa using h₁)
  simp only [closure_empty, mem_bot] at h₀
  subst a₀
  let n : Fin 25 := ⟨i.val + 5*j.val, by omega⟩
  refine ⟨n, ?_⟩
  have hi : n.val % 5 = i.val := by dsimp [n]; omega
  have hj : n.val / 5 = j.val := by dsimp [n]; omega
  simp only [kNF, hi, hj, one_mul]

private theorem cNF_surjective {a : Atlas1600Group} (ha : a ∈ complement) :
    ∃ n : Fin 24, cNF n = a := by
  have ht : ∀ b ∈ ({s,r} : Set Atlas1600Group), t * b * t⁻¹ ∈ closure {s,r} := by
    rintro b (rfl | rfl)
    · rw [t_conj_s]
      exact pow_mem (subset_closure (by simp)) _
    · rw [t_conj_r]
      exact mul_mem (pow_mem (subset_closure (by simp)) _) (subset_closure (by simp))
  have hs : ∀ b ∈ ({r} : Set Atlas1600Group), s * b * s⁻¹ ∈ closure {r} := by
    rintro b (rfl : b = r)
    rw [s_conj_r]
    exact pow_mem (subset_closure (by simp)) _
  obtain ⟨a₂, h₂, k, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s,r} t 3 (by decide) t_cube ht ha
  obtain ⟨a₁, h₁, j, rfl⟩ := collect_power_mem {r} s 2 (by decide)
    (by rw [s_square]; exact pow_mem (subset_closure (by simp)) _) hs h₂
  obtain ⟨a₀, h₀, i, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert ∅ r 4 (by decide) r_fourth
      (by simp) (by simpa using h₁)
  simp only [closure_empty, mem_bot] at h₀
  subst a₀
  let n : Fin 24 := ⟨i.val + 4*j.val + 8*k.val, by omega⟩
  refine ⟨n, ?_⟩
  have hi : n.val % 4 = i.val := by dsimp [n]; omega
  have hj : n.val / 4 % 2 = j.val := by dsimp [n]; omega
  have hk : n.val / 8 = k.val := by dsimp [n]; omega
  simp only [cNF, hi, hj, hk, one_mul]

private theorem kNF_injective : Function.Injective kNF := by
  have h : Function.Injective (fun n : Fin 25 => kPerm n 0) := by decide +kernel
  intro i j he
  apply h
  simpa only [kNF_val] using congrArg (fun a : Atlas1600Group => a.val 0) he

private theorem cNF_injective : Function.Injective cNF := by
  have h : Function.Injective (fun n : Fin 24 => cPerm n 2) := by decide +kernel
  intro i j he
  apply h
  simpa only [cNF_val] using congrArg (fun a : Atlas1600Group => a.val 2) he

public theorem kernel_card : Nat.card kernel = 25 := by
  let e : Fin 25 ≃ kernel := Equiv.ofBijective
    (fun n => ⟨kNF n, kNF_mem n⟩)
    ⟨fun _ _ h => kNF_injective (congrArg Subtype.val h), fun a => by
      obtain ⟨n, hn⟩ := kNF_surjective a.property
      exact ⟨n, Subtype.ext hn⟩⟩
  rw [← Nat.card_congr e]
  exact Nat.card_fin 25

public theorem complement_card : Nat.card complement = 24 := by
  let e : Fin 24 ≃ complement := Equiv.ofBijective
    (fun n => ⟨cNF n, cNF_mem n⟩)
    ⟨fun _ _ h => cNF_injective (congrArg Subtype.val h), fun a => by
      obtain ⟨n, hn⟩ := cNF_surjective a.property
      exact ⟨n, Subtype.ext hn⟩⟩
  rw [← Nat.card_congr e]
  exact Nat.card_fin 24

public instance kernel_commutative : IsMulCommutative kernel := by
  apply isMulCommutative_closure
  rintro x (rfl | rfl) y (rfl | rfl)
  · rfl
  · exact uv_comm.symm
  · exact uv_comm
  · rfl

public theorem complement_normalizes :
    complement ≤ normalizer (kernel : Set Atlas1600Group) := by
  have hu : u ∈ kernel := subset_closure (by simp)
  have hv : v ∈ kernel := subset_closure (by simp)
  apply (closure_le _).mpr
  rintro a (rfl | rfl | rfl)
  · apply normalizes_closure
    rintro b (rfl | rfl)
    · rw [t_conj_v]; exact mul_mem (pow_mem hu _) (pow_mem hv _)
    · rw [t_conj_u]; exact mul_mem hu hv
  · apply normalizes_closure
    rintro b (rfl | rfl)
    · rw [s_conj_v]; exact mul_mem (pow_mem hu _) (pow_mem hv _)
    · rw [s_conj_u]; exact pow_mem hu _
  · apply normalizes_closure
    rintro b (rfl | rfl)
    · rw [r_conj_v]; exact pow_mem hv _
    · rw [r_conj_u]; exact mul_mem (pow_mem hu _) (pow_mem hv _)

/-- Every nonidentity element of the complement fixes only the kernel identity. -/
public theorem complement_free (c : complement) (hc : c ≠ 1) (k : kernel)
    (h : (c : Atlas1600Group) * k * (c : Atlas1600Group)⁻¹ = k) : k = 1 := by
  obtain ⟨i, hi⟩ := cNF_surjective c.property
  obtain ⟨j, hj⟩ := kNF_surjective k.property
  have hcheck : ∀ i : Fin 24, ∀ j : Fin 25,
      (cPerm i * kPerm j * (cPerm i)⁻¹) 0 = kPerm j 0 → i = 0 ∨ j = 0 := by
    decide +kernel
  have he : (cPerm i * kPerm j * (cPerm i)⁻¹) 0 = kPerm j 0 := by
    rw [← hi, ← hj] at h
    have hh := congrArg (fun a : Atlas1600Group => a.val 0) h
    change ((cNF i).val * (kNF j).val * (cNF i).val⁻¹) 0 = (kNF j).val 0 at hh
    simpa only [cNF_val, kNF_val] using hh
  rcases hcheck i j he with hzero | hzero
  · exfalso
    apply hc
    apply Subtype.ext
    rw [← hi, hzero]
    simp [cNF]
  · apply Subtype.ext
    rw [← hj, hzero]
    simp [kNF]

end Tits.FiveFrobenius
