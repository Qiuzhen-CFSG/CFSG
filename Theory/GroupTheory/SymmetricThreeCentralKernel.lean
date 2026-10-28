module
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.GroupTheory.PResidual.CyclicImageCentralKernel
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# Central cubic kernels above symmetric-three factors

A three-perfect central extension of S₃ or S₃ × S₃ with a three-group
kernel has trivial kernel. In the single-factor case the Sylow
three-preimage is a central extension of a cyclic group, hence abelian.
In the pair case a coordinate transposition inverts one cubic axis and
fixes the other. Partial inversion forces their lifts to commute, again
making the Sylow preimage abelian. Central Sylow transfer kills the kernel.

This avoids an extraspecial-extension classification in the larger-kernel
branch of Aschbacher–Smith 13.4.8, printed p.905. The literal residual-section
application is in `CubicResidualSelection` and Chapter13's `LargerSelection`.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace SymmetricThreeCentralKernel
variable {E : Type*} [Group E] [Finite E]
local notation "S3" => Equiv.Perm (Fin 3)

private theorem ker_eq_bot_of_abelian_sylow {D : Type*} [Group D]
    (f : E →* D) (hc : f.ker ≤ center E) (hp : IsPGroup 3 f.ker)
    (hE : IsPPerfect 3 E) (P : Sylow 3 E) (hP : IsMulCommutative P) : f.ker = ⊥ := by
  let : IsMulCommutative P := hP
  let : CommGroup P := IsMulCommutative.instCommGroup
  apply eq_bot_iff.mpr
  intro x hx
  let y : P := ⟨x,hp.le_sylow_of_normal P hx⟩
  have hy := P.character_eq_one_of_central_mem_pResidual (MonoidHom.id P)
    P.isPGroup' y (hc hx) (by rw [(pResidual_eq_top_iff 3 E).mpr hE]; trivial)
  exact congrArg (fun a : P => (a : E)) hy

/-- A three-perfect central three-extension of S₃ is faithful. -/
theorem single (f : E →* S3) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hp : IsPGroup 3 f.ker)
    (hE : IsPPerfect 3 E) : f.ker = ⊥ := by
  let P : Sylow 3 E := Sylow.nonempty.some
  let Q := P.mapSurjective hf
  have hcard : Nat.card Q = 3 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
    change 3 ^ (6 : ℕ).factorization 3 = 3
    have h6 := congrArg (fun t : ℕ →₀ ℕ => t 3)
      (Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) (by decide : (3 : ℕ) ≠ 0))
    change (6 : ℕ).factorization 3 = (2 : ℕ).factorization 3 + (3 : ℕ).factorization 3 at h6
    rw [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ (3 : ℕ) ∣ 2),
      Nat.Prime.factorization_self Nat.prime_three, zero_add] at h6
    rw [h6, pow_one]
  let : IsCyclic Q := isCyclic_of_prime_card hcard
  let B := (Q : Subgroup S3).comap f
  let g : B →* Q := f.subgroupComap Q
  have hgc : g.ker ≤ center B := by
    intro x hx
    exact mem_center_iff.mpr fun y => Subtype.ext
      (mem_center_iff.mp (hc (congrArg Subtype.val hx)) y)
  let : IsMulCommutative B := g.isMulCommutative_of_isCyclic_of_ker_le_center hgc
  have hPB : (P : Subgroup E) ≤ B := fun x hx => mem_map_of_mem f hx
  exact ker_eq_bot_of_abelian_sylow f hc hp hE P
    (.of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hPB ha) (hPB hb))

private def c : S3 := Equiv.swap 0 1 * Equiv.swap 1 2
private def x : S3 × S3 := (c,1)
private def y : S3 × S3 := (1,c)
private def r : S3 × S3 := (Equiv.swap 0 1,1)

private theorem base_generated : closure ({x,y} : Set (S3 × S3)) =
    (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro z hz
    rcases hz with rfl | rfl
    · change c.sign = 1 ∧ (1 : S3).sign = 1
      decide
    · change (1 : S3).sign = 1 ∧ c.sign = 1
      decide
  · intro z hz
    have hw : ∀ z : S3 × S3, z.1.sign = 1 → z.2.sign = 1 →
        ∃ i j : Fin 3, z = x ^ i.val * y ^ j.val := by decide +kernel
    obtain ⟨i,j,hz⟩ := hw z hz.1 hz.2
    rw [hz]
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)

/-- Independent partial inversion kills a central three-kernel above S₃ × S₃. -/
theorem pair (f : E →* (S3 × S3)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hp : IsPGroup 3 f.ker)
    (hE : IsPPerfect 3 E) : f.ker = ⊥ := by
  obtain ⟨a,ha⟩ := hf x
  obtain ⟨b,hb⟩ := hf y
  have hab := CentralExtension.commute_lifts_of_partial_inversion f hf hc x y r
    (by decide : Nat.Coprime 3 2) (by decide : x ^ 3 = 1)
    (show x * y = y * x from by decide) (by decide : r * x * r⁻¹ = x⁻¹)
    (show r * y = y * r from by decide) a b ha hb
  let B := ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))).comap f
  let : IsMulCommutative B := CentralExtension.isMulCommutative_comap_of_pair_lifts
    f hc _ a b hab (by rw [ha,hb]; exact base_generated)
  let P : Sylow 3 E := Sylow.nonempty.some
  have hPB : (P : Subgroup E) ≤ B := by
    intro z hz
    change f z ∈ (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))
    rw [← SymmetricThreeProductResidual.residual_eq]
    apply mem_pResidual_of_orderOf_coprime
    have hh := (P.isPGroup'.map f).orderOf_coprime (by decide : Nat.Coprime 3 2)
      (⟨f z,mem_map_of_mem f hz⟩ : (P : Subgroup E).map f)
    rw [← orderOf_coe] at hh
    exact hh.symm
  exact ker_eq_bot_of_abelian_sylow f hc hp hE P
    (.of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hPB ha) (hPB hb))

end SymmetricThreeCentralKernel
