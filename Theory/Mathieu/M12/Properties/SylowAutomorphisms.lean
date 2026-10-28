module

public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Order
public import Theory.Mathieu.M12.Properties.Simplicity
public import Theory.GroupAction.SimpleCosets

/-!
# Automorphisms fixing the marked M₁₂ Sylow subgroup

An automorphism fixing the common Sylow subgroup pointwise fixes the first
parabolic's cubic actor: its discrepancy centralizes the quaternion core,
whose centralizer is the distinguished involution group. The checked
192-element enumeration of the second parabolic leaves exactly two images
for its cubic actor. These are related by conjugation by the central involution.

The Sylow subgroup and the two cubic actors generate the actual Witt-design
M₁₂. Explicit elements of orders five and eleven force a subgroup containing
them to have index at most nine; simplicity and the faithful coset action
exclude a proper subgroup of such index.

Thus the pointwise stabilizer in `MulAut M12` has order two, without requiring
a description of the outer automorphism extension. This is the intrinsic
local calculation used for the Aut(M₁₂) case of Aschbacher–Smith, F.1.12(13)
and Lemma 15.4.15, printed pp.263 and 1161. The marked permutations and the
normalizer enumeration are reused from `M12.SmallParabolicPair`, which retains
their source attribution. The finite checks here are kernel checked.
-/

public section

open Subgroup
namespace Sporadic.Mathieu.M12SmallPair.SylowAutomorphisms
open SylowEnumeration
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

private theorem rightI_mem : rightI ∈ sylowCandidate :=
  core_le_sylowCandidate ((mem_core _).mpr ⟨.a 0, .a 1, by decide +kernel⟩)
private theorem leftI_mem : leftI ∈ sylowCandidate :=
  core_le_sylowCandidate ((mem_core _).mpr ⟨.a 1, .a 0, by decide +kernel⟩)
private theorem z_mem : z ∈ sylowCandidate := core_le_sylowCandidate z_mem_core
private theorem v_mem : v ∈ sylowCandidate := core_le_sylowCandidate (natural_le_core v_mem_natural)

private theorem centralizer_core (x : M12)
    (hx : x ∈ centralizer (core : Set M12)) : x = 1 ∨ x = z := by
  have hxS : x ∈ sylowCandidate := by
    refine ⟨?_, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (hx z z_mem_core).symm
    · exact centralizer_le_normalizer (natural : Set M12)
        (fun y hy => hx y (natural_le_core hy))
  have hxE : x ∈ elementary := by
    rw [← sylowCandidate_centralizer_elementary]
    exact ⟨hxS, fun y hy => hx y (elementary_le_core hy)⟩
  exact (core_center_mem ⟨x, elementary_le_core hxE⟩).mp
    (mem_center_iff.mpr (fun y => Subtype.ext (hx y y.property)))

private theorem fixes_cubic (f : MulAut M12)
    (hf : ∀ x ∈ sylowCandidate, f x = x) : f cubicActor = cubicActor := by
  let a := cubicActor
  have hconj (q : M12) (hq : q ∈ core) :
      f a * q * (f a)⁻¹ = a * q * a⁻¹ := by
    have hnorm : firstParabolic ≤ normalizer (core : Set M12) :=
      (normal_subgroupOf_iff_le_normalizer core_le_firstParabolic).mp inferInstance
    have hn := (mem_set_normalizer_iff.mp (hnorm cubicActor_mem) q).mp hq
    have he := hf _ (core_le_sylowCandidate hn)
    simpa only [map_mul, map_inv, hf q (core_le_sylowCandidate hq)] using he
  have hc : a⁻¹ * f a ∈ centralizer (core : Set M12) := by
    intro q hq
    have he : (a⁻¹ * f a) * q * (a⁻¹ * f a)⁻¹ = q := by
      calc
        _ = a⁻¹ * (f a * q * (f a)⁻¹) * a := by group
        _ = a⁻¹ * (a * q * a⁻¹) * a := by rw [hconj q hq]
        _ = q := by group
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rcases centralizer_core _ hc with he | he
  · exact (inv_mul_eq_one.mp he).symm
  · have he' : f a = a * z := (inv_mul_eq_iff_eq_mul.mp he)
    have hp : (f a)^3 = 1 := by
      rw [← map_pow, show a ^ 3 = 1 by exact (by simpa [cubicActor_order] using pow_orderOf_eq_one cubicActor), map_one]
    rw [he'] at hp
    have hbad : (a * z)^3 ≠ 1 := by decide +kernel
    exact (hbad hp).elim

private theorem moving_conjugate_mem :
    movingActor * (rightI * leftI) * movingActor⁻¹ ∈ sylowCandidate := by
  constructor
  · exact (mem_firstParabolic_iff _).mpr (by decide +kernel)
  · exact (mem_secondParabolic_iff _).mpr (by decide +kernel)

private theorem moving_image_check : ∀ i : Fin 192,
    let y := wordElement i
    y ^ 3 = 1 → y * z * y⁻¹ = v →
    y * (rightI * leftI) * y⁻¹ = movingActor * (rightI * leftI) * movingActor⁻¹ →
    (y * rightI)^4 = 1 → (y * rightI)^2 ≠ 1 →
    y = movingActor ∨ y = z * movingActor * z⁻¹ := by
  decide +kernel

private theorem moving_image (f : MulAut M12)
    (hf : ∀ x ∈ sylowCandidate, f x = x) :
    f movingActor = movingActor ∨ f movingActor = z * movingActor * z⁻¹ := by
  have hfN (x : M12) (hx : x ∈ natural) : f x = x :=
    hf x (core_le_sylowCandidate (natural_le_core hx))
  have hy : f movingActor ∈ secondParabolic := by
    apply mem_normalizer_fintype
    intro x hx
    have hn : movingActor * x * movingActor⁻¹ ∈ natural :=
      (mem_set_normalizer_iff.mp movingActor_mem x).mp hx
    have he := hfN _ hn
    simp only [map_mul, map_inv, hfN x hx] at he
    rwa [he]
  have h := (mem_wordCarrier_iff (f movingActor).val).mpr
    ⟨(mem_M12_iff_preservesBlocks _).mp (f movingActor).property,
      (mem_secondParabolic_iff _).mp hy⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  have hie : wordElement i = f movingActor := Subtype.ext hi
  rw [← hie]
  apply moving_image_check i
  · rw [hie, ← map_pow, show movingActor ^ 3 = 1 by
        simpa [movingActor_order] using pow_orderOf_eq_one movingActor, map_one]
  · rw [hie, ← hf z z_mem, ← map_inv, ← map_mul, ← map_mul,
      movingActor_conjugates_z, hf v v_mem]
  · have he := hf _ moving_conjugate_mem
    simpa only [map_mul, map_inv, hf rightI rightI_mem, hf leftI leftI_mem, hie] using he
  · rw [hie, ← hf rightI rightI_mem, ← map_mul, ← map_pow,
        show (movingActor * rightI)^4 = 1 by decide +kernel, map_one]

  · rw [hie, ← hf rightI rightI_mem, ← map_mul, ← map_pow]
    intro he
    have hh := f.injective (he.trans (map_one f).symm)
    exact (by decide +kernel : (movingActor * rightI)^2 ≠ 1) hh

private theorem order_dvd {K : Subgroup M12} {x : M12} (hx : x ∈ K) :
    orderOf x ∣ Nat.card K := by
  have h := orderOf_dvd_natCard (⟨x,hx⟩ : K)
  simpa only [Subgroup.orderOf_mk] using h

/-- The known Sylow subgroup and the two marked cubic actors generate M₁₂. -/
theorem eq_top_of_contains_sylow_and_cubics (K : Subgroup M12) (hS : sylowCandidate ≤ K)
    (ha : cubicActor ∈ K) (hb : movingActor ∈ K) : K = ⊤ := by
  have h64 : 64 ∣ Nat.card K := by
    simpa only [card_sylowCandidate] using card_dvd_of_le hS
  have h3 : 3 ∣ Nat.card K := by simpa only [cubicActor_order] using order_dvd ha
  have h5 : 5 ∣ Nat.card K := by
    have hm := K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem ha hb) ha) hb) (hS rightI_mem)
    have ho : orderOf (cubicActor * movingActor * cubicActor * movingActor * rightI) = 5 := by
      have : Fact (Nat.Prime 5) := ⟨by decide⟩
      apply orderOf_eq_prime <;> decide +kernel
    simpa only [ho] using order_dvd hm
  have h11 : 11 ∣ Nat.card K := by
    have hm := K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hb ha) hb) ha) (hS leftI_mem)
    have ho : orderOf (movingActor * cubicActor * movingActor * cubicActor * leftI) = 11 := by
      have : Fact (Nat.Prime 11) := ⟨by decide⟩
      apply orderOf_eq_prime <;> decide +kernel
    simpa only [ho] using order_dvd hm
  have hd : 10560 ∣ Nat.card K := by
    exact (show Nat.Coprime 192 55 by decide).mul_dvd_of_dvd_of_dvd
      ((show Nat.Coprime 64 3 by decide).mul_dvd_of_dvd_of_dvd h64 h3)
      ((show Nat.Coprime 5 11 by decide).mul_dvd_of_dvd_of_dvd h5 h11)
  have hcard := K.card_mul_index
  rw [m12_order] at hcard
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := K)) hd
  have hi : K.index ≤ 9 := by nlinarith
  by_contra hne
  let := m12_isSimpleGroup
  have hdiv := K.card_dvd_factorial_index_of_simple hne
  have h11div : 11 ∣ (9 : ℕ).factorial :=
    dvd_trans (show 11 ∣ Nat.card M12 by rw [m12_order]; decide)
      (dvd_trans hdiv (Nat.factorial_dvd_factorial hi))
  exact (by decide : ¬ 11 ∣ (9 : ℕ).factorial) h11div

/-- The pointwise stabilizer of the marked Sylow subgroup in the actual
full automorphism group consists of the identity and conjugation by `z`. -/
theorem eq_one_or_conj_of_fixes_sylow (f : MulAut M12)
    (hf : ∀ x ∈ sylowCandidate, f x = x) : f = 1 ∨ f = MulAut.conj z := by
  have ha := fixes_cubic f hf
  rcases moving_image f hf with hb | hb
  · left
    have htop := eq_top_of_contains_sylow_and_cubics (f.toMonoidHom.eqLocus (MonoidHom.id _)) hf ha hb
    apply MulEquiv.ext
    intro x
    exact (show x ∈ f.toMonoidHom.eqLocus (MonoidHom.id _) from htop.symm ▸ mem_top x)
  · right
    have hc (x : M12) (hx : x ∈ sylowCandidate) : MulAut.conj z x = x := by
      have he := mem_centralizer_singleton_iff.mp hx.1
      change z * x * z⁻¹ = x
      rw [← he, mul_inv_cancel_right]
    have hac : MulAut.conj z cubicActor = cubicActor := by decide +kernel
    have htop := eq_top_of_contains_sylow_and_cubics (f.toMonoidHom.eqLocus (MulAut.conj z).toMonoidHom)
      (fun x hx => (hf x hx).trans (hc x hx).symm) (ha.trans hac.symm) hb
    apply MulEquiv.ext
    intro x
    exact (show x ∈ f.toMonoidHom.eqLocus (MulAut.conj z).toMonoidHom from htop.symm ▸ mem_top x)
end Sporadic.Mathieu.M12SmallPair.SylowAutomorphisms
