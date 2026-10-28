module

public import CFSG.Quasithin.ChapterG.Section08.Defs
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Mathlib.GroupTheory.Sylow

/-!
# The rank-one step of Thompson's dihedral lemma

A nontrivial involutory action on an odd-order subgroup inverts a nonidentity
displacement. Extract a prime-order element from its cyclic subgroup; the
inverting involution and this rotation generate an actual dihedral subgroup.
The prime divides the order of the original odd subgroup.

Source: Aschbacher–Smith G.8.6, printed p.350.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section08
variable {G : Type*} [Group G] [Finite G]

/-- A noncentral involution acting on an odd-order subgroup inverts an
actual element of odd prime order in that subgroup. -/
theorem exists_inverted_prime (X : Subgroup G) (hodd : Odd (Nat.card X))
    (a : G) (ha2 : a ^ 2 = 1) (hn : a ∈ normalizer (X : Set G))
    (hc : a ∉ centralizer (X : Set G)) :
    ∃ y : G, y ∈ X ∧ (orderOf y).Prime ∧ Odd (orderOf y) ∧
      a * y * a⁻¹ = y⁻¹ := by
  have hnot : ∃ z ∈ X, a * z * a⁻¹ ≠ z := by
    by_contra! h
    apply hc
    intro z hz
    exact (mul_inv_eq_iff_eq_mul.mp (h z hz)).symm
  obtain ⟨z, hz, hzne⟩ := hnot
  let x := (a * z * a⁻¹) * z⁻¹
  have hxX : x ∈ X := X.mul_mem ((hn z).mp hz) (X.inv_mem hz)
  have hxne : x ≠ 1 := by
    intro h
    exact hzne (mul_inv_eq_one.mp h)
  have haInv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ha2)
  have hxInv : a * x * a⁻¹ = x⁻¹ := by
    dsimp [x]
    rw [haInv]
    have haa : a * a = 1 := by simpa [pow_two] using ha2
    calc
      a * (a * z * a * z⁻¹) * a = (a * a) * z * a * z⁻¹ * a := by group
      _ = z * a * z⁻¹ * a := by rw [haa]; simp
      _ = (a * z * a * z⁻¹)⁻¹ := by simp [haInv, mul_assoc]
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (show orderOf x ≠ 1 from fun h => hxne (orderOf_eq_one_iff.mp h))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := zpowers x) p
    (by simpa only [Nat.card_zpowers] using hpdvd)
  have hyorder : orderOf (y : G) = p := by simpa using hy
  have hyX : (y : G) ∈ X := (zpowers_le.mpr hxX) y.property
  refine ⟨y, hyX, hyorder ▸ hp, ?_, ?_⟩
  · exact hodd.of_dvd_nat (by simpa using orderOf_dvd_natCard (⟨(y : G), hyX⟩ : X))
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp y.property
    rw [← hk]
    calc
      a * x ^ k * a⁻¹ = (a * x * a⁻¹) ^ k := by simp
      _ = (x⁻¹) ^ k := by rw [hxInv]
      _ = (x ^ k)⁻¹ := by simp

/-- The rank-one extraction, retaining the prime divisor of the odd subgroup. -/
theorem exists_dihedral_involution (X : Subgroup G) (hodd : Odd (Nat.card X))
    (a : G) (ha2 : a ^ 2 = 1) (hn : a ∈ normalizer (X : Set G))
    (hc : a ∉ centralizer (X : Set G)) :
    ∃ D : DihedralProduct G 1,
      zpowers a ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ zpowers a ∧
      ∀ i, D.prime i ∣ Nat.card X := by
  obtain ⟨y, hyX, hyp, hyo, hay⟩ := exists_inverted_prime X hodd a ha2 hn hc
  let R := zpowers y
  have hcR : Nat.card R = orderOf y := Nat.card_zpowers y
  have hpR : (Nat.card R).Prime := hcR.symm ▸ hyp
  have hoR : Odd (Nat.card R) := hcR.symm ▸ hyo
  have ha1 : a ≠ 1 := fun h => hc (h ▸ (centralizer (X : Set G)).one_mem)
  have hanot : a ∉ R := by
    intro haR
    have hd := orderOf_dvd_natCard (⟨a, haR⟩ : R)
    have haord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
    apply hoR.not_two_dvd_nat
    simpa only [Subgroup.orderOf_mk, haord] using hd
  obtain ⟨e⟩ := R.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted a
    inferInstance ha2 hanot (by
      intro r hr
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
      calc
        a * y ^ k * a⁻¹ = (a * y * a⁻¹) ^ k := by simp
        _ = (y⁻¹) ^ k := by rw [hay]
        _ = (y ^ k)⁻¹ := by simp)
  let f : (Fin 1 → DihedralGroup (Nat.card R)) →* G :=
    (R ⊔ zpowers a).subtype.comp
      (e.symm.toMonoidHom.comp (Pi.evalMonoidHom _ 0))
  have hf : Function.Injective f := by
    intro b c h
    have hbc : b 0 = c 0 := e.symm.injective (Subtype.ext h)
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hbc
  have hr : f.range = R ⊔ zpowers a := by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      exact (e.symm (b 0)).property
    · intro x hx
      refine ⟨fun _ => e ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  refine ⟨⟨fun _ => Nat.card R, fun _ => hpR, fun _ => hoR, f, hf⟩,
    ?_, ?_, fun _ => card_dvd_of_le (zpowers_le.mpr hyX)⟩
  · change zpowers a ≤ f.range
    rw [hr]
    exact le_sup_right
  · change f.range ≤ _
    rw [hr]
    exact sup_le_sup_right (zpowers_le.mpr hyX) _
end CFSG.Quasithin.ChapterG.Section08
