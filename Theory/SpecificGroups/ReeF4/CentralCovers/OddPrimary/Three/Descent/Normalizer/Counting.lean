module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent

/-!
# Sylow-three assembly from a marked torus and its literal normalizers

The three-primary part of the full norm-one parameter pair is a two-generator
torus. A coordinate cycle has order three, normalizes that torus and meets it
trivially. The known carrier order makes their join Sylow. The coordinate
transposition exchanges its two generators; the given inverter inverts the
torus and centralizes the cycle, completing the original `ThreeSylowData`.

Only the displayed torus and normalizer equations remain as input here.
`Normalizer` discharges them with the actual descended Weyl words.
Source: GLS3 Example 2.6.3 and Table 4.7.3A; Aschbacher--Smith I.1.1--4.
-/

public section
open Subgroup
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic
noncomputable section
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

 theorem threeSylowData_of_torus_actions (m : ℕ)
    (horder : Nat.card (Model m) =
      (2 ^ (2 * m + 1)) ^ 12 * ((2 ^ (2 * m + 1)) ^ 6 + 1) *
        ((2 ^ (2 * m + 1)) ^ 4 - 1) * ((2 ^ (2 * m + 1)) ^ 3 + 1) *
          (2 ^ (2 * m + 1) - 1))
    (T : Parameters m →* Model m) (hT : Function.Injective T)
    (c s v : Model m) (hc : c^3 = 1)
    (hcT : ∀ a : Parameters m, c * T a * c⁻¹ = T ((a.1*a.2)⁻¹,a.1))
    (hsT : ∀ a : Parameters m, s * T a * s⁻¹ = T (a.2,a.1))
    (hvT : ∀ a : Parameters m, v * T a * v⁻¹ = (T a)⁻¹)
    (hvc : Commute v c) : Nonempty (ThreeSylowData m) := by
  classical
  let J := form m
  let C := OddThreeMatrix.primary J
  let inc : C →* BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne J :=
    Unitary.primaryInclusion J
  let d : C × C →* Model m := T.comp (inc.prodMap inc)
  let A := d.range
  have hd : Function.Injective d := by
    intro a b h
    have h' := hT h
    exact Prod.ext (Subtype.ext (congrArg (fun z => z.1.val) h'))
      (Subtype.ext (congrArg (fun z => z.2.val) h'))
  have hcd (a : C × C) : c * d a * c⁻¹ = d ((a.1*a.2)⁻¹,a.1) := by
    change c * T (inc a.1, inc a.2) * c⁻¹ = T (inc ((a.1*a.2)⁻¹),inc a.1)
    rw [map_inv, map_mul]
    exact hcT (inc a.1,inc a.2)
  have hcn : c ∉ A := by
    rintro ⟨a, ha⟩
    obtain ⟨u, hu⟩ := exists_normOne_ne_one m
    have hcomm : Commute c (T (u, 1)) := by
      rw [← ha]
      exact (Commute.all ((inc.prodMap inc) a) (u, 1)).map T
    have he := (hcT (u, 1)).symm.trans hcomm.mul_inv_cancel
    have hz := congrArg Prod.snd (hT he)
    exact hu hz
  have ho : orderOf c = 3 := orderOf_eq_prime hc (fun h => hcn (h ▸ one_mem A))
  have hnorm : c ∈ normalizer (A : Set (Model m)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      rw [hcd]
      exact ⟨_, rfl⟩
    · rintro ⟨a, ha⟩
      have he : c * d (a.2,(a.1*a.2)⁻¹) * c⁻¹ = d a := by
        rw [hcd]
        congr 1
        ext <;> simp [mul_comm]
      exact ⟨_, (mul_left_cancel (mul_right_cancel (ha.symm.trans he.symm))).symm⟩
  have hdis : Disjoint A (zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hy
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    have hn3 : n < 3 := Finset.mem_range.mp hn
    interval_cases n
    · simp
    · simp only [pow_one] at hx
      exact (hcn hx).elim
    · have h4 : (c^2)^2 = c := by
        rw [← pow_mul, show 2*2 = 3+1 from rfl, pow_add, hc, pow_one, one_mul]
      exact (hcn (h4 ▸ pow_mem hx 2)).elim
  let S := A ⊔ zpowers c
  have hA : Nat.card A = Nat.card C ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hd).toEquiv, Nat.card_prod, pow_two]
  have hcard : Nat.card S = Nat.card C ^ 2 * 3 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A (zpowers c)
      (zpowers_le.mpr hnorm) hdis, hA, Nat.card_zpowers, ho]
  have hC : Nat.card C = 3 ^ (2 ^ (2*m+1)+1).factorization 3 :=
    OddThreeMatrix.primary_card J (quadraticField_card m) (form_conj m)
  have hS : IsPGroup 3 S := by
    apply IsPGroup.of_card (n := 2*(2^(2*m+1)+1).factorization 3+1)
    rw [hcard, hC, ← pow_mul, pow_succ]
    congr 2
    omega
  obtain ⟨b, hCb, hb⟩ := OddThreeMatrix.primary_complement J
    (quadraticField_card m) (form_conj m)
  have hi : ¬ 3 ∣ S.index := index_prime_to_three_of_order (fieldSize_mod_three m)
    (Nat.card_pos (α := C)) hCb hb horder S hcard
  let P : Sylow 3 (Model m) := hS.toSylow hi
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  refine ⟨{
    sylow := P
    torus := A
    first := d (g,1)
    second := d (1,g)
    cycle := c
    swap := s
    inverter := v
    torus_generated := ?_
    generators_commute := (Commute.all (g,(1:C)) (1,g)).map d
    swap_first := ?_
    swap_second := ?_
    sylow_generated := rfl
    cycle_normalizes := hnorm
    inverts_torus := ?_
    fixes_cycle := hvc }⟩
  · apply le_antisymm
    · apply (closure_le _).mpr
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨(g,1),rfl⟩
      · exact ⟨(1,g),rfl⟩
    · rintro x ⟨⟨a,b⟩,rfl⟩
      obtain ⟨k,rfl⟩ := mem_zpowers_iff.mp (hg a)
      obtain ⟨l,rfl⟩ := mem_zpowers_iff.mp (hg b)
      have he : (g^k,g^l) = (g,(1:C))^k * (1,g)^l := by simp
      rw [he, map_mul, map_zpow, map_zpow]
      exact mul_mem (zpow_mem (subset_closure (by simp)) k)
        (zpow_mem (subset_closure (by simp)) l)
  · change s * T (inc g,inc 1) * s⁻¹ = T (inc 1,inc g)
    simpa only [map_one] using hsT (inc g,1)
  · change s * T (inc 1,inc g) * s⁻¹ = T (inc g,inc 1)
    simpa only [map_one] using hsT (1,inc g)
  · rintro t ⟨a,rfl⟩
    exact hvT ((inc.prodMap inc) a)

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent.Normalizer
