module

public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.SpecificGroups.PSL2.PrimeQuadraticMaximal
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence

/-!
# Maximal involution centralizers in prime-field PSL₂

For odd prime p > 9, Dickson's classification proves that every involution
centralizer in PSL₂(p) is maximal. The actual centralizer has order p−1 or
p+1. The cyclic, dihedral and affine alternatives cannot properly contain it;
prime fields have no proper subfield alternatives. In A₄, S₄ and A₅ the
centralizer of the marked involution has order at most eight, which excludes
those alternatives while retaining the actual marked involution.

Source application: Aschbacher–Smith E.2.2(2c), printed pp.215–216.
-/

public section
open Subgroup Equiv.Perm BenderSuzuki.MatrixGroups
namespace Theory.PSL2

private theorem perm_involution_centralizer_le_eight {n : ℕ} (hn : n ≤ 4) (x : Equiv.Perm (Fin n)) (hx : orderOf x = 2) :
    Nat.card (centralizer ({x} : Set (Equiv.Perm (Fin n)))) ≤ 8 := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (hx ▸ Nat.prime_two)
  rw [hx] at hk
  have hb := x.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hkbound : k ≤ 1 := by omega
  rw [nat_card_centralizer, hk]
  interval_cases k
  · have hsub : n - 2 ≤ 2 := by omega
    interval_cases h : n - 2 <;> norm_num [h]
  · have hn4 : n = 4 := by omega
    norm_num [hn4]

private theorem alternating_involution_centralizer_le_eight {n : ℕ} (hn : n ≤ 5) (x : alternatingGroup (Fin n)) (hx : orderOf x = 2) :
    Nat.card (centralizer ({x} : Set (alternatingGroup (Fin n)))) ≤ 8 := by
  have hct := alternatingGroup.involution_cycleType_of_degree_le_six (by omega) x hx
  let f : centralizer ({x} : Set (alternatingGroup (Fin n))) →*
      centralizer ({(x : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))) := {
    toFun := fun y => ⟨y.val.val, by
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun y : centralizer ({(x : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))) => (y : Equiv.Perm (Fin n))) hab))
  apply (Nat.card_le_card_of_injective f hf).trans
  rw [nat_card_centralizer, hct]
  have hnsub : n - 4 ≤ 1 := by omega
  interval_cases h : n - 4 <;> norm_num [h]

private theorem centralizer_card_le_model {G A : Type*} [Group G] [Group A]
    [Finite G] [Finite A] (t : G) (U : Subgroup G)
    (hCU : centralizer ({t} : Set G) ≤ U) (e : U ≃* A) :
    Nat.card (centralizer ({t} : Set G)) ≤
      Nat.card (centralizer ({e ⟨t, hCU (mem_centralizer_singleton_iff.mpr rfl)⟩} : Set A)) := by
  let tU : U := ⟨t, hCU (mem_centralizer_singleton_iff.mpr rfl)⟩
  let f : centralizer ({t} : Set G) →*
      centralizer ({e tU} : Set A) := {
    toFun := fun y => ⟨e ⟨y.val, hCU y.property⟩, by
      apply mem_centralizer_singleton_iff.mpr
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp y.property⟩
    map_one' := Subtype.ext e.map_one
    map_mul' := fun a b => Subtype.ext (e.map_mul
      (⟨a, hCU a.property⟩ : U) (⟨b, hCU b.property⟩ : U)) }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hh := e.injective (congrArg (fun y : centralizer ({e tU} : Set A) => (y : A)) hab)
    exact congrArg (fun x : U => (x : G)) hh
  exact Nat.card_le_card_of_injective f hf

/-- Every involution centralizer is maximal in odd prime PSL₂(p), p > 9. -/
theorem prime_involution_centralizer_isCoatom_of_nine_lt
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (t : PSL2MatrixGroup F) (ht : GorensteinWalter.IsInvolution t) :
    IsCoatom (centralizer ({t} : Set (PSL2MatrixGroup F))) := by
  let D := centralizer ({t} : Set (PSL2MatrixGroup F))
  change IsCoatom D
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩
  have hDcard : Nat.card D = p - 1 ∨ Nat.card D = p + 1 := by
    simpa [D, hF] using involution_centralizer_card_cases hodd t ht
  have hlow : p - 1 ≤ Nat.card D := by omega
  have hupp : Nat.card D ≤ p + 1 := by omega
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right_iff_dvd.mpr
    obtain ⟨k, hk⟩ := ho
    exact ⟨k, by omega⟩
  have hcop : (Nat.card D).Coprime p := by
    rcases hDcard with hd | hd
    · rw [hd]
      exact ((Nat.coprime_self_sub_right (by omega : 1 ≤ p)).mpr
        (Nat.coprime_one_right p)).symm
    · rw [hd]
      exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left p)
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho)
  rw [hF] at hcard
  change Nat.card (PSL2MatrixGroup F) * 2 = p * (p ^ 2 - 1) at hcard
  have hDne : D ≠ ⊤ := by
    intro he
    have hc : Nat.card (PSL2MatrixGroup F) ≤ p + 1 := by simpa [he] using hupp
    have hsq : 5 ≤ p ^ 2 := by nlinarith
    have hs : 4 ≤ p ^ 2 - 1 := by omega
    have hb := Nat.mul_le_mul_left p hs
    omega
  refine ⟨hDne, ?_⟩
  intro H hDH
  have hlt : Nat.card D < Nat.card H := by
    by_contra! hge
    exact hDH.ne (eq_of_le_of_card_ge hDH.le hge)
  have hdvd : Nat.card D ∣ Nat.card H := card_dvd_of_le hDH.le
  let tH : H := ⟨t, hDH.le (mem_centralizer_singleton_iff.mpr rfl)⟩
  have htH : orderOf tH = 2 := by
    rw [← orderOf_injective H.subtype H.subtype_injective tH]
    exact orderOf_eq_prime ht.2 ht.1
  have hFp : Nat.card F = p ^ 1 := by simpa using hF
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFp H with
    hElem | hCyc | hDih | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · let := hElem
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hm] at hdvd
    have hh := (hcop.pow_right m).eq_one_of_dvd hdvd
    omega
  · obtain ⟨n, hn, hc, _⟩ := hCyc
    rw [hgcd, hF] at hn
    rcases hn with hn | hn
    all_goals
      have hh := Nat.le_of_dvd (by omega) hn
      omega
  · obtain ⟨n, hn, hc, _⟩ := hDih
    rw [hgcd, hF] at hn
    have hu : Nat.card H ≤ p + 1 := by
      rcases hn with hn | hn
      all_goals
        have hh := Nat.le_of_dvd (by omega) hn
        omega
    have hh := Nat.eq_of_dvd_of_lt_two_mul (Nat.card_pos (α := H)).ne' hdvd
      (by omega : Nat.card H < 2 * Nat.card D)
    omega
  · obtain ⟨e⟩ := hA4.2
    have hh := (centralizer_card_le_model t H hDH.le e).trans
      (alternating_involution_centralizer_le_eight (by decide : 4 ≤ 5) (e tH)
        ((e.orderOf_eq tH).trans htH))
    change Nat.card D ≤ 8 at hh
    omega
  · obtain ⟨e⟩ := hS4.2
    have hh := (centralizer_card_le_model t H hDH.le e).trans
      (perm_involution_centralizer_le_eight (by decide : 4 ≤ 4) (e tH)
        ((e.orderOf_eq tH).trans htH))
    change Nat.card D ≤ 8 at hh
    omega
  · obtain ⟨e⟩ := hA5.2
    have hh := (centralizer_card_le_model t H hDH.le e).trans
      (alternating_involution_centralizer_le_eight (by decide : 5 ≤ 5) (e tH)
        ((e.orderOf_eq tH).trans htH))
    change Nat.card D ≤ 8 at hh
    omega
  · obtain ⟨m, c, _, hcdiv, N, C, hn, _, hcN, _, hcC, hd, hsup⟩ := hAff
    let := hn
    have hc : Nat.card H = p ^ m * c := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top]; exact le_top) hd
      simpa [hsup, hcN, hcC] using hh
    rw [hc] at hdvd
    have hh := (hcop.pow_right m).dvd_of_dvd_mul_left hdvd
    have hcpos : 0 < c := hcC ▸ Nat.card_pos (α := C)
    have hl := Nat.le_of_dvd hcpos hh
    have hg : Nat.gcd (p ^ 1 - 1) 2 = 2 := by simpa [hF] using hgcd
    rw [hg, pow_one] at hcdiv
    have hu := Nat.le_of_dvd (by omega : 0 < (p - 1) / 2) hcdiv
    omega
  · obtain ⟨m, hm, hd, ⟨e⟩⟩ := hPSL
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hd
    subst m
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := GaloisField p 1) (by simpa [GaloisField.card p 1 (by decide)] using ho)
    rw [GaloisField.card p 1 (by decide), pow_one, ← Nat.card_congr e.toEquiv] at hc
    apply H.eq_top_of_card_eq
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) (hc.trans hcard.symm)
  · obtain ⟨m, hm, hd, _⟩ := hPGL
    have hh := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega

private theorem odd_mod_eight_of_sixteen_dvd_order_product {q : ℕ}
    (ho : Odd q) (hpos : 1 < q) (hd : 16 ∣ q * (q ^ 2 - 1)) :
    q % 8 = 1 ∨ q % 8 = 7 := by
  have hsq : 1 ≤ q ^ 2 := by nlinarith
  have hdiff : q ^ 2 = (q ^ 2 - 1) + 1 := (Nat.sub_add_cancel hsq).symm
  have hmod := congrArg (fun n : ℕ => n % 16) hdiff
  rw [Nat.pow_mod, Nat.add_mod] at hmod
  have hzero := Nat.mod_eq_zero_of_dvd hd
  rw [Nat.mul_mod] at hzero
  have hodd : q % 2 = 1 := Nat.odd_iff.mp ho
  have hbound : q % 16 < 16 := Nat.mod_lt _ (by decide)
  interval_cases h : q % 16 <;> norm_num [h] at hmod hzero <;> omega

/-- Divisibility by eight gives precisely the large-Sylow odd residues. -/
theorem mod_eight_of_eight_dvd_psl_card {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) (hd : 8 ∣ Nat.card (PSL2MatrixGroup F)) :
    Nat.card F % 8 = 1 ∨ Nat.card F % 8 = 7 := by
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) ho
  apply odd_mod_eight_of_sixteen_dvd_order_product ho Finite.one_lt_card
  rw [← hc]
  exact Nat.mul_dvd_mul hd (dvd_refl 2)


end Theory.PSL2
