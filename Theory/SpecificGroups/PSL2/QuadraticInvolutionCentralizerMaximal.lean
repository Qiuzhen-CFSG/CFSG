module

public import Theory.SpecificGroups.PGL2.InvolutionCentralizerBound
public import Theory.SpecificGroups.PSL2.PrimeQuadraticMaximal

/-!
# Maximal involution centralizers in quadratic odd PSL₂

Dickson's alternatives reduce a proper overgroup to a prime subfield group.
Its centralizer of the original involution has order at most 2(p+1),
whereas the quadratic-field centralizer has order at least p²−1.
The small exceptional subgroups are excluded by their exact orders.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216.
-/

public section
open Subgroup Equiv.Perm BenderSuzuki.MatrixGroups GorensteinWalter

namespace Theory.PSL2
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

/-- In odd square fields of characteristic greater than three, involution centralizers are maximal. -/
theorem quadratic_involution_centralizer_isCoatom
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (t : PSL2MatrixGroup F) (ht : GorensteinWalter.IsInvolution t) :
    IsCoatom (centralizer ({t} : Set (PSL2MatrixGroup F))) := by
  have hp5 : 5 ≤ p := by have := Nat.odd_iff.mp ho; omega
  have hp2 : 25 ≤ p ^ 2 := by nlinarith
  have hsub : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (by omega)
  let D := centralizer ({t} : Set (PSL2MatrixGroup F))
  change IsCoatom D
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have hDcard : Nat.card D = p ^ 2 - 1 ∨ Nat.card D = p ^ 2 + 1 := by
    simpa [D, hF] using involution_centralizer_card_cases hodd t ht
  have hlow : p ^ 2 - 1 ≤ Nat.card D := by omega
  have hupp : Nat.card D ≤ p ^ 2 + 1 := by omega
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right_iff_dvd.mpr
    obtain ⟨k, hk⟩ := ho.pow (n := 2)
    exact ⟨k, by omega⟩
  have hcop : (Nat.card D).Coprime p := by
    rcases hDcard with hd | hd
    · rw [hd]
      have hh : (p ^ 2 - 1).Coprime (p ^ 2) :=
        ((Nat.coprime_self_sub_right (by nlinarith : 1 ≤ p ^ 2)).mpr
          (Nat.coprime_one_right _)).symm
      exact hh.of_dvd_right (dvd_pow_self p (by decide : 2 ≠ 0))
    · rw [hd]
      exact (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left (p ^ 2))).of_dvd_right
        (dvd_pow_self p (by decide : 2 ≠ 0))
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho.pow)
  rw [hF] at hcard
  change Nat.card (PSL2MatrixGroup F) * 2 = p ^ 2 * ((p ^ 2) ^ 2 - 1) at hcard
  have hDne : D ≠ ⊤ := by
    intro he
    have hc : Nat.card (PSL2MatrixGroup F) ≤ p ^ 2 + 1 := by simpa [he] using hupp
    have hsq : 5 ≤ (p ^ 2) ^ 2 := by nlinarith
    have hs : 4 ≤ (p ^ 2) ^ 2 - 1 := by omega
    have hb := Nat.mul_le_mul_left (p ^ 2) hs
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
  have hFp : Nat.card F = p ^ 2 := hF
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
    have hu : Nat.card H ≤ p ^ 2 + 1 := by
      rcases hn with hn | hn
      all_goals
        have hh := Nat.le_of_dvd (by omega) hn
        omega
    have hh := Nat.eq_of_dvd_of_lt_two_mul (Nat.card_pos (α := H)).ne' hdvd
      (by omega : Nat.card H < 2 * Nat.card D)
    omega
  · obtain ⟨e⟩ := hA4.2
    have hh := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hh
    norm_num at hh
    nlinarith
  · obtain ⟨e⟩ := hS4.2
    have hh := Nat.card_congr e.toEquiv
    rw [Nat.card_perm, Nat.card_fin] at hh
    norm_num at hh
    nlinarith
  · obtain ⟨e⟩ := hA5.2
    have hh := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hh
    norm_num at hh
    have hsmall : p ≤ 7 := by nlinarith
    interval_cases p <;> rcases hDcard with hd | hd <;> norm_num [hd, hh] at hdvd
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
    have hg : Nat.gcd (p ^ 2 - 1) 2 = 2 := by simpa [hF] using hgcd
    rw [hg] at hcdiv
    have hu := Nat.le_of_dvd (by omega : 0 < (p ^ 2 - 1) / 2) hcdiv
    omega
  · obtain ⟨m, hm, hd, ⟨e⟩⟩ := hPSL
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hm1 | hm2
    · subst m
      have hsubodd : IsOddPrimePower (Nat.card (GaloisField p 1)) :=
        ⟨p, 1, Fact.out, ho, by decide, GaloisField.card p 1 (by decide)⟩
      have htmodel : IsInvolution (e tH) :=
        ⟨fun h => (by have hh := e.orderOf_eq tH; rw [h, orderOf_one, htH] at hh; omega),
         (orderOf_dvd_iff_pow_eq_one).mp (by rw [e.orderOf_eq, htH])⟩
      have hb := centralizer_card_le_model t H hDH.le e
      have hc := involution_centralizer_card_cases hsubodd (e tH) htmodel
      rw [GaloisField.card p 1 (by decide), pow_one] at hc
      change Nat.card D ≤ Nat.card (centralizer ({e tH} : Set (PSL2MatrixGroup (GaloisField p 1)))) at hb
      rcases hc with hc | hc <;> rw [hc] at hb
      · have hbound : Nat.card D ≤ p + 1 := by omega
        nlinarith
      · nlinarith
    · subst m
      have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
        (F := GaloisField p 2) (by simpa [GaloisField.card p 2 (by decide)] using ho.pow (n := 2))
      rw [GaloisField.card p 2 (by decide), ← Nat.card_congr e.toEquiv] at hc
      apply H.eq_top_of_card_eq
      exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) (hc.trans hcard.symm)
  · obtain ⟨m, hm, hd, ⟨e⟩⟩ := hPGL
    have hh := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hm1 : m = 1 := by omega
    subst m
    have hsubodd : IsOddPrimePower (Nat.card (GaloisField p 1)) :=
      ⟨p, 1, Fact.out, ho, by decide, GaloisField.card p 1 (by decide)⟩
    let : Finite (PGL2 (GaloisField p 1)) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
    have htmodel : IsInvolution (e tH) :=
      ⟨fun h => (by have hh := e.orderOf_eq tH; rw [h, orderOf_one, htH] at hh; omega),
       (orderOf_dvd_iff_pow_eq_one).mp (by rw [e.orderOf_eq, htH])⟩
    have hb := (centralizer_card_le_model t H hDH.le e).trans
      (Theory.PGL2.involution_centralizer_card_le hsubodd
        (by simpa [GaloisField.card p 1 (by decide)] using hp) (e tH) htmodel)
    rw [GaloisField.card p 1 (by decide), pow_one] at hb
    change Nat.card D ≤ 2 * (p + 1) at hb
    nlinarith
end Theory.PSL2
