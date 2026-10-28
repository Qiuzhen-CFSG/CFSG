module
public import Theory.Representation.CoprimeElementaryComplement
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.PGroup

/-!
# Reducible coprime actions on the extraspecial group of order 27

If a group of order coprime to three acts reducibly on the Frattini quotient
of an extraspecial group of order 27 and exponent three, two invariant
subgroups of order three generate the whole extraspecial group.

Coprime complements first split the two-dimensional Frattini quotient into
lines, and then lift each line through its elementary preimage of order nine.
The Frattini nongenerating property gives generation after lifting.

Source: Aschbacher--Smith, 15.1.2, printed p.1086, the reducible Sylow case.
-/

open Subgroup
open scoped IsMulCommutative
namespace ExtraspecialSylow
variable {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
  [IsExtraspecial 3 P]

private theorem card_quotient (hP : Nat.card P = 27) :
    Nat.card (P ⧸ frattini P) = 9 := by
  have h := card_eq_card_quotient_mul_card_subgroup (frattini P)
  have hc : Nat.card (frattini P) = 3 := by
    rw [IsExtraspecial.frattini_eq_center (p := 3), IsExtraspecial.center_order_p 3 P]
  rw [hc, hP] at h
  omega

private theorem card_line {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 9) (L : Subgroup Q) (hL0 : L ≠ ⊥) (hL1 : L ≠ ⊤) :
    Nat.card L = 3 := by
  have hd : Nat.card L ∣ 3^2 := by simpa [hQ] using L.card_subgroup_dvd_card
  obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  interval_cases n
  · exact (hL0 (card_eq_one.mp hc)).elim
  · exact hc
  · exact (hL1 (eq_of_le_of_card_ge le_top (by rw [card_top, hQ, hc]; norm_num))).elim

private theorem card_preimage (L : Subgroup (P ⧸ frattini P)) :
    Nat.card (L.comap (QuotientGroup.mk' (frattini P))) = Nat.card L * 3 := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero L.index_ne_zero_of_finite)
  calc
    Nat.card (L.comap (QuotientGroup.mk' (frattini P))) * L.index = Nat.card P := by
      rw [← L.index_comap_of_surjective (QuotientGroup.mk'_surjective _)]
      exact (L.comap (QuotientGroup.mk' _)).card_mul_index
    _ = Nat.card (P ⧸ frattini P) * 3 := by
      have h := card_eq_card_quotient_mul_card_subgroup (frattini P)
      have hc : Nat.card (frattini P) = 3 := by
        rw [IsExtraspecial.frattini_eq_center (p := 3), IsExtraspecial.center_order_p 3 P]
      rwa [hc] at h
    _ = (Nat.card L * 3) * L.index := by rw [← L.card_mul_index]; ac_rfl

private theorem lift_line (α : A →* MulAut P) (hcop : Nat.Coprime 3 (Nat.card A))
    (hexp : Monoid.exponent P = 3)
    (L : Subgroup (P ⧸ frattini P)) (hL : Nat.card L = 3)
    (hstable : ∀ a : A, ∀ x ∈ L, quotientAut (frattini P) (α a) x ∈ L) :
    ∃ K : Subgroup P, Nat.card K = 3 ∧ K.map (QuotientGroup.mk' (frattini P)) = L ∧
      (∀ a : A, ∀ x ∈ K, α a x ∈ K) := by
  let q := QuotientGroup.mk' (frattini P)
  let E := L.comap q
  have hE : Nat.card E = 9 := by rw [card_preimage, hL]
  let : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using hE)
  let : IsElementaryAbelian 3 E := by
    refine { exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    have hp : Monoid.exponent P ∣ 3 := by rw [hexp]
    exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hp) (x : P)
  have hZ : frattini P ≤ E := by
    intro x hx
    change q x ∈ L
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact L.one_mem
  have hαE (a : A) (x : P) (hx : x ∈ E) : α a x ∈ E := by
    change q (α a x) ∈ L
    rw [← quotientAut_apply_mk]
    exact hstable a (q x) hx
  let β : A →* MulAut E := {
    toFun a := {
      toFun x := ⟨α a x, hαE a x x.property⟩
      invFun x := ⟨α a⁻¹ x, hαE a⁻¹ x x.property⟩
      left_inv x := by
        apply Subtype.ext
        change α a⁻¹ (α a (x : P)) = (x : P)
        rw [map_inv]
        exact (α a).symm_apply_apply x
      right_inv x := by
        apply Subtype.ext
        change α a (α a⁻¹ (x : P)) = (x : P)
        rw [map_inv]
        exact (α a).apply_symm_apply x
      map_mul' x y := by apply Subtype.ext; exact map_mul (α a) (x : P) (y : P) }
    map_one' := by ext x; exact congrArg (fun f : MulAut P => f x) α.map_one
    map_mul' a b := by ext x; exact congrArg (fun f : MulAut P => f x) (α.map_mul a b) }
  let Z := (frattini P).subgroupOf E
  have hZstable : ∀ a : A, ∀ x ∈ Z, β a x ∈ Z := by
    intro a x hx
    change α a (x : P) ∈ frattini P
    have he := (frattini P).characteristic_iff_map_eq.mp inferInstance (α a)
    exact he ▸ mem_map_of_mem (α a).toMonoidHom hx
  obtain ⟨K, hK, hKs⟩ := IsElementaryAbelian.exists_invariant_complement β hcop Z hZstable
  let R := K.map E.subtype
  have hZcard : Nat.card Z = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv]
    rw [IsExtraspecial.frattini_eq_center (p := 3), IsExtraspecial.center_order_p 3 P]
  have hKcard : Nat.card K = 3 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z K (by rw [normalizer_eq_top]; exact le_top)
    rw [hK.inf_eq_bot, hK.sup_eq_top, card_bot, card_top, one_mul, hZcard, hE] at hh
    omega
  have hRcard : Nat.card R = 3 := (Nat.card_congr (equivMapOfInjective K E.subtype E.subtype_injective).toEquiv).symm.trans hKcard
  have hRmap : R.map q = L := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨y,hy,rfl⟩,rfl⟩
      exact y.property
    · have he : E.map q = L := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L
      rw [← he]
      have hs : (Z ⊔ K).map E.subtype = E := by rw [hK.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      rw [← hs, Subgroup.map_sup, Subgroup.map_sup]
      have hzbot : (Z.map E.subtype).map q = ⊥ := by
        apply (Subgroup.map_eq_bot_iff _).mpr
        rintro x ⟨y,hy,rfl⟩
        exact (QuotientGroup.eq_one_iff _).mpr hy
      rw [hzbot]
      simp [R]
  refine ⟨R,hRcard,hRmap,?_⟩
  rintro a x ⟨y,hy,rfl⟩
  exact mem_map_of_mem E.subtype (hKs a y hy)

public theorem exists_normalized_cubic_generators
    (α : A →* MulAut P) (hcop : Nat.Coprime 3 (Nat.card A))
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (L : Subgroup (P ⧸ frattini P)) (hL0 : L ≠ ⊥) (hL1 : L ≠ ⊤)
    (hstable : ∀ a : A, ∀ x ∈ L, quotientAut (frattini P) (α a) x ∈ L) :
    ∃ K R : Subgroup P, Nat.card K = 3 ∧ Nat.card R = 3 ∧
      K ≠ center P ∧ R ≠ center P ∧ K ⊔ R = ⊤ ∧
      (∀ a : A, ∀ x ∈ K, α a x ∈ K) ∧
      (∀ a : A, ∀ x ∈ R, α a x ∈ R) := by
  let : Fact (IsPGroup 3 P) := ⟨IsExtraspecial.isPGroup 3 P⟩
  let : IsElementaryAbelian 3 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini (p := 3)
  let β := (quotientAut (frattini P)).comp α
  obtain ⟨L', hc, hs⟩ := IsElementaryAbelian.exists_invariant_complement β hcop L hstable
  have hLc := card_line (card_quotient hP) L hL0 hL1
  have hL'c : Nat.card L' = 3 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes L L' (by rw [normalizer_eq_top]; exact le_top)
    rw [hc.inf_eq_bot, hc.sup_eq_top, card_bot, card_top, one_mul, hLc, card_quotient hP] at hh
    omega
  obtain ⟨K,hK,hKm,hKs⟩ := lift_line α hcop hexp L hLc hstable
  obtain ⟨R,hR,hRm,hRs⟩ := lift_line α hcop hexp L' hL'c hs
  have hKZ : K ≠ center P := by
    intro he
    have h : K.map (QuotientGroup.mk' (frattini P)) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [he, ← IsExtraspecial.frattini_eq_center (p := 3), QuotientGroup.ker_mk']
    exact hL0 (hKm.symm.trans h)
  have hRZ : R ≠ center P := by
    intro he
    have h : R.map (QuotientGroup.mk' (frattini P)) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [he, ← IsExtraspecial.frattini_eq_center (p := 3), QuotientGroup.ker_mk']
    have hb : L' = ⊥ := hRm.symm.trans h
    rw [hb, card_bot] at hL'c
    omega
  have htop : K ⊔ R = ⊤ := by
    apply frattini_nongenerating
    have hm : (K ⊔ R).map (QuotientGroup.mk' (frattini P)) = ⊤ := by
      rw [Subgroup.map_sup, hKm, hRm, hc.sup_eq_top]
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (frattini P))) hm
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using hh
  exact ⟨K,R,hK,hR,hKZ,hRZ,htop,hKs,hRs⟩
end ExtraspecialSylow
