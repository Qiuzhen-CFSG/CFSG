module

public import Theory.GroupTheory.PGroup.AbelianCriticalSixteenFixedAction
public import Theory.GroupAction.C4SquareCubicCongruence

/-!
# The invariant order-sixty-four core of an abelian critical sixteen

Conjugation on a critical C₄-square has kernel exactly the critical subgroup.
The displacement map of the free cubic action on that subgroup is bijective,
so a fixed conjugation action lifts to an actual fixed ambient element. The
fixed-action bound therefore bounds the fixed part of the conjugation image
by two.

If the entire image were fixed, the fixed-element inversion theorem would put
all ambient squares in the central omega four. An outside fixed involution
would then generate a normal elementary eight together with that four. This
contradiction allows the cubic congruence theorem to produce its moved plane.
Its inverse image is the required invariant core of order sixty-four and
index at most two.

Source: MacWilliams, Trans. AMS 150 (1970), (xxi) and Lemma 3, printed
pp.380–382, DOI 10.1090/S0002-9947-1970-0276324-3;
`refs/original/n-group-global/odd-core-rank-two-source/macwilliams-1970-ams-wayback.pdf`.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace IsCriticalPSubgroup
variable {P : Type*} [Group P] [Finite P] {C : Subgroup P}

-- Surjectivity of displacement corrects a representative to a fixed element.
private theorem fixed_lift [C.Characteristic] [IsMulCommutative C]
    (a : MulAut P) (hfree : ∀ c ∈ C, a c = c → c = 1)
    (x : P) (hx : a x * x⁻¹ ∈ C) :
    ∃ c : C, a ((c : P)⁻¹ * x) = (c : P)⁻¹ * x := by
  let b : MulAut C := MulAut.characteristic C a
  let d : C →* C := {
    toFun := fun c => b c * c⁻¹
    map_one' := by simp
    map_mul' := by intro c z; simp [mul_comm, mul_left_comm, mul_assoc] }
  have hi : Function.Injective d := by
    apply d.ker_eq_bot_iff.mp
    apply bot_unique
    intro c hc
    apply Subtype.ext
    apply hfree c c.property
    have hh : b c * c⁻¹ = 1 := hc
    exact congrArg Subtype.val (mul_inv_eq_one.mp hh)
  obtain ⟨c, hc⟩ := Finite.surjective_of_injective hi (⟨a x * x⁻¹, hx⟩ : C)
  have hc' : a (c : P) * (c : P)⁻¹ = a x * x⁻¹ := congrArg Subtype.val hc
  refine ⟨c, ?_⟩
  have hac : a (c : P) = (a x * x⁻¹) * c := (mul_inv_eq_iff_eq_mul).mp hc'
  rw [map_mul, map_inv, hac, mul_inv_rev]
  group

omit [Finite P] in
private theorem action_equivariant [C.Characteristic] (a : MulAut P) (x : P) :
    MulAut.conjNormal (H := C) (a x) =
      MulAut.characteristic C a * MulAut.conjNormal x * (MulAut.characteristic C a)⁻¹ := by
  apply MulEquiv.ext
  intro c
  apply Subtype.ext
  change a x * (c : P) * (a x)⁻¹ = a (x * (a⁻¹ (c : P)) * x⁻¹)
  simp

private theorem fixed_image_lift
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (a : MulAut P) (hfree : ∀ c ∈ C, a c = c → c = 1) :
    letI : C.Characteristic := hC.characteristic
    ∀ f ∈ (MulAut.conjNormal (H := C)).range,
      Commute f (MulAut.characteristic C a) →
      ∃ x : a.fixedSubgroup, MulAut.conjNormal (H := C) (x : P) = f := by
  let : C.Characteristic := hC.characteristic
  rintro f ⟨x, rfl⟩ hf
  let φ : P →* MulAut C := MulAut.conjNormal
  have hk : φ.ker = C := conjNormal_ker_eq_of_selfCentralizing_abelian C
    hC.centralizer_eq_self_of_abelian.le
  have hx : a x * x⁻¹ ∈ C := by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv]
    rw [show φ (a x) = _ from action_equivariant a x]
    rw [← hf.eq]
    simp [φ]
  obtain ⟨c, hc⟩ := fixed_lift a hfree x hx
  refine ⟨⟨(c : P)⁻¹ * x, (MulAut.mem_fixedSubgroup a _).mpr hc⟩, ?_⟩
  change φ ((c : P)⁻¹ * x) = φ x
  have hφc : φ c = 1 := MonoidHom.mem_ker.mp (by rw [hk]; exact c.property)
  rw [map_mul, map_inv, hφc, inv_one, one_mul]


-- In the entirely fixed case every square is central of exponent two.
private theorem image_not_all_fixed
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hnonab : ¬ IsMulCommutative P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model)
    (a : MulAut P) (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) :
    letI : C.Characteristic := hC.characteristic
    ¬ ∀ f ∈ (MulAut.conjNormal (H := C)).range,
      Commute f (MulAut.characteristic C a) := by
  let : C.Characteristic := hC.characteristic
  intro hall
  let φ : P →* MulAut C := MulAut.conjNormal
  have hk : φ.ker = C := conjNormal_ker_eq_of_selfCentralizing_abelian C
    hC.centralizer_eq_self_of_abelian.le
  have hlift (x : P) : ∃ y : a.fixedSubgroup, φ y = φ x :=
    fixed_image_lift hC a hfree (φ x) ⟨x, rfl⟩ (hall (φ x) ⟨x, rfl⟩)
  let W := (omega₁ (center P) (p := 2)).map (center P).subtype
  have hW : W ≤ center P := map_subtype_le _
  let : W.Normal := ⟨fun w hw g => by
    rw [mem_center_iff.mp (hW hw) g, mul_inv_cancel_right]
    exact hw⟩
  let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 a.fixedSubgroup :=
    hC.fixedSubgroup_elementary_of_c4_square hno hZ e a hfree
  have hWC : W ≤ C := by
    dsimp [W]
    rw [← hC.omega_one_map_eq_center hno hZ]
    exact map_subtype_le _
  have hsC (c : P) (hc : c ∈ C) : c ^ 2 ∈ W := by
    apply hC.mem_omega_center_of_square_eq_one hno hZ (C.pow_mem hc 2)
    have hh : (⟨c, hc⟩ : C) ^ 4 = 1 := e.injective (by
      rw [map_pow, map_one]
      exact (by decide : ∀ z : C4SquareExtension.Model, z ^ 4 = 1) _)
    have hh' : c ^ 4 = 1 := congrArg Subtype.val hh
    simpa only [← pow_mul] using hh'
  have hs (x : P) : x ^ 2 ∈ W := by
    obtain ⟨y, hy⟩ := hlift x
    have hc : x * (y : P)⁻¹ ∈ C := by
      rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
    by_cases hy1 : (y : P) = 1
    · apply hsC x
      simpa [hy1] using hc
    · have hyfix := (MulAut.mem_fixedSubgroup a y).mp y.property
      have hinv := hC.fixed_element_inverts_c4_square hno hZ e a ha hfree y hyfix hy1
        (x * (y : P)⁻¹) hc
      have hy2 : (y : P) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (y : P) y.property
      have hx2 : x ^ 2 = 1 := by
        calc
          x ^ 2 = (x * (y : P)⁻¹) * ((y : P) * (x * (y : P)⁻¹) * (y : P)⁻¹) * (y : P) ^ 2 := by simp only [pow_two]; group
          _ = 1 := by rw [hinv, mul_inv_cancel, hy2, one_mul]
      rw [hx2]
      exact W.one_mem
  have hQs (x : P ⧸ W) : x ^ 2 = 1 := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective W x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hs y)
  have hQcomm (x y : P ⧸ W) : x * y = y * x := by
    have hi (z : P ⧸ W) : z⁻¹ = z :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hQs z)
    calc
      x * y = (x * y)⁻¹ := (hi _).symm
      _ = y * x := by rw [mul_inv_rev, hi, hi]
  have hcomm (x y : P) : ⁅x, y⁆ ∈ W := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' W) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hQcomm _ _
  have hout : ∃ x : P, x ∉ C := by
    by_contra! hh
    apply hnonab
    exact IsMulCommutative.of_comm (fun x y =>
      congrArg Subtype.val (mul_comm (⟨x, hh x⟩ : C) ⟨y, hh y⟩))
  obtain ⟨x, hx⟩ := hout
  obtain ⟨t, ht⟩ := hlift x
  have htC : (t : P) ∉ C := by
    intro hc
    apply hx
    rw [← hk, MonoidHom.mem_ker, ← ht]
    exact MonoidHom.mem_ker.mp (by rwa [hk])
  have ht2 : (t : P) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (t : P) t.property
  let E := W ⊔ zpowers (t : P)
  let : IsElementaryAbelian 2 (zpowers (t : P)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  have htW : (t : P) ∈ centralizer (W : Set P) := by
    intro w hw
    exact (mem_center_iff.mp (hW hw) t).symm
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr htW)
  let : E.Normal := Subgroup.commutator_top_left_le_iff.mp
    (Subgroup.commutator_le.mpr (fun g _ y _ =>
      (le_sup_left : W ≤ E) (hcomm g y)))
  have hEW := normal_elementary_le_omega_center_of_no_normal_eight hno hZ E
  exact htC (hWC (hEW ((le_sup_right : zpowers (t : P) ≤ E) (mem_zpowers (t : P)))))


/-- The cubic moved plane lifts to an invariant core of order sixty-four. -/
public theorem exists_cubic_core_of_c4_square
    (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hnonab : ¬ IsMulCommutative P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (e : C ≃* C4SquareExtension.Model)
    (a : MulAut P) (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) :
    ∃ R : Subgroup P, C ≤ R ∧ Nat.card R = 64 ∧
      (R.index = 1 ∨ R.index = 2) ∧
      (∀ r ∈ R, a r ∈ R) ∧
      (∀ r ∈ R, a r * r⁻¹ ∈ C → r ∈ C) ∧
      (∀ r ∈ R, r ∉ C → ∀ c ∈ C, Commute c r → c ^ 2 = 1) := by
  classical
  let : C.Characteristic := hC.characteristic
  let φ : P →* MulAut C := MulAut.conjNormal
  let b : MulAut C := MulAut.characteristic C a
  let H := φ.range
  have hk : φ.ker = C := conjNormal_ker_eq_of_selfCentralizing_abelian C
    hC.centralizer_eq_self_of_abelian.le
  have heq (x : P) : φ (a x) = b * φ x * b⁻¹ := action_equivariant a x
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.characteristic C a) ^ 3 = 1
    rw [← map_pow, show a ^ 3 = 1 from ha ▸ pow_orderOf_eq_one a, map_one]
  have hbne : b ≠ 1 := by
    intro hb
    have hall (c : C) : c = 1 := by
      apply Subtype.ext
      apply hfree c c.property
      exact congrArg (fun f : MulAut C => (f c : P)) hb
    have h : (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4))) =
        (1 : C4SquareExtension.Model) := by
      simpa using congrArg e (hall (e.symm (Multiplicative.ofAdd 1, 1)))
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 4),
      (1 : Multiplicative (ZMod 4))) ≠ (1 : C4SquareExtension.Model)) h
  have hfix : ∀ f ∈ H, ∀ x : C, x ^ 2 = 1 → f x = x := by
    rintro f ⟨g, rfl⟩ x hx
    exact IsPGroup.conjNormal_fixed_of_square_eq_one_of_no_normal_eight
      hno hZ C hC.centralizer_eq_self_of_abelian.le g x hx
  have hnorm : ∀ f ∈ H, b * f * b⁻¹ ∈ H := by
    rintro f ⟨g, rfl⟩
    exact ⟨a g, heq g⟩
  have hcent : Nat.card (H ⊓ centralizer ({b} : Set (MulAut C)) : Subgroup (MulAut C)) ≤ 2 := by
    have hl (f : ↥(H ⊓ centralizer ({b} : Set (MulAut C)))) :
        ∃ x : a.fixedSubgroup, φ x = f :=
      fixed_image_lift hC a hfree f f.property.1
        (Subgroup.mem_centralizer_singleton_iff.mp f.property.2)
    choose k hk' using hl
    have hi : Function.Injective k := by
      intro f g hfg
      apply Subtype.ext
      exact (hk' f).symm.trans ((congrArg (fun x : a.fixedSubgroup => φ x) hfg).trans (hk' g))
    exact (Nat.card_le_card_of_injective k hi).trans
      (hC.fixedSubgroup_card_le_two_of_c4_square hno hZ e a ha hfree)
  obtain ⟨V, hVH, hVcard, hVi, hVa, hVfree, hVfix⟩ :=
    C4SquareExtension.exists_c4_square_cubic_plane e b H hb3 hbne hfix hnorm hcent
      (image_not_all_fixed hC hnonab hno hZ e a ha hfree)
  let R := V.comap φ
  have hCR : C ≤ R := by
    intro c hc
    change φ c ∈ V
    have hh : φ c = 1 := MonoidHom.mem_ker.mp (by rwa [hk])
    rw [hh]
    exact V.one_mem
  have hRmap : R.map φ = V := by
    change (V.comap φ).map φ = V
    rw [map_comap_eq, inf_eq_right.mpr hVH]
  have hrel : C.relIndex R = 4 := by
    rw [← hk, relIndex_ker, hRmap, hVcard]
  have hCcard : Nat.card C = 16 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [C4SquareExtension.Model, Nat.card_prod, Nat.card_eq_fintype_card]
  have hRcard : Nat.card R = 64 := by
    have hh := (C.subgroupOf R).card_mul_index
    have hc : Nat.card (C.subgroupOf R) = Nat.card C :=
      Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv
    rw [hc, hCcard, show (C.subgroupOf R).index = C.relIndex R from rfl, hrel] at hh
    exact hh.symm
  refine ⟨R, hCR, hRcard, ?_, ?_, ?_, ?_⟩
  · change (V.comap φ).index = 1 ∨ (V.comap φ).index = 2
    rwa [index_comap]
  · intro r hr
    change φ (a r) ∈ V
    rw [heq]
    exact hVa (φ r) hr
  · intro r hr hd
    rw [← hk, MonoidHom.mem_ker] at hd ⊢
    rw [map_mul, map_inv, mul_inv_eq_one] at hd
    apply hVfree (φ r) hr
    exact (heq r).symm.trans hd
  · intro r hr hn c hc hcomm
    have hn' : φ r ≠ 1 := by
      intro hh
      apply hn
      rw [← hk, MonoidHom.mem_ker]
      exact hh
    have hfixc : φ r (⟨c, hc⟩ : C) = ⟨c, hc⟩ := by
      apply Subtype.ext
      change r * c * r⁻¹ = c
      rw [← hcomm.eq, mul_inv_cancel_right]
    exact congrArg Subtype.val (hVfix (φ r) hr hn' ⟨c, hc⟩ hfixc)
end IsCriticalPSubgroup
