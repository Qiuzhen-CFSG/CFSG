module

public import Theory.GroupTheory.PGroup.NormalFourNormControl
public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourDiagonalMul
public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourDiagonalKernel
public import Theory.GroupTheory.PGroup.NormalFourFourthRootDetection
public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.GroupTheory.PGroup.HomocyclicElementaryFourTorsion
public import Theory.GroupTheory.SpecificGroups.AbelianCyclicTwoFixedAut
public import Theory.GroupTheory.SpecificGroups.AbelianCyclicTwoCentralKernelCount

/-!
# Elementary actions on unequal bases with a normal omega four

An elementary overgroup of the normal omega four fixes every involution of
the abelian base. For factors of order at least eight, restrict to eighth
roots, use the homocyclic four-torsion count, and apply fourth-root detection.
This does not require the normal four to be central in the ambient group.

For the factor of order two, the normal-four obstruction excludes central
automorphisms fixing fourth roots, and the corresponding automorphism count
proves the full bound. For the factor of order four, normal norm control excludes the kernel of the
two diagonal signs, embedding the elementary action image into a group of order
four. The structural argument only requires a normal omega four. Swapping the
factors then completes the bound for every pair of unequal nontrivial factors.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.1, printed p.385;
MacWilliams, Trans. AMS 150 (1970), §1.2.
-/

open Subgroup OmegaAction

/-- An elementary overgroup of the omega subgroup fixes all involutions of
the normal base, even when the full ambient group does not. -/
public theorem Subgroup.conjNormal_fixed_of_elementary_overgroup_omega
    {P : Type*} [Group P]
    (W D B : Subgroup P) [D.Normal] [IsElementaryAbelian 2 B]
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (b : B) (d : D) (hd : d ^ 2 = 1) : MulAut.conjNormal (b : P) d = d := by
  have hdW : (d : P) ∈ W := by
    rw [← hO]
    exact ⟨d, subset_closure (by simpa using hd), rfl⟩
  apply Subtype.ext
  change (b : P) * (d : P) * (b : P)⁻¹ = d
  rw [(B.le_centralizer b.property d (hWB hdW)).symm, mul_inv_cancel_right]

namespace IsPGroup

/-- For factors of order at least eight, the fourth-root image of an
elementary overgroup of the omega four has order at most four. -/
public theorem card_fourth_root_image_le_four_of_large_factors_overgroup
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) :
    Nat.card ((omegaTwoConjugation D).comp B.subtype).range ≤ 4 := by
  let ρ := (MulAut.conjNormal : P →* MulAut D).comp B.subtype
  change Nat.card ((omegaRestriction D 2 2).comp ρ).range ≤ 4
  rw [card_fourth_root_range_eq_on_eighth_roots]
  apply card_restriction_range_le_of_faithful_bound
  · intro a x hx
    apply Subtype.ext
    exact conjNormal_fixed_of_elementary_overgroup_omega W D B hO hWB a x
      (congrArg Subtype.val hx)
  · intro A hA hfix hfaith
    let : IsElementaryAbelian 2 A := hA
    exact HomocyclicFourTorsion.card_le_four_of_homocyclic_elementary_four_torsion
      3 (by decide) ((e.omega 2 3).trans (productOmegaEquiv n m 3 hn hm))
      A hfix hfaith

/-- The full action bound when both factors have order at least eight.
Neither global centrality nor uniqueness of the omega four is needed. -/
public theorem card_conj_image_le_four_of_large_factors_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 :=
  (NormalFourFourthRoot.card_conj_image_le_fourth_root_image_of_thick_factors
    hP hno W hW D hDC hO n m (by omega) (by omega) e B).trans
    (card_fourth_root_image_le_four_of_large_factors_overgroup W D B hO hWB n m hn hm e)

/-- The known cyclic-times-two calculation bounds the restricted action
without a central-omega-four hypothesis. -/
public theorem card_fourth_root_image_le_four_of_cyclic_two_overgroup
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsElementaryAbelian 2 B]
    (hO : (omega₁ D (p := 2)).map D.subtype = W) (hWB : W ≤ B)
    (n : ℕ) (hn : 2 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2))) :
    Nat.card ((omegaTwoConjugation D).comp B.subtype).range ≤ 4 := by
  exact abelian_cyclic_two_fixed_aut_omega_two_range_card_le_four_of_equiv hn e
    ((MulAut.conjNormal : P →* MulAut D).comp B.subtype)
    (conjNormal_fixed_of_elementary_overgroup_omega W D B hO hWB)

/-- A count excluding central fourth-root-kernel automorphisms suffices for
the full conjugation bound; the normal-four obstruction supplies that exclusion. -/
public theorem card_conj_image_le_four_of_central_kernel_count
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B)
    (hcount : ∀ A : Subgroup (MulAut D), IsElementaryAbelian 2 A →
      (∀ f ∈ A, ∀ d : D, d ^ 2 = 1 → f d = d) →
      (∀ f ∈ A, f ∈ center (MulAut D) → (∀ d : D, d ^ 4 = 1 → f d = d) → f = 1) →
      Nat.card A ≤ 4) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  let ρ := (MulAut.conjNormal : P →* MulAut D).comp B.subtype
  let : IsElementaryAbelian 2 ρ.range := by
    change IsElementaryAbelian 2 ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range
    rw [MonoidHom.range_comp, range_subtype]
    exact IsElementaryAbelian.map _
  apply hcount ρ.range inferInstance
  · rintro f ⟨b, rfl⟩ d hd
    exact conjNormal_fixed_of_elementary_overgroup_omega W D B hO hWB b d hd
  · exact NormalFourFourthRoot.conj_image_central_fourth_root_kernel_trivial
      hP hno W hW D hDC hO B

/-- The cyclic-times-two case of the full action bound. -/
public theorem card_conj_image_le_four_of_cyclic_two_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 2 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  apply card_conj_image_le_four_of_central_kernel_count hP hno W hW D hDC hO B hWB
  intro A _ hfix hcentral
  exact abelian_cyclic_two_aut_card_le_four_of_central_kernel hn e A hfix hcentral

/-- The two smaller-factor bounds assemble with the proved large
case to give the unequal-base bound in either orientation. -/
public theorem card_conj_image_le_four_of_unequal_overgroup_small_factor_bounds
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B)
    (hthin : ∀ k : ℕ, 2 ≤ k →
      (D ≃* (Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod 2))) →
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4)
    (hfour : ∀ k : ℕ, 3 ≤ k →
      (D ≃* (Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod 4))) →
      Nat.card ((omegaTwoConjugation D).comp B.subtype).range ≤ 4)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hne : n ≠ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  have ordered (k l : ℕ) (hl : 1 ≤ l) (hlk : l < k)
      (f : D ≃* (Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ l)))) :
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
    by_cases hl1 : l = 1
    · subst l
      exact hthin k (by omega) (by simpa using f)
    by_cases hl2 : l = 2
    · subst l
      exact (NormalFourFourthRoot.card_conj_image_le_fourth_root_image_of_thick_factors
        hP hno W hW D hDC hO k 2 (by omega) (by decide) f B).trans
        (hfour k (by omega) (by simpa using f))
    exact card_conj_image_le_four_of_large_factors_overgroup hP hno W hW D hDC hO
      k l (by omega) (by omega) f B hWB
  rcases lt_or_gt_of_ne hne with h | h
  · exact ordered m n hn h (e.trans MulEquiv.prodComm)
  · exact ordered n m hm h e

open UnequalCyclicFourNormControl in
private theorem cyclic_four_control_fix (n : ℕ) (hn : 3 ≤ n)
    (f : MulAut (V n)) (hf : f ∈ controlSubgroup n)
    (x : V n) (hx : x ^ 2 = 1) : f x = x := by
  have hx4 : x ^ 4 = 1 := by
    calc
      x ^ 4 = (x ^ 2) ^ 2 := pow_mul x 2 2
      _ = 1 := by rw [hx, one_pow]
  obtain ⟨a, ha⟩ := roots_le_squares n hn (congrArg Prod.fst hx4)
  have shortRoot : ∀ b : C4, b ^ 2 = 1 → ∃ c : C4, c ^ 2 = b := by decide
  obtain ⟨b, hb⟩ := shortRoot x.2 (congrArg Prod.snd hx)
  have hr : (a, b) ^ 2 = x := Prod.ext ha hb
  exact hr ▸ hf.1 (a, b)

open UnequalCyclicFourNormControl in
/-- The normal-four obstruction excludes the intrinsic cyclic-four control
subgroup without assuming that the ambient group fixes the omega four. -/
public theorem cyclic_four_conj_image_disjoint_control
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n) (e : D ≃* V n)
    (B : Subgroup P) [IsElementaryAbelian 2 B] :
    (((MulAut.congr e).toMonoidHom.comp
      ((MulAut.conjNormal : P →* MulAut D).comp B.subtype)).range) ⊓
        controlSubgroup n = ⊥ := by
  let : (control n hn).subgroup.Normal := controlSubgroup_normal n
  exact NormalFourNormControl.conj_image_disjoint_norm_control hP hno W hW D hDC hO
    e (control n hn) (cyclic_four_control_fix n hn) B

open UnequalCyclicFourNormControl in
/-- Multiplicative diagonal signs and their involutive kernel description
suffice to count the C₄ case once normal norm control is excluded. -/
public theorem card_conj_image_le_four_of_cyclic_four_overgroup_diagonal_lemmas
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n) (e : D ≃* V n)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B)
    (hmul : ∀ f g : involutionFixing n,
      diagonal n hn ((f : MulAut (V n)) * g) = diagonal n hn f * diagonal n hn g)
    (hkernel : ∀ f : involutionFixing n, (f : MulAut (V n)) ^ 2 = 1 →
      diagonal n hn f = 1 → (f : MulAut (V n)) ∈ controlSubgroup n) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  let ρ := (MulAut.conjNormal : P →* MulAut D).comp B.subtype
  let F := (MulAut.congr e).toMonoidHom.comp ρ
  let H := F.range
  let : IsElementaryAbelian 2 H := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply Subtype.ext
      obtain ⟨b, hb⟩ := x.property
      change (x : MulAut (V n)) ^ 2 = 1
      rw [← hb, ← map_pow]
      rw [show b ^ 2 = 1 from Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian (b : P) b.property), map_one] }
  have hfix : ∀ f ∈ H, ∀ x : V n, x ^ 2 = 1 → f x = x := by
    rintro f ⟨b, rfl⟩ x hx
    change e (MulAut.conjNormal (b : P) (e.symm x)) = x
    rw [conjNormal_fixed_of_elementary_overgroup_omega W D B hO hWB b (e.symm x)
      (by rw [← map_pow, hx, map_one])]
    exact e.apply_symm_apply x
  have hdis : H ⊓ controlSubgroup n = ⊥ :=
    cyclic_four_conj_image_disjoint_control hP hno W hW D hDC hO n hn e B
  let d : involutionFixing n →* (ZMod 4 × ZMod 4) :=
    { toFun := fun f => diagonal n hn f
      map_one' := diagonal_one n hn
      map_mul' := hmul }
  let inclusion : H →* involutionFixing n :=
    { toFun := fun f => ⟨f, hfix f f.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let s := d.toHomUnits.comp inclusion
  have hs : Function.Injective s := by
    apply s.ker_eq_bot_iff.mp
    rw [Subgroup.eq_bot_iff_forall]
    intro f hf
    apply Subtype.ext
    have he : diagonal n hn (f : MulAut (V n)) = 1 := by
      exact congrArg (fun u : (ZMod 4 × ZMod 4)ˣ => (u : ZMod 4 × ZMod 4)) hf
    have hfT := hkernel (inclusion f)
      (elemPow_eq_one_of_isElementaryAbelian (f : MulAut (V n)) f.property) he
    have hmem : (f : MulAut (V n)) ∈ H ⊓ controlSubgroup n := ⟨f.property, hfT⟩
    rwa [hdis, Subgroup.mem_bot] at hmem
  have hc : Nat.card (ZMod 4 × ZMod 4)ˣ = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hb : Nat.card H ≤ 4 := (Nat.card_le_card_of_injective s hs).trans_eq hc
  change Nat.card (((MulAut.congr e).toMonoidHom.comp ρ).range) ≤ 4 at hb
  rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective] at hb
  exact hb

open UnequalCyclicFourNormControl in
/-- Final unequal-factor assembly reduced solely to the two independent
cyclic-four diagonal identities. All ambient structural premises are discharged. -/
public theorem card_conj_image_le_four_of_unequal_overgroup_diagonal_lemmas
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B)
    (hmul : ∀ k (hk : 3 ≤ k) (f g : involutionFixing k),
      diagonal k hk ((f : MulAut (V k)) * g) = diagonal k hk f * diagonal k hk g)
    (hkernel : ∀ k (hk : 3 ≤ k) (f : involutionFixing k), (f : MulAut (V k)) ^ 2 = 1 →
      diagonal k hk f = 1 → (f : MulAut (V k)) ∈ controlSubgroup k)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hne : n ≠ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 := by
  apply card_conj_image_le_four_of_unequal_overgroup_small_factor_bounds
    hP hno W hW D hDC hO B hWB ?_ ?_ n m hn hm hne e
  · intro k hk f
    exact card_conj_image_le_four_of_cyclic_two_overgroup hP hno W hW D hDC hO k hk f B hWB
  · intro k hk f
    have hb := card_conj_image_le_four_of_cyclic_four_overgroup_diagonal_lemmas
      hP hno W hW D hDC hO k hk f B hWB (hmul k hk) (hkernel k hk)
    let : (omega D (p := 2) 2).Characteristic := omega_characteristic D 2
    change Nat.card (((MulAut.characteristic (omega D (p := 2) 2)).comp
      ((MulAut.conjNormal : P →* MulAut D).comp B.subtype)).range) ≤ 4
    rw [MonoidHom.range_comp]
    exact (Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)).trans hb

/-- An elementary overgroup of a normal omega four has conjugation image
of order at most four on a cyclic two-group times C₄. -/
public theorem card_conj_image_le_four_of_cyclic_four_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 4)))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 :=
  card_conj_image_le_four_of_cyclic_four_overgroup_diagonal_lemmas
    hP hno W hW D hDC hO n hn e B hWB
    (UnequalCyclicFourNormControl.diagonal_mul n hn)
    (UnequalCyclicFourNormControl.diagonal_kernel_mem n hn)

/-- The unequal-factor action bound needs only normality of the omega four,
with no assumption on the order of the central omega or uniqueness of the four. -/
public theorem card_conj_image_le_four_of_normal_four_unequal_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hne : n ≠ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 :=
  card_conj_image_le_four_of_unequal_overgroup_diagonal_lemmas
    hP hno W hW D hDC hO B hWB
    UnequalCyclicFourNormControl.diagonal_mul
    UnequalCyclicFourNormControl.diagonal_kernel_mem n m hn hm hne e

/-- The unequal-base action bound in the central-omega-two, unique-normal-four
case. The ambient exclusion concerns only normal elementary subgroups. -/
public theorem card_conj_image_le_four_of_unequal_overgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (_hZ : Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 2)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (_hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hne : n ≠ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hWB : W ≤ B) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range ≤ 4 :=
  card_conj_image_le_four_of_normal_four_unequal_overgroup
    hP hno W hW D hDC hO n m hn hm hne e B hWB

end IsPGroup
