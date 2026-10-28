module

public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
A proper image in an algebraic torus is annihilated by a nontrivial character.

After transporting the closed image to a standard diagonal torus, the proof
normalizes a separating polynomial to a finite Laurent sum. A vanishing sum
of minimal support is proportional to each of its translates by the image;
the ratio of two distinct exponents in its support is therefore the required
character. The character itself is constructed directly from positive and
negative exponent polynomials, without using a maximal-torus image theorem.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

public theorem IsTorus.exists_character_ne_one_of_not_surjective
    {k : Type*} [Field k] [IsAlgClosed k]
    {S H : Variety k} [AlgebraicGroup S] [AlgebraicGroup H]
    (hS : IsTorus S) (hH : IsTorus H)
    (q : AlgebraicGroup.Morphism S H)
    (hq : ¬ Function.Surjective q.onPoints) :
    ∃ χ : AlgebraicGroup.Morphism H (KMult k),
      (∀ x, χ.onPoints (q.onPoints x) = 1) ∧
      ∃ y, χ.onPoints y ≠ 1 := by
  classical
  rcases hH with ⟨n, ⟨e⟩⟩
  let B : Set (Variety.Point (dVariety k n)) :=
    e.hom.onPoints ⁻¹' (q.imageClosedSubgroup : Set (Variety.Point H))
  have B_closed : IsZariskiClosed (dVariety k n) B :=
    e.hom.toVariety.isZariskiClosed_preimage
      q.imageClosedSubgroup.isZariskiClosed
  have B_one : (1 : Variety.Point (dVariety k n)) ∈ B := by
    change e.hom.onPoints 1 ∈ q.imageClosedSubgroup
    rw [map_one]
    exact ⟨1, q.map_one⟩
  have B_mul {x y : Variety.Point (dVariety k n)}
      (hx : x ∈ B) (hy : y ∈ B) : x * y ∈ B := by
    change e.hom.onPoints (x * y) ∈ q.imageClosedSubgroup
    rw [map_mul]
    exact q.imageClosedSubgroup.toSubgroup.mul_mem hx hy
  change ¬ ∀ y, ∃ x, q.onPoints x = y at hq
  push Not at hq
  obtain ⟨y, hy⟩ := hq
  let yD : Variety.Point (dVariety k n) := e.inv.onPoints y
  have yD_not_mem : yD ∉ B := by
    intro hyD
    change e.hom.onPoints (e.inv.onPoints y) ∈ q.imageClosedSubgroup at hyD
    rw [e.inv_hom_id] at hyD
    rcases hyD with ⟨x, hx⟩
    exact hy x hx
  have not_all_equations :
      ¬ ∀ p ∈ Variety.closedEquations B_closed,
        evalPolynomial yD.val p = 0 := by
    intro hall
    apply yD_not_mem
    rw [Variety.closedEquations_spec B_closed]
    exact hall
  push Not at not_all_equations
  obtain ⟨p, hp, hp_yD⟩ := not_all_equations
  have hp_B (x : Variety.Point (dVariety k n)) (hx : x ∈ B) :
      evalPolynomial x.val p = 0 := by
    have hx' : x ∈ {z | ∀ r ∈ Variety.closedEquations B_closed,
        evalPolynomial z.val r = 0} := by
      rw [← Variety.closedEquations_spec B_closed]
      exact hx
    exact hx' p hp

  let exponent : ((dVariety k n).Coordinates →₀ ℕ) →
      (ULift (Fin n) → ℤ) :=
    fun d i => (d (Sum.inl i) : ℤ) - (d (Sum.inr i) : ℤ)
  let monomialValue : (ULift (Fin n) → ℤ) →
      Variety.Point (dVariety k n) → kˣ :=
    fun a x => ∏ i, dPointEquiv n x i.down ^ a i
  let evaluateLaurent (f : (ULift (Fin n) → ℤ) →₀ k)
      (x : Variety.Point (dVariety k n)) : k :=
    Finsupp.linearCombination k (fun a => (monomialValue a x).val) f
  let normalizeLaurent
      (r : MvPolynomial (dVariety k n).Coordinates k) :
      (ULift (Fin n) → ℤ) →₀ k :=
    Finsupp.mapDomain exponent (AddMonoidAlgebra.coeff r)
  have monomialValue_one (a : ULift (Fin n) → ℤ) :
      monomialValue a (1 : Variety.Point (dVariety k n)) = 1 := by
    simp [monomialValue, dPointEquiv_one]
  have monomialValue_mul (a : ULift (Fin n) → ℤ)
      (x y : Variety.Point (dVariety k n)) :
      monomialValue a (x * y) = monomialValue a x * monomialValue a y := by
    simp only [monomialValue, congrFun (dPointEquiv_mul n x y),
      Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  have monomialValue_neg (a : ULift (Fin n) → ℤ)
      (x : Variety.Point (dVariety k n)) :
      monomialValue (-a) x = (monomialValue a x)⁻¹ := by
    simp [monomialValue, ← Finset.prod_inv_distrib]
  have monomialValue_sub (a b : ULift (Fin n) → ℤ)
      (x : Variety.Point (dVariety k n)) :
      monomialValue (a - b) x =
        monomialValue a x * (monomialValue b x)⁻¹ := by
    simp [monomialValue, zpow_sub, Finset.prod_mul_distrib,
      ← Finset.prod_inv_distrib]
  have rawMonomial_eval
      (d : (dVariety k n).Coordinates →₀ ℕ)
      (x : Variety.Point (dVariety k n)) :
      (monomialValue (exponent d) x).val =
        d.prod fun c m => x.val c ^ m := by
    rw [Finsupp.prod_fintype]
    · rw [Fintype.prod_sum_type, Units.coe_prod]
      simp only [exponent, zpow_sub, Units.val_mul,
        Units.val_inv_eq_inv_val, zpow_natCast,
        Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      change (dPointEntry n x i.down ^ d (Sum.inr i))⁻¹ =
        dPointEntryInv n x i.down ^ d (Sum.inr i)
      rw [← inv_pow, dPoint_entry_inv]
    · intro c
      simp
  have normalizeLaurent_eval
      (r : MvPolynomial (dVariety k n).Coordinates k)
      (x : Variety.Point (dVariety k n)) :
      evaluateLaurent (normalizeLaurent r) x = evalPolynomial x.val r := by
    simp only [evaluateLaurent, Finsupp.linearCombination_apply,
      smul_eq_mul, normalizeLaurent]
    rw [Finsupp.sum_mapDomain_index]
    · rw [show evalPolynomial x.val r =
          (AddMonoidAlgebra.coeff r).sum
            (fun d c => c * d.prod fun i m => x.val i ^ m) by rfl]
      apply Finsupp.sum_congr
      intro d c
      rw [rawMonomial_eval]
    · intro a
      simp
    · intro a c d
      simp [add_mul]
  let f0 := normalizeLaurent p
  have f0_ne : f0 ≠ 0 := by
    intro hf0
    change normalizeLaurent p = 0 at hf0
    apply hp_yD
    rw [← normalizeLaurent_eval p yD, hf0]
    simp [evaluateLaurent]
  have f0_vanishes : ∀ x ∈ B, evaluateLaurent f0 x = 0 := by
    intro x hx
    rw [normalizeLaurent_eval]
    exact hp_B x hx
  have candidate_exists :
      ∃ m : ℕ, ∃ f : (ULift (Fin n) → ℤ) →₀ k,
        f ≠ 0 ∧
        (∀ x ∈ B, evaluateLaurent f x = 0) ∧
        f.support.card = m :=
    ⟨f0.support.card, f0, f0_ne, f0_vanishes, rfl⟩
  let m := Nat.find candidate_exists
  obtain ⟨f, f_ne, f_vanishes, f_card⟩ :
      ∃ f : (ULift (Fin n) → ℤ) →₀ k,
        f ≠ 0 ∧
        (∀ x ∈ B, evaluateLaurent f x = 0) ∧
        f.support.card = m := by
    simpa [m] using Nat.find_spec candidate_exists
  have support_minimal
      (g : (ULift (Fin n) → ℤ) →₀ k) (g_ne : g ≠ 0)
      (g_vanishes : ∀ x ∈ B, evaluateLaurent g x = 0) :
      f.support.card ≤ g.support.card := by
    rw [f_card]
    exact Nat.find_min' candidate_exists
      ⟨g, g_ne, g_vanishes, rfl⟩
  have f_support_nonempty : f.support.Nonempty := by
    exact Finsupp.support_nonempty_iff.mpr f_ne
  have support_card_gt_one : 1 < f.support.card := by
    by_contra hcard
    have hcard_le : f.support.card ≤ 1 := Nat.le_of_not_gt hcard
    have hcard_pos : 0 < f.support.card :=
      Finset.card_pos.mpr f_support_nonempty
    have hcard_eq : f.support.card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard_eq
    have ha_mem : a ∈ f.support := by rw [ha]; simp
    have f_single : f = Finsupp.single a (f a) :=
      (Finsupp.support_eq_singleton.mp ha).2
    have hf_one := f_vanishes 1 B_one
    rw [f_single] at hf_one
    simp [evaluateLaurent, Finsupp.linearCombination_apply,
      monomialValue_one] at hf_one
    exact (Finsupp.mem_support_iff.mp ha_mem) hf_one
  obtain ⟨a0, ha0, a1, ha1, a0_ne_a1⟩ :=
    Finset.one_lt_card.mp support_card_gt_one
  have a1_ne_a0 : a1 ≠ a0 := a0_ne_a1.symm

  let translate (b : Variety.Point (dVariety k n))
      (g : (ULift (Fin n) → ℤ) →₀ k) :
      (ULift (Fin n) → ℤ) →₀ k :=
    Finsupp.onFinset g.support
      (fun a => g a * (monomialValue a b).val)
      (by
        intro a ha
        rw [Finsupp.mem_support_iff]
        intro hga
        apply ha
        simp [hga])
  have translate_apply (b : Variety.Point (dVariety k n))
      (g : (ULift (Fin n) → ℤ) →₀ k) (a : ULift (Fin n) → ℤ) :
      translate b g a = g a * (monomialValue a b).val := by
    simp [translate]
  have translate_support (b : Variety.Point (dVariety k n))
      (g : (ULift (Fin n) → ℤ) →₀ k) :
      (translate b g).support = g.support := by
    ext a
    simp [Finsupp.mem_support_iff, translate_apply]
  have evaluate_translate (b : Variety.Point (dVariety k n))
      (g : (ULift (Fin n) → ℤ) →₀ k)
      (x : Variety.Point (dVariety k n)) :
      evaluateLaurent (translate b g) x = evaluateLaurent g (b * x) := by
    simp only [evaluateLaurent, Finsupp.linearCombination_apply,
      smul_eq_mul, Finsupp.sum]
    rw [translate_support]
    apply Finset.sum_congr rfl
    intro a ha
    rw [translate_apply, monomialValue_mul]
    simp [mul_assoc]
  have translate_relation (b : Variety.Point (dVariety k n)) (hb : b ∈ B) :
      translate b f = (monomialValue a0 b).val • f := by
    let g := translate b f - (monomialValue a0 b).val • f
    have g_vanishes : ∀ x ∈ B, evaluateLaurent g x = 0 := by
      intro x hx
      dsimp only [g]
      simp only [evaluateLaurent, map_sub, map_smul]
      change evaluateLaurent (translate b f) x -
        (monomialValue a0 b).val * evaluateLaurent f x = 0
      rw [evaluate_translate, f_vanishes (b * x) (B_mul hb hx),
        f_vanishes x hx]
      simp
    have g_a0 : g a0 = 0 := by
      simp [g, translate_apply, mul_comm]
    have g_support_subset : g.support ⊆ f.support.erase a0 := by
      intro a ha
      have hga : g a ≠ 0 := Finsupp.mem_support_iff.mp ha
      have hane : a ≠ a0 := by
        intro hae
        subst a
        exact hga g_a0
      have haf : a ∈ f.support := by
        rw [Finsupp.mem_support_iff]
        intro hfa
        apply hga
        simp [g, translate_apply, hfa]
      exact Finset.mem_erase.mpr ⟨hane, haf⟩
    have g_zero : g = 0 := by
      by_contra g_ne
      have hmin := support_minimal g g_ne g_vanishes
      have hle := Finset.card_le_card g_support_subset
      have hlt := Finset.card_erase_lt_of_mem ha0
      omega
    apply sub_eq_zero.mp
    exact g_zero
  have support_values_equal (b : Variety.Point (dVariety k n)) (hb : b ∈ B)
      (a : ULift (Fin n) → ℤ) (ha : a ∈ f.support) :
      monomialValue a b = monomialValue a0 b := by
    have h := congrArg (fun g : (ULift (Fin n) → ℤ) →₀ k => g a)
      (translate_relation b hb)
    rw [translate_apply] at h
    simp only [Finsupp.smul_apply, smul_eq_mul] at h
    have hfa : f a ≠ 0 := Finsupp.mem_support_iff.mp ha
    apply Units.ext
    apply mul_left_cancel₀ hfa
    simpa [mul_comm] using h
  let z := a1 - a0
  have z_ne : z ≠ 0 := sub_ne_zero.mpr a1_ne_a0
  have z_annihilates (x : Variety.Point (dVariety k n)) (hx : x ∈ B) :
      monomialValue z x = 1 := by
    rw [show z = a1 - a0 by rfl, monomialValue_sub,
      support_values_equal x hx a1 ha1]
    simp

  let monomialPolynomial (a : ULift (Fin n) → ℤ) :
      MvPolynomial (dVariety k n).Coordinates k :=
    ∏ i : ULift (Fin n),
      MvPolynomial.X (Sum.inl i) ^ (a i).toNat *
      MvPolynomial.X (Sum.inr i) ^ (-a i).toNat
  have eval_monomialPolynomial (a : ULift (Fin n) → ℤ)
      (x : Variety.Point (dVariety k n)) :
      evalPolynomial x.val (monomialPolynomial a) =
        (monomialValue a x).val := by
    rw [show evalPolynomial x.val (monomialPolynomial a) =
        ∏ i : ULift (Fin n),
          (x.val (Sum.inl i) ^ (a i).toNat *
            x.val (Sum.inr i) ^ (-a i).toNat) by
      simp [monomialPolynomial, evalPolynomial]]
    rw [Units.coe_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rcases i with ⟨i⟩
    cases h : a (ULift.up i) with
    | ofNat m =>
        simp [h]
        change dPointEntry n x i ^ m =
          ((dPointEquiv n x i) ^ m : kˣ).val
        rfl
    | negSucc m =>
        simp [h]
        change dPointEntryInv n x i ^ (m + 1) =
          (dPointEntry n x i ^ (m + 1))⁻¹
        rw [← inv_pow, dPoint_entry_inv]
  let χD : AlgebraicGroup.Morphism (dVariety k n) (KMult k) :=
    { toVariety :=
        { toFun := fun x =>
            (dPointEquiv 1).symm (fun _ => monomialValue z x)
          regular := by
            intro c
            cases c with
            | inl i =>
                refine ⟨monomialPolynomial z, ?_⟩
                intro x
                rw [dPointEquiv_symm_val_inl]
                exact (eval_monomialPolynomial z x).symm
            | inr i =>
                refine ⟨monomialPolynomial (-z), ?_⟩
                intro x
                rw [dPointEquiv_symm_val_inr, eval_monomialPolynomial,
                  monomialValue_neg]
                exact Units.inv_eq_val_inv _ }
      map_one := by
        apply (dPointEquiv 1).injective
        rw [dPointEquiv_one, (dPointEquiv 1).apply_symm_apply]
        funext i
        exact monomialValue_one z
      map_mul := by
        intro x y
        apply (dPointEquiv 1).injective
        rw [dPointEquiv_mul, (dPointEquiv 1).apply_symm_apply,
          (dPointEquiv 1).apply_symm_apply,
          (dPointEquiv 1).apply_symm_apply]
        funext i
        exact monomialValue_mul z x y }
  let χ : AlgebraicGroup.Morphism H (KMult k) := χD.comp e.inv
  refine ⟨χ, ?_, ?_⟩
  · intro x
    let xD := e.inv.onPoints (q.onPoints x)
    have hxD : xD ∈ B := by
      change e.hom.onPoints (e.inv.onPoints (q.onPoints x)) ∈
        q.imageClosedSubgroup
      rw [e.inv_hom_id]
      exact ⟨x, rfl⟩
    change (dPointEquiv 1).symm (fun _ => monomialValue z xD) = 1
    apply (dPointEquiv 1).injective
    rw [(dPointEquiv 1).apply_symm_apply, dPointEquiv_one]
    funext i
    exact z_annihilates xD hxD
  · have z_coordinate : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      apply z_ne
      funext i
      exact h i
    obtain ⟨i, hi⟩ := z_coordinate
    rcases i with ⟨i⟩
    obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (k := k) hi
    let xD : Variety.Point (dVariety k n) :=
      (dPointEquiv n).symm (fun j => if j = i then a else 1)
    have hxD : monomialValue z xD ≠ 1 := by
      change (∏ j : ULift (Fin n),
          (if j.down = i then a else 1) ^ z j) ≠ 1
      rw [Finset.prod_eq_single (ULift.up i)]
      · simpa using ha
      · intro j hj hji
        have hjdown : j.down ≠ i := by
          intro h
          apply hji
          exact congrArg ULift.up h
        simp [hjdown]
      · simp
    refine ⟨e.hom.onPoints xD, ?_⟩
    change χD.onPoints (e.inv.onPoints (e.hom.onPoints xD)) ≠ 1
    rw [e.hom_inv_id]
    intro hχ
    change (dPointEquiv 1).symm (fun _ => monomialValue z xD) = 1 at hχ
    have hχ' := congrArg (dPointEquiv 1) hχ
    rw [(dPointEquiv 1).apply_symm_apply, dPointEquiv_one] at hχ'
    exact hxD (congrFun hχ' 0)

end Theory.AlgebraicGroup
