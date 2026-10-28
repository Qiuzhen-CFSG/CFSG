module

public import Theory.Character.AbelianLinearCharacters
public import Theory.GroupTheory.HomocyclicSylowCentralizers

/-!
# Ordinary linear characters for a rank-two homocyclic Sylow subgroup

The normalizer image acts freely on nonprincipal linear characters: the
fixed-point-free displacement automorphism on the group is surjective, so a
fixed character is principal. Fusion control identifies actual ambient
conjugacy with this normalizer image. Orbit sums count each subgroup element
once. Ordinary character completeness then supplies the Fourier consequences.

Source: Brauer, *Some applications of the theory of blocks of characters of
finite groups. II* (1964), §VI (6.2)–(6.6), following §V Lemma 3. See
refs/original/brauer-homocyclic-sylow/README.md.
-/

public section
noncomputable section
open scoped BigOperators IsMulCommutative
attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace HomocyclicSylowLinearCharacters

section FourierHelpers

variable {A : Type*} [Group A] [Fintype A]
omit [Group A] in
private theorem scalarProduct_sub_right (f g h : A → ℂ) :
    scalarProduct A f (g - h) = scalarProduct A f g - scalarProduct A f h := by
  simp only [scalarProduct, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib]
omit [Group A] in
private theorem scalarProduct_sum_left {ι : Type*} [Fintype ι]
    (f : ι → A → ℂ) (g : A → ℂ) :
    scalarProduct A (fun s => ∑ i, f i s) g = ∑ i, scalarProduct A (f i) g := by
  simp only [scalarProduct, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm
private theorem scalarProduct_comp (f g : A → ℂ) (a : MulAut A) :
    scalarProduct A (fun s => f (a s)) (fun s => g (a s)) = scalarProduct A f g := by
  unfold scalarProduct
  congr 1
  exact a.toEquiv.sum_comp (fun s => f s * star (g s))
/-- Precomposition preserves coefficients of functions invariant under it. -/
theorem scalarProduct_comp_of_invariant (f g : A → ℂ) (a : MulAut A)
    (hf : ∀ s, f (a s) = f s) :
    scalarProduct A f (fun s => g (a s)) = scalarProduct A f g := by
  have he : (fun s => f (a s)) = f := funext hf
  simpa only [he] using scalarProduct_comp f g a
/-- Orthogonality of the differences from the principal character. -/
theorem scalarProduct_sub_one (χ ψ : A →* ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    scalarProduct A ((χ : A → ℂ) - 1) ((ψ : A → ℂ) - 1) =
      1 + if χ = ψ then 1 else 0 := by
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
  have hft : Fintype.ofFinite A = ‹Fintype A› := Subsingleton.elim _ _
  have hc := AbelianLinearCharacters.orthogonal χ ψ
  have hl := AbelianLinearCharacters.orthogonal χ 1
  have hr := AbelianLinearCharacters.orthogonal 1 ψ
  have ho := AbelianLinearCharacters.orthogonal (1 : A →* ℂ) 1
  rw [hft] at hc hl hr ho
  change scalarProduct A (χ : A → ℂ) 1 = _ at hl
  change scalarProduct A 1 (ψ : A → ℂ) = _ at hr
  change scalarProduct A 1 1 = _ at ho
  rw [hc, hl, hr, ho, if_neg hχ, if_neg (Ne.symm hψ), if_pos rfl]
  ring

end FourierHelpers

variable {A : Type*} [Group A] [Finite A] [IsMulCommutative A]

/-- A fixed-point-free automorphism fixes no nonprincipal linear character. -/
theorem character_eq_one_of_fixed (a : MulAut A)
    (hfixed : ∀ s : A, a s = s → s = 1) (χ : A →* ℂ)
    (hχ : χ.comp a.toMonoidHom = χ) : χ = 1 := by
  let d : A →* A := a.toMonoidHom / MonoidHom.id A
  have hinj : Function.Injective d := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro s hs
    exact hfixed s (div_eq_one.mp (show a s / s = 1 from hs))
  have hsurj := Finite.surjective_of_injective hinj
  ext s
  obtain ⟨t, rfl⟩ := hsurj s
  change χ (a t / t) = 1
  have ht : χ (a t) = χ t := DFunLike.congr_fun hχ t
  rw [map_div, ht]
  apply div_self
  intro hz
  have hh := χ.map_mul t t⁻¹
  simp [hz] at hh

/-- Precomposition by a freely acting automorphism group is free on
nonprincipal complex characters. -/
theorem character_orbit_injective (K : Subgroup (MulAut A))
    (hfixed : ∀ a : K, a ≠ 1 → ∀ s : A, (a : MulAut A) s = s → s = 1)
    (χ : A →* ℂ) (hχ : χ ≠ 1) :
    Function.Injective (fun a : K => χ.comp (a : MulAut A).toMonoidHom) := by
  intro a b hab
  by_contra hne
  have hd : a * b⁻¹ ≠ 1 := fun he => hne (mul_inv_eq_one.mp he)
  apply hχ
  apply character_eq_one_of_fixed (a * b⁻¹ : K).val (hfixed _ hd)
  ext s
  have hh := DFunLike.congr_fun hab ((b : MulAut A).symm s)
  simpa using hh

omit [Finite A] [IsMulCommutative A] in
private theorem comp_ne_one (χ : A →* ℂ) (hχ : χ ≠ 1) (a : MulAut A) :
    χ.comp a.toMonoidHom ≠ 1 := by
  intro h
  apply hχ
  ext s
  have hh := DFunLike.congr_fun h (a.symm s)
  simpa using hh
private def characterSetoid (K : Subgroup (MulAut A)) : Setoid {χ : A →* ℂ // χ ≠ 1} where
  r χ ψ := ∃ a : K, χ.val.comp a.val.toMonoidHom = ψ.val
  iseqv := {
    refl := by intro χ; exact ⟨1, by ext s; rfl⟩
    symm := by
      rintro χ ψ ⟨a, ha⟩
      refine ⟨a⁻¹, ?_⟩
      ext s
      have hh := DFunLike.congr_fun ha (a.val.symm s)
      simpa using hh.symm
    trans := by
      rintro χ ψ θ ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      ext s
      have h1 : χ.val (a.val (b.val s)) = ψ.val (b.val s) := DFunLike.congr_fun ha (b.val s)
      exact h1.trans (DFunLike.congr_fun hb s) }

/-- Actual representatives and unique automizers, with a specified first character. -/
theorem exists_pointed_orbit_representatives (K : Subgroup (MulAut A))
    (hfixed : ∀ a : K, a ≠ 1 → ∀ s : A, a.val s = s → s = 1)
    (χ₀ : A →* ℂ) (hχ₀ : χ₀ ≠ 1) :
    ∃ (r : ℕ) (hr : 0 < r) (ψ : Fin r → A →* ℂ),
      ψ ⟨0, hr⟩ = χ₀ ∧
      (∀ j, ψ j ≠ 1) ∧
      Function.Injective (fun p : Fin r × K => (ψ p.1).comp p.2.val.toMonoidHom) ∧
      (∀ χ : A →* ℂ, χ ≠ 1 → ∃ (j : Fin r) (a : K), (ψ j).comp a.val.toMonoidHom = χ) ∧
      r * Nat.card K + 1 = Nat.card A := by
  classical
  let X := {χ : A →* ℂ // χ ≠ 1}
  let R := characterSetoid (A := A) K
  let Q := Quotient R
  let x₀ : X := ⟨χ₀, hχ₀⟩
  let q₀ : Q := Quotient.mk R x₀
  let rep (q : Q) : X := if q = q₀ then x₀ else q.out
  have hrep (q : Q) : Quotient.mk R (rep q) = q := by
    dsimp [rep]
    split_ifs with h
    · exact h.symm
    · exact q.out_eq
  have hr : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q₀⟩
  let E : Q ≃ Fin (Fintype.card Q) :=
    (Fintype.equivFin Q).trans (Equiv.swap ((Fintype.equivFin Q) q₀) ⟨0, hr⟩)
  have he : E q₀ = ⟨0, hr⟩ := by simp [E]
  let ψ (j : Fin (Fintype.card Q)) : A →* ℂ := (rep (E.symm j)).val
  have hψ (j) : ψ j ≠ 1 := (rep (E.symm j)).property
  let F : Fin (Fintype.card Q) × K → X := fun p =>
    ⟨(ψ p.1).comp p.2.val.toMonoidHom, comp_ne_one _ (hψ p.1) _⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have hea : Quotient.mk R (F (i,a)) = E.symm i := by
        rw [← hrep (E.symm i)]
        symm
        exact Quotient.sound ⟨a, rfl⟩
      have heb : Quotient.mk R (F (j,b)) = E.symm j := by
        rw [← hrep (E.symm j)]
        symm
        exact Quotient.sound ⟨b, rfl⟩
      have hij : i = j := E.symm.injective (hea.symm.trans ((congrArg (Quotient.mk R) hab).trans heb))
      subst j
      congr 1
      exact character_orbit_injective K hfixed (ψ i) (hψ i) (congrArg Subtype.val hab)
    · intro χ
      let q : Q := Quotient.mk R χ
      have hrel : R (rep q) χ := Quotient.exact (hrep q)
      obtain ⟨a, ha⟩ := hrel
      refine ⟨(E q, a), Subtype.ext ?_⟩
      change (ψ (E q)).comp a.val.toMonoidHom = χ.val
      simpa only [ψ, E.symm_apply_apply] using ha
  refine ⟨Fintype.card Q, hr, ψ, ?_, hψ, ?_, ?_, ?_⟩
  · change (rep (E.symm ⟨0, hr⟩)).val = χ₀
    rw [← he, E.symm_apply_apply]
    simp [rep, x₀]
  · intro p q hpq
    exact hF.1 (Subtype.ext hpq)
  · intro χ hχ
    obtain ⟨⟨j,a⟩, ha⟩ := hF.2 ⟨χ,hχ⟩
    exact ⟨j,a,congrArg Subtype.val ha⟩
  · have hc := Nat.card_congr (Equiv.ofBijective F hF)
    simp only [Nat.card_prod, Nat.card_fin] at hc
    have hx : Nat.card X + 1 = Nat.card (A →* ℂ) := by
      simp only [X, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_unique]
      exact Nat.sub_add_cancel Fintype.card_pos
    rw [hc, hx, AbelianLinearCharacters.card]

omit [Finite A] [IsMulCommutative A] in
/-- A homocyclic coordinate gives an actual nonprincipal order-two character,
whose support away from one consists of elements of full exponent. -/
theorem exists_order_two_character {n : ℕ} (hn : 1 ≤ n)
    (e : A ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n)))) :
    ∃ χ : A →* ℂ, χ ≠ 1 ∧ (∀ s, χ s ^ 2 = 1) ∧
      (∀ s, χ s ≠ 1 → orderOf s = 2 ^ n) := by
  let B := Multiplicative (ZMod 2)
  have hc : Nat.card (B →* ℂ) = 2 := by
    rw [AbelianLinearCharacters.card]
    simp [B, Nat.card_eq_fintype_card]
  have hb : Nontrivial (B →* ℂ) := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card, hc]
    omega
  obtain ⟨θ, hθ⟩ := exists_ne (1 : B →* ℂ)
  let q : ZMod (2 ^ n) →+* ZMod 2 := ZMod.castHom (dvd_pow_self 2 (by omega)) (ZMod 2)
  let f : A →* B := q.toAddMonoidHom.toMultiplicative.comp ((MonoidHom.fst _ _).comp e.toMonoidHom)
  have hfsurj : Function.Surjective f := by
    intro b
    obtain ⟨z, hz⟩ := ZMod.castHom_surjective (dvd_pow_self 2 (by omega : n ≠ 0)) b.toAdd
    refine ⟨e.symm (Multiplicative.ofAdd z, 1), ?_⟩
    change Multiplicative.ofAdd (q (e (e.symm (Multiplicative.ofAdd z, 1))).1.toAdd) = b
    simpa [q] using congrArg Multiplicative.ofAdd hz
  have htwo (b : B) : b ^ 2 = 1 := by
    change (2 : ℕ) • b.toAdd = 0
    rw [nsmul_eq_mul]
    change (2 : ZMod 2) * b.toAdd = 0
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]
  refine ⟨θ.comp f, ?_, ?_, ?_⟩
  · intro he
    apply hθ
    ext b
    obtain ⟨s, rfl⟩ := hfsurj b
    exact DFunLike.congr_fun he s
  · intro s
    change θ (f s) ^ 2 = 1
    rw [← map_pow, htwo, map_one]
  · intro s hs
    have hq : q (e s).1.toAdd ≠ 0 := by
      intro h
      apply hs
      change θ (Multiplicative.ofAdd (q (e s).1.toAdd)) = 1
      rw [h]
      exact θ.map_one
    let z := (e s).1.toAdd
    have hval : ¬ 2 ∣ z.val := by
      intro hd
      apply hq
      change q z = 0
      rw [← ZMod.natCast_zmod_val z, map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
    have hz : orderOf (e s).1 = 2 ^ n := by
      change addOrderOf z = 2 ^ n
      rw [← ZMod.natCast_zmod_val z, ZMod.addOrderOf_coe _ (by positivity)]
      rw [(Nat.prime_two.coprime_pow_of_not_dvd hval).symm.gcd_eq_one, Nat.div_one]
    have hdiv : orderOf (e s).2 ∣ 2 ^ n := by
      have hh := orderOf_dvd_natCard (x := (e s).2)
      simpa [Nat.card_eq_fintype_card] using hh
    rw [← e.orderOf_eq, Prod.orderOf, hz, Nat.lcm_eq_left hdiv]

variable {G : Type*} [Group G] [Finite G]

/-- The actual image of normalizer conjugation on the Sylow subgroup. -/
abbrev Automizer (S : Sylow 2 G) := (S : Subgroup G).normalizerMonoidHom.range

/-- Ambient conjugacy on the Sylow subgroup is exactly its actual automizer orbit. -/
theorem isConj_iff_automizer (S : Sylow 2 G) {n : ℕ}
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s t : S) : IsConj (s : G) (t : G) ↔
    ∃ a : Automizer S, (a.val : MulAut S) s = t := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have hy : g⁻¹⁻¹ * (s : G) * g⁻¹ ∈ S := by
      simpa only [inv_inv, hg] using t.property
    obtain ⟨u, hu, he⟩ := S.conj_eq_normalizer_conj_of_equiv_prod_zmod e s g⁻¹ s.property hy
    refine ⟨⟨(S : Subgroup G).normalizerMonoidHom
      ⟨u⁻¹, (Subgroup.normalizer (S : Set G)).inv_mem hu⟩,
      ⟨⟨u⁻¹, (Subgroup.normalizer (S : Set G)).inv_mem hu⟩, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change u⁻¹ * (s : G) * u⁻¹⁻¹ = (t : G)
    simpa only [inv_inv, hg] using he.symm
  · rintro ⟨a, ha⟩
    obtain ⟨u, hu⟩ := a.property
    apply isConj_iff.mpr
    refine ⟨(u : G), ?_⟩
    have hh := congrArg (fun z : S => (z : G)) ha
    change (((a.val : MulAut S) s : S) : G) = (t : G) at hh
    rw [← hu] at hh
    exact hh

/-- Every nonidentity member of the actual automizer fixes only one. -/
theorem automizer_fixed (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : Automizer S) (ha : a ≠ 1) (s : S) (hs : a.val s = s) : s = 1 := by
  exact S.normalizer_automorphism_fixed_point_eq_one_of_equiv_prod_zmod hn e
    a.val a.property (fun he => ha (Subtype.ext he)) s hs

/-- Ambient conjugacy sum, with each conjugate subgroup element counted once. -/
@[expose] def conjugacySum (S : Sylow 2 G) (η : ClassFunction S) : ClassFunction S :=
  fun s => ∑ t : S, if IsConj (s : G) (t : G) then η t else 0

/-- Evaluation of the actual automizer is injective away from the identity. -/
theorem automizer_eval_injective (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (s : S) (hs : s ≠ 1) : Function.Injective (fun a : Automizer S => a.val s) := by
  intro a b hab
  by_contra hne
  apply hs
  apply automizer_fixed S hn e (b⁻¹ * a) (fun he => hne (inv_mul_eq_one.mp he).symm)
  change (b.val : MulAut S).symm (a.val s) = s
  change a.val s = b.val s at hab
  rw [hab]
  exact (b.val : MulAut S).symm_apply_apply s

/-- Functions vanishing at one may be summed over the automizer without
stabilizer multiplicities, including at the identity itself. -/
theorem conjugacySum_eq_sum_automizer (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (η : ClassFunction S) (hη : η 1 = 0) (s : S) :
    conjugacySum S η s = ∑ a : Automizer S, η (a.val s) := by
  classical
  by_cases hs : s = 1
  · subst s
    simp only [conjugacySum, Subgroup.coe_one, map_one, hη, Finset.sum_const_zero]
    apply Finset.sum_eq_zero
    intro t _
    split_ifs with ht
    · have ht' : t = 1 := Subtype.ext (isConj_one_right.mp ht)
      simpa only [ht'] using hη
    · rfl
  · rw [conjugacySum, ← Finset.sum_filter]
    symm
    apply Finset.sum_bij (fun a _ => a.val s)
    · intro a _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isConj_iff_automizer S e s _).mpr ⟨a, rfl⟩⟩
    · intro a _ b _ hab
      exact automizer_eval_injective S hn e s hs hab
    · intro t ht
      obtain ⟨a, ha⟩ := (isConj_iff_automizer S e s t).mp (Finset.mem_filter.mp ht).2
      exact ⟨a, Finset.mem_univ _, ha⟩
    · intro a _
      rfl

/-- The ordinary Gram calculation for pairwise distinct normalizer orbits. -/
theorem conjugacySum_pairing (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (hc : Nat.card (Automizer S) = 3) {r : ℕ} (ψ : Fin r → S →* ℂ)
    (hne : ∀ j, ψ j ≠ 1)
    (hinj : Function.Injective (fun p : Fin r × Automizer S => (ψ p.1).comp p.2.val.toMonoidHom))
    (i j : Fin r) :
    scalarProduct S (conjugacySum S ((ψ j : S → ℂ) - 1)) ((ψ i : S → ℂ) - 1) =
      (3 : ℂ) + if i = j then 1 else 0 := by
  classical
  have hsum : conjugacySum S ((ψ j : S → ℂ) - 1) =
      fun s => ∑ a : Automizer S, ((ψ j).comp a.val.toMonoidHom s - 1) := by
    funext s
    exact conjugacySum_eq_sum_automizer S hn e _ (by simp) s
  rw [hsum, scalarProduct_sum_left]
  have hne' (a : Automizer S) : (ψ j).comp a.val.toMonoidHom ≠ 1 := by
    intro he
    apply hne j
    ext s
    have hh := DFunLike.congr_fun he (a.val.symm s)
    simpa using hh
  have heq (a : Automizer S) : (ψ j).comp a.val.toMonoidHom = ψ i ↔ i = j ∧ a = 1 := by
    constructor
    · intro h
      have h' : (ψ j).comp a.val.toMonoidHom = (ψ i).comp (1 : Automizer S).val.toMonoidHom := by
        exact h.trans (by ext s; rfl)
      have hh := hinj (a₁ := (j, a)) (a₂ := (i, 1)) h'
      exact ⟨(congrArg Prod.fst hh).symm, congrArg Prod.snd hh⟩
    · rintro ⟨rfl, rfl⟩
      ext s
      rfl
  have hv (a : Automizer S) :
      scalarProduct S (fun s => ((ψ j).comp a.val.toMonoidHom) s - 1) ((ψ i : S → ℂ) - 1) =
        1 + if i = j ∧ a = 1 then 1 else 0 := by
    have hh := scalarProduct_sub_one _ _ (hne' a) (hne i)
    simp only [heq] at hh
    convert hh using 1
    congr 1
  simp_rw [hv]
  rw [Finset.sum_add_distrib]
  have hc' : (Nat.card (Automizer S) : ℂ) = 3 := by exact_mod_cast hc
  have hsone : (∑ _a : Automizer S, (1 : ℂ)) = 3 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
    exact hc'
  rw [hsone]
  by_cases hij : i = j
  · simp only [hij, true_and, if_true, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [hij, false_and, if_false, Finset.sum_const_zero, add_zero]

/-- Ambient invariance and coverage by orbit representatives reduce all Fourier
coefficient conditions to the representative conditions. -/
theorem eq_neg_of_orbit_coefficients (S : Sylow 2 G) {n : ℕ}
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    {r : ℕ} (ψ : Fin r → S →* ℂ)
    (hcover : ∀ χ : S →* ℂ, χ ≠ 1 → ∃ (j : Fin r) (a : Automizer S),
      (ψ j).comp a.val.toMonoidHom = χ)
    (f : S → ℂ) (hf : ∀ s t : S, IsConj (s : G) (t : G) → f s = f t)
    (δ : ℂ) (hδ : ∀ j, scalarProduct S f ((ψ j : S → ℂ) - 1) = δ)
    (s : S) (hs : s ≠ 1) : f s = -δ := by
  let : IsMulCommutative S := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  apply AbelianLinearCharacters.eq_neg_of_coeff_sub_one f δ ?_ s hs
  intro χ hχ
  obtain ⟨j, a, rfl⟩ := hcover χ hχ
  have hfa (t : S) : f (a.val t) = f t :=
    (hf t (a.val t) ((isConj_iff_automizer S e t _).mpr ⟨a, rfl⟩)).symm
  have hh := scalarProduct_comp_of_invariant f ((ψ j : S → ℂ) - 1) a.val hfa
  convert hh.trans (hδ j) using 1
  congr 1
  exact Subsingleton.elim _ _

/-- The ordinary character witnesses for Brauer's homocyclic Sylow argument,
including the actual normalizer orbits and both Fourier identities. -/
structure OrbitSystem (S : Sylow 2 G) (n : ℕ) where
  r : ℕ
  five_le : 5 ≤ r
  card_eq : 3 * r + 1 = Nat.card S
  ψ : Fin r → ClassFunction S
  linear : ∀ j, IsLinearCharacter (ψ j)
  nonprincipal : ∀ j, ψ j ≠ 1
  orbit_unique : ∀ (i j : Fin r) (a b : Automizer S),
    (fun s => ψ i (a.val s)) = (fun s => ψ j (b.val s)) → i = j ∧ a = b
  orbit_cover : ∀ χ : ClassFunction S, IsLinearCharacter χ → χ ≠ 1 →
    ∃ (j : Fin r) (a : Automizer S), ∀ s, χ s = ψ j (a.val s)
  first_square_one : ∀ s, ψ ⟨0, by omega⟩ s ^ 2 = 1
  first_support_order : ∀ s, ψ ⟨0, by omega⟩ s ≠ 1 → orderOf s = 2 ^ n
  pairing : ∀ i j,
    scalarProduct S (conjugacySum S (ψ j - 1)) (ψ i - 1) =
      (3 : ℂ) + if i = j then 1 else 0
  constant_of_coefficients : ∀ (f : S → ℂ),
    (∀ s t : S, IsConj (s : G) (t : G) → f s = f t) → ∀ δ : ℂ,
    (∀ j, scalarProduct S f (ψ j - 1) = δ) → ∀ s : S, s ≠ 1 → f s = -δ

/-- Construct the complete ordinary orbit system from the homocyclic Sylow
coordinates and the noncentralizing normalizer, with no character packet input. -/
theorem exists_orbitSystem (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (h : ¬ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) :
    Nonempty (OrbitSystem S n) := by
  let : IsMulCommutative S := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  obtain ⟨χ₀, hχ₀, hsq, hsupp⟩ := exists_order_two_character (by omega : 1 ≤ n) e
  obtain ⟨r, hr, ψ, hfirst, hne, hinj, hcover, hc⟩ :=
    exists_pointed_orbit_representatives (Automizer S)
      (fun a ha s hs => automizer_fixed S hn e a ha s hs) χ₀ hχ₀
  have hK : Nat.card (Automizer S) = 3 :=
    S.card_normalizer_action_eq_three_of_equiv_prod_zmod hn e h
  rw [hK] at hc
  have hS : 16 ≤ Nat.card S := by
    have hpow : 4 ≤ 2 ^ n := by
      have hh := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn
      norm_num at hh ⊢
      exact hh
    rw [Nat.card_congr e.toEquiv]
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_multiplicative,
      ZMod.card]
    nlinarith
  have hr5 : 5 ≤ r := by omega
  refine ⟨{
    r := r
    five_le := hr5
    card_eq := by omega
    ψ := fun j => (ψ j : S → ℂ)
    linear := fun j => (ψ j).isLinearCharacter
    nonprincipal := fun j hh => hne j (DFunLike.coe_injective hh)
    orbit_unique := ?_
    orbit_cover := ?_
    first_square_one := ?_
    first_support_order := ?_
    pairing := ?_
    constant_of_coefficients := ?_ }⟩
  · intro i j a b hab
    have hh := hinj (a₁ := (i, a)) (a₂ := (j, b)) (DFunLike.ext _ _ (congrFun hab))
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  · intro χ hχ hχne
    have hχ' : hχ.toMonoidHom ≠ 1 := by
      intro he
      exact hχne (congrArg DFunLike.coe he)
    obtain ⟨j, a, ha⟩ := hcover hχ.toMonoidHom hχ'
    exact ⟨j, a, fun s => (DFunLike.congr_fun ha s).symm⟩
  · intro s
    rw [hfirst]
    exact hsq s
  · intro s hs
    rw [hfirst] at hs
    exact hsupp s hs
  · exact conjugacySum_pairing S hn e hK ψ hne hinj
  · exact eq_neg_of_orbit_coefficients S e ψ hcover

/-- The first representative has order exactly two as a pointwise function. -/
theorem OrbitSystem.first_orderOf {S : Sylow 2 G} {n : ℕ} (D : OrbitSystem S n) :
    orderOf (D.ψ ⟨0, by have := D.five_le; omega⟩) = 2 := by
  apply orderOf_eq_prime
  · funext s
    exact D.first_square_one s
  · exact D.nonprincipal _

end HomocyclicSylowLinearCharacters
