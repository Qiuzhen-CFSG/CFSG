module

public import Theory.GroupTheory.SymmetricFourCoxeterRecognition

/-!
# Recognizing S₄ from equivariant involution lifts

Suppose six involutions map to the six transpositions of S₄ and their
conjugation is determined by this permutation image. The three adjacent
lifts satisfy the A₃ Coxeter relations. They generate all six lifts by
conjugation, hence generate the whole source group and identify it with S₄.

This is the small quotient argument used for the radius-four label group
in Goldschmidt (1980), (6.12.6).
-/

@[expose] public section
namespace Theory.GroupTheory.SymmetricFourCoxeterRecognition
open Subgroup

abbrev Transposition := {σ : Equiv.Perm (Fin 4) // σ.IsSwap}

private def reflection (i : Fin 3) : Transposition :=
  ⟨Equiv.swap i.castSucc i.succ, ⟨i.castSucc, i.succ, by fin_cases i <;> decide, rfl⟩⟩

theorem conjugate_isSwap (g : Equiv.Perm (Fin 4)) (x : Transposition) :
    (g * x.val * g⁻¹).IsSwap := by
  rcases x with ⟨x, a, b, hab, rfl⟩
  change (g * Equiv.swap a b * g⁻¹).IsSwap
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]
  exact ⟨g a, g b, g.injective.ne hab, rfl⟩

/-- The conjugation action of S₄ on its six transpositions. -/
def conjugateTransposition (g : Equiv.Perm (Fin 4)) (x : Transposition) : Transposition :=
  ⟨g * x.val * g⁻¹, conjugate_isSwap g x⟩

variable {G : Type*} [Group G]

/-- Recognition from the literal equivariant six-element reflection family.
The specified homomorphism is retained in the conclusion. -/
theorem bijective_of_equivariant_transposition_lifts
    (f : G →* Equiv.Perm (Fin 4)) (t : Transposition → G)
    (htwo : ∀ x, t x ^ 2 = 1) (hmap : ∀ x, f (t x) = x.val)
    (hconj : ∀ (g : G) (x : Transposition),
      g * t x * g⁻¹ = t (conjugateTransposition (f g) x))
    (hgen : closure (Set.range t) = ⊤) : Function.Bijective f := by
  let a := t (reflection 0)
  let b := t (reflection 1)
  let c := t (reflection 2)
  have ha : a ^ 2 = 1 := htwo _
  have hb : b ^ 2 = 1 := htwo _
  have hc : c ^ 2 = 1 := htwo _
  have hfa : f a = Equiv.swap 0 1 := hmap _
  have hfb : f b = Equiv.swap 1 2 := hmap _
  have hfc : f c = Equiv.swap 2 3 := hmap _
  have hinv (x : Transposition) : (t x)⁻¹ = t x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using htwo x)
  have braid (i j : Fin 3)
      (he : conjugateTransposition (reflection i).val (reflection j) =
        conjugateTransposition (reflection j).val (reflection i)) :
      (t (reflection i) * t (reflection j)) ^ 3 = 1 := by
    have hij := hconj (t (reflection i)) (reflection j)
    have hji := hconj (t (reflection j)) (reflection i)
    rw [hmap, hinv] at hij hji
    have hbraid : t (reflection i) * t (reflection j) * t (reflection i) =
        t (reflection j) * t (reflection i) * t (reflection j) := by
      rw [hij, he, hji]
    have hi : t (reflection i) * t (reflection i) = 1 := by
      simpa only [pow_two] using htwo (reflection i)
    have hj : t (reflection j) * t (reflection j) = 1 := by
      simpa only [pow_two] using htwo (reflection j)
    calc
      (t (reflection i) * t (reflection j)) ^ 3 =
          (t (reflection i) * t (reflection j) * t (reflection i)) *
            (t (reflection j) * t (reflection i) * t (reflection j)) := by
              simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = (t (reflection j) * t (reflection i) * t (reflection j)) *
            (t (reflection j) * t (reflection i) * t (reflection j)) := by rw [hbraid]
      _ = 1 := by
        calc
          _ = t (reflection j) * t (reflection i) *
              (t (reflection j) * t (reflection j)) * t (reflection i) *
                t (reflection j) := by group
          _ = 1 := by rw [hj, mul_one, mul_assoc (t (reflection j)), hi, mul_one, hj]
  have hab : (a * b) ^ 3 = 1 := braid 0 1 (by apply Subtype.ext; decide +kernel)
  have hbc : (b * c) ^ 3 = 1 := braid 1 2 (by apply Subtype.ext; decide +kernel)
  have hac : Commute a c := by
    have hh := hconj a (reflection 2)
    rw [hfa] at hh
    have he : conjugateTransposition (Equiv.swap 0 1) (reflection 2) = reflection 2 := by
      apply Subtype.ext
      decide +kernel
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  let H := closure ({a,b,c} : Set G)
  have haH : a ∈ H := subset_closure (by simp)
  have hbH : b ∈ H := subset_closure (by simp)
  have hcH : c ∈ H := subset_closure (by simp)
  have hsurj : H.map f = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.closure_isSwap]
    apply (closure_le _).mpr
    intro σ hσ
    have hswap : ∀ i : Fin 3, Equiv.swap i.castSucc i.succ ∈ H.map f := by
      intro i
      fin_cases i
      · exact hfa ▸ mem_map_of_mem f haH
      · exact hfb ▸ mem_map_of_mem f hbH
      · exact hfc ▸ mem_map_of_mem f hcH
    have hh : (⊤ : Submonoid (Equiv.Perm (Fin 4))) ≤ (H.map f).toSubmonoid := by
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ 3]
      exact Submonoid.closure_le.mpr (by rintro _ ⟨i, rfl⟩; exact hswap i)
    exact hh (mem_top σ)
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    rintro _ ⟨σ, rfl⟩
    obtain ⟨i, j, hij, hσ⟩ := σ.property
    obtain ⟨p, hp⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (by decide : (0 : Fin 4) ≠ 1) hij)
    have hpm : p ∈ H.map f := hsurj ▸ mem_top p
    obtain ⟨g, hg, hgp⟩ := hpm
    have he : conjugateTransposition (f g) (reflection 0) = σ := by
      apply Subtype.ext
      change f g * Equiv.swap 0 1 * (f g)⁻¹ = σ.val
      rw [hgp, hp, hσ]
    rw [← he, ← hconj]
    exact H.mul_mem (H.mul_mem hg haH) (H.inv_mem hg)
  have hne : a ≠ c := by
    intro he
    have hh := congrArg f he
    rw [hfa, hfc] at hh
    exact (by decide : Equiv.swap (0 : Fin 4) 1 ≠ Equiv.swap 2 3) hh
  obtain ⟨e, hea, heb, hec⟩ := exists_marked_equiv a b c ha hb hc hab hbc hac hH hne
  have hfe : f = e.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense (s := ({a,b,c} : Set G)) hH
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact hfa.trans hea.symm
    · exact hfb.trans heb.symm
    · exact hfc.trans hec.symm
  rw [hfe]
  exact ⟨fun _ _ h => e.injective h, fun y => e.surjective y⟩

/-- Six involutions forming a conjugation-invariant family and mapping onto
transpositions already give the same recognition. Their indexing need not
be chosen in advance to match the standard transposition coordinates. -/
theorem bijective_of_six_conjugate_lifts
    {I : Type*} [Finite I] [Nonempty I] (hI : Nat.card I ≤ 6)
    (f : G →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (t : I → G) (htwo : ∀ i, t i ^ 2 = 1) (hswap : ∀ i, (f (t i)).IsSwap)
    (hstable : ∀ (g : G) i, ∃ j, g * t i * g⁻¹ = t j)
    (hgen : closure (Set.range t) = ⊤) : Function.Bijective f := by
  classical
  let m : I → Transposition := fun i => ⟨f (t i), hswap i⟩
  have hm : Function.Surjective m := by
    intro σ
    let i : I := Classical.arbitrary I
    obtain ⟨a, b, hab, ht⟩ := hswap i
    obtain ⟨c, d, hcd, hσ⟩ := σ.property
    obtain ⟨p, hp⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hcd)
    obtain ⟨g, hg⟩ := hf p
    obtain ⟨j, hj⟩ := hstable g i
    refine ⟨j, Subtype.ext ?_⟩
    change f (t j) = σ.val
    rw [← hj, map_mul, map_mul, map_inv, hg, ht, hp, ← hσ]
  have hcard : Nat.card Transposition = 6 := by
    let : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
    let : DecidablePred (fun σ : Equiv.Perm (Fin 4) => σ.IsSwap) := fun σ =>
      inferInstanceAs (Decidable (∃ a b : Fin 4, a ≠ b ∧ σ = Equiv.swap a b))
    let : Fintype Transposition := Subtype.fintype _
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hb : Function.Bijective m := hm.bijective_of_nat_card_le (hI.trans_eq hcard.symm)
  let e : I ≃ Transposition := Equiv.ofBijective m hb
  let u : Transposition → G := fun σ => t (e.symm σ)
  apply bijective_of_equivariant_transposition_lifts f u
  · exact fun σ => htwo _
  · intro σ
    exact congrArg Subtype.val (e.apply_symm_apply σ)
  · intro g σ
    obtain ⟨j, hj⟩ := hstable g (e.symm σ)
    have he : e j = conjugateTransposition (f g) σ := by
      apply Subtype.ext
      change f (t j) = f g * σ.val * (f g)⁻¹
      rw [← hj, map_mul, map_mul, map_inv]
      exact congrArg (fun q => f g * q * (f g)⁻¹)
        (congrArg Subtype.val (e.apply_symm_apply σ))
    change g * t (e.symm σ) * g⁻¹ = t (e.symm _)
    rw [hj, ← he, e.symm_apply_apply]
  · have hrange : Set.range u = Set.range t := by
      ext x
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨e.symm σ, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp only [u, e.symm_apply_apply]⟩
    rw [hrange, hgen]

/-- The literal six order-two subgroups suffice: their unique nonidentity
elements supply the equivariant transposition lifts. -/
theorem bijective_of_six_conjugate_subgroups
    {I : Type*} [Finite I] [Nonempty I] (hI : Nat.card I ≤ 6)
    (f : G →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (P : I → Subgroup G) (hcard : ∀ i, Nat.card (P i) = 2)
    (hswap : ∀ i, ∃ u : G, u ∈ P i ∧ (f u).IsSwap)
    (hstable : ∀ (g : G) i, ∃ j, (P i).map (MulAut.conj g).toMonoidHom = P j)
    (hgen : (⨆ i, P i) = ⊤) : Function.Bijective f := by
  classical
  choose t ht hs using hswap
  have hne (i : I) : t i ≠ 1 := by
    intro he
    have hh := (hs i).sign_eq
    rw [he, map_one, map_one] at hh
    exact (by decide : (1 : ℤˣ) ≠ -1) hh
  have huniq (i : I) {u : G} (hu : u ∈ P i) (hne' : u ≠ 1) : u = t i := by
    obtain ⟨v, hv, hunique⟩ := (Nat.card_eq_two_iff' (1 : P i)).mp (hcard i)
    have hu' : (⟨u, hu⟩ : P i) ≠ 1 := fun he => hne' (congrArg Subtype.val he)
    have ht' : (⟨t i, ht i⟩ : P i) ≠ 1 := fun he => hne i (congrArg Subtype.val he)
    exact congrArg Subtype.val ((hunique _ hu').trans (hunique _ ht').symm)
  apply bijective_of_six_conjugate_lifts hI f hf t
  · intro i
    have hh := pow_card_eq_one' (x := (⟨t i, ht i⟩ : P i))
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  · exact hs
  · intro g i
    obtain ⟨j, hj⟩ := hstable g i
    refine ⟨j, huniq j ?_ ?_⟩
    · rw [← hj]
      exact mem_map_of_mem _ (ht i)
    · intro he
      apply hne i
      have hh := congrArg (fun x => g⁻¹ * x * g) he
      simpa only [mul_assoc, inv_mul_cancel_left, one_mul, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hh
  · apply le_antisymm le_top
    rw [← hgen]
    apply iSup_le
    intro i u hu
    by_cases he : u = 1
    · exact he ▸ one_mem _
    · rw [huniq i hu he]
      exact subset_closure ⟨i, rfl⟩

end Theory.GroupTheory.SymmetricFourCoxeterRecognition
