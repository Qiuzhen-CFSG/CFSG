module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers.DoubleFlip
public import Theory.GroupTheory.CentralExtensionInvertedRankThree

/-!
# Transporting the squared orthogonal torus and its partial inverters

The three prime-order parameter axes are sent to their literal squared
diagonals. For two different axes, choose the unused third coordinate and
flip the first and third pairs. This inverts the first axis and commutes
with the second. An injective map from the split carrier transports these
identities while the torus remains inside the original root normalizer.

A prime dividing `|F|-1` is odd when the field has characteristic two.
The global partial-inverter lifting theorem then excludes every finite
central cover, with no restriction on its central kernel. The two membership
hypotheses are discharged for the actual plus and minus carriers in the
parent extension. Source: Aschbacher--Smith A.2.18, printed p.40.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers
variable {F : Type*} [Field F] [CharP F 2] {r : ℕ}

open CentralExtension.SwappedRankThree (basis)

omit [CharP F 2] in
/-- A single parameter occupies its literal hyperbolic coordinate. -/
theorem torusEntries_single (hr : 3 ≤ r) (C : Subgroup Fˣ) (i : Fin 3) (t : C) :
    torusEntriesHom (r := r) C (Pi.mulSingle i t) =
      Pi.mulSingle (Fin.castLE hr i) t.val := by
  funext k
  by_cases hk : k = Fin.castLE hr i
  · subst k
    simp [torusEntriesHom, i.isLt]
  · by_cases h : k.val < 3
    · have hi : (⟨k.val, h⟩ : Fin 3) ≠ i := by
        intro he
        apply hk
        exact Fin.ext (congrArg (fun z : Fin 3 => z.val) he)
      simp [torusEntriesHom, h, hi, hk]
    · simp [torusEntriesHom, h, hk]

omit [CharP F 2] in
/-- The cyclic marking preserves the single-coordinate axes. -/
theorem marked_entries (hr : 3 ≤ r) {p : ℕ} (C : Subgroup Fˣ)
    (ρ : Multiplicative (ZMod p) ≃* C) (i : Fin 3) :
    torusEntriesHom (r := r) C
      ((MulEquiv.piCongrRight (fun _ : Fin 3 => ρ)) (basis p i)) =
        Pi.mulSingle (Fin.castLE hr i) (ρ (Multiplicative.ofAdd 1)).val := by
  have he : (MulEquiv.piCongrRight (fun _ : Fin 3 => ρ)) (basis p i) =
      Pi.mulSingle i (ρ (Multiplicative.ofAdd 1)) := by
    funext j
    change ρ (basis p i j) = (Pi.mulSingle i (ρ (Multiplicative.ofAdd 1)) : Fin 3 → C) j
    by_cases h : j = i
    · subst j
      simp [basis]
    · simp [basis, h]
  rw [he, torusEntries_single hr]

omit [CharP F 2] in
/-- Prime roots of unity are marked by the additive prime field. -/
theorem roots_marking [Finite F] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card F - 1) :
    Nonempty (Multiplicative (ZMod p) ≃* rootsOfUnity p F) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hdu : p ∣ Nat.card Fˣ := by simpa only [Nat.card_units] using hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hprim : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hprim.card_rootsOfUnity'
  exact ⟨mulEquivOfPrimeCardEq (by simp) hc⟩

theorem exists_third (i j : Fin 3) : ∃ k : Fin 3, i ≠ k ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

section Transport
variable {G : Type*} [Group G]
variable (S : Subgroup (O r F)) (π : S →* G) {u v : Fin r} (huv : u ≠ v)
variable (hroot : ∀ a : F, root huv a ∈ S)
variable (hdiag : ∀ d : Fin r → Fˣ, diagonal (d ^ 2) ∈ S)
variable (hflip : ∀ i k : Fin r, i ≠ k → flipOne (F := F) i * flipOne k ∈ S)

include hdiag hflip in
/-- The original local torus has actual global partial inverters. -/
theorem torus_partial_inverters (hr : 3 ≤ r) (hπ : Function.Injective π) {p : ℕ}
    (C : Subgroup Fˣ) (ρ : Multiplicative (ZMod p) ≃* C) :
    ∃ e : (Fin 3 → Multiplicative (ZMod p)) →* liftedRootNormalizer S π huv hroot,
      Function.Injective e ∧ ∀ i j : Fin 3, i ≠ j → ∃ g : G,
        g * (e (basis p i) : G) * g⁻¹ = (e (basis p i) : G)⁻¹ ∧
          Commute g (e (basis p j) : G) := by
  let η := MulEquiv.piCongrRight (fun _ : Fin 3 => ρ)
  let e := (torusNormalizerHom S π huv hroot hdiag C).comp η.toMonoidHom
  let A (i : Fin 3) : S := squareDiagonalHom S hdiag
    (Pi.mulSingle (Fin.castLE hr i) (ρ (Multiplicative.ofAdd 1)).val)
  have he (i : Fin 3) : (e (basis p i) : G) = π (A i) := by
    change π (squareDiagonalHom S hdiag
      (torusEntriesHom C (η (basis p i)))) = π (A i)
    rw [marked_entries hr C ρ]
  have ha (i : Fin 3) : (A i : O r F) =
      diagonal (Pi.mulSingle (Fin.castLE hr i) ((ρ (Multiplicative.ofAdd 1)).val ^ 2)) := by
    change diagonal ((Pi.mulSingle _ _) ^ 2) = _
    rw [← Pi.mulSingle_pow]
  refine ⟨e, (torusNormalizerHom_injective S π huv hroot hdiag hr hπ C).comp η.injective, ?_⟩
  intro i j hij
  obtain ⟨k, hik, hkj⟩ := exists_third i j
  have hc {a b : Fin 3} (hab : a ≠ b) : Fin.castLE hr a ≠ Fin.castLE hr b := by
    intro h
    apply hab
    exact Fin.ext (congrArg (fun z : Fin r => z.val) h)
  let g : S := ⟨flipOne (Fin.castLE hr i) * flipOne (Fin.castLE hr k), hflip _ _ (hc hik)⟩
  refine ⟨π g, ?_, ?_⟩
  · rw [he i]
    have hinv : g * A i * g⁻¹ = (A i)⁻¹ := by
      apply Subtype.ext
      change (g : O r F) * (A i : O r F) * (g : O r F)⁻¹ = (A i : O r F)⁻¹
      rw [ha]
      exact DoubleFlip.doubleFlip_inverts (hc hik) _
    simpa only [map_mul, map_inv] using congrArg π hinv
  · rw [he j]
    have hcomm : Commute g (A j) := by
      apply Commute.of_map S.subtype_injective
      change Commute (g : O r F) (A j : O r F)
      rw [ha]
      exact DoubleFlip.doubleFlip_commutes (hc hij) (hc hkj) _
    exact hcomm.map π

include huv hroot hdiag hflip in
/-- Double flips in the split carrier give the actual central-cover obstruction. -/
theorem not_quasithin_of_doubleFlips [Finite F] {E : Type*} [Group E] [Finite E]
    (hr : 3 ≤ r) (hπ : Function.Injective π) (hq : 2 < Nat.card F)
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ¬ IsQuasithin E := by
  obtain ⟨p, hp, ho, hd⟩ := exists_odd_prime_dvd_card_sub_one hq
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ⟩ := roots_marking hp hd
  obtain ⟨e, he, hs⟩ := torus_partial_inverters S π huv hroot hdiag hflip hr hπ _ ρ
  exact CentralExtension.InvertedRankThree.not_quasithin f hf hk ho _
    (liftedRootNormalizer_isTwoLocal S π huv hroot hπ) e he hs

end Transport

end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers
