module

public import Theory.Representation.PSL3Two.ParabolicCyclic.Basic

/-!
# The two-dimensional parabolic seed and its cyclic quotient

The line parabolic has three Borel cosets. Its order-three coset representative
therefore moves a Borel-fixed generator whose parabolic orbit spans a plane.
The three translates are distinct nonzero vectors of that binary plane, so their
sum vanishes. An intertwiner sending the generator to a vector fixed by this
three-cycle must send it to zero. This excludes both trivial and dual-natural
quotients, since every Borel-fixed covector is fixed by the three-cycle.

Together with the flag orbit map and the corrected simple-head reduction this
constructs a surjection from the point core plus the Steinberg module, with no
extra finite-dimensionality, irreducibility, or quotient-exclusion assumptions.
This proves the quotient assertion of Aschbacher–Smith H.6.5, printed p.388 of
the 1 March 2004 manuscript. The five isomorphism alternatives require the
separate classification of nonzero quotients of that direct sum. The seed
relation also supplies the local relation for H.5.5, printed p.386.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Representation Matrix
namespace BinaryLinearThree.ParabolicCyclic
open FanoDecomposition
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- The line-parabolic orbit of a Borel-fixed vector consists of three possible translates. -/
theorem line_orbit_of_fixed (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (g : Group) (hg : g ∈ Matrix.PSL3Two.lineParabolicSL) :
    ∃ i : Fin 3, ρ g m = ρ (lineCycle ^ (i : ℕ)) m := by
  obtain ⟨i, hi⟩ := line_cosets g hg
  refine ⟨i, ?_⟩
  have he := congrArg (ρ (lineCycle ^ (i : ℕ))) (hfixed _ hi)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using he

/-- A two-dimensional parabolic orbit span excludes a fixed point for the three-cycle. -/
theorem lineCycle_moves_seed (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2) :
    ρ lineCycle m ≠ m := by
  classical
  intro he
  have hpow (n : ℕ) : ρ (lineCycle ^ n) m = m := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, he, ih]
  have hle : orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m ≤ Submodule.span (ZMod 2) {m} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi⟩ := line_orbit_of_fixed ρ m hfixed g hg
    rw [hi, hpow]
    exact Submodule.subset_span (Set.mem_singleton m)
  have hb := Submodule.finrank_mono hle
  have hc := finrank_span_finset_le_card (R := ZMod 2) ({m} : Finset M)
  simp only [Finset.coe_singleton, Finset.card_singleton] at hc
  change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {m}) ≤ 1 at hc
  omega

private theorem binary_plane_sum : ∀ a b c : Fin 2 → ZMod 2,
    a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c → a + b + c = 0 := by
  decide +kernel

/-- The three translates of the seed are the three nonzero vectors of its binary plane. -/
theorem seed_relation (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2) :
    m + ρ lineCycle m + ρ (lineCycle ^ 2) m = 0 := by
  let D := orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m
  have : FiniteDimensional (ZMod 2) D := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m)
    omega)
  let e := (Module.finBasisOfFinrankEq (ZMod 2) D hdim).equivFun
  let a : D := ⟨m, mem_orbitSpan ρ _ m⟩
  let b : D := ⟨ρ lineCycle m, orbit_mem ρ _ m _ lineCycle_mem⟩
  let c : D := ⟨ρ (lineCycle ^ 2) m, orbit_mem ρ _ m _
    (Matrix.PSL3Two.lineParabolicSL.pow_mem lineCycle_mem 2)⟩
  have hab := lineCycle_moves_seed ρ m hfixed hdim
  have hzero : m ≠ 0 := by intro hm; exact hab (by simp [hm])
  have h2 : ρ (lineCycle ^ 2) m ≠ m := by
    intro he
    have he' := congrArg (ρ lineCycle) he
    have hc : lineCycle * lineCycle ^ 2 = 1 := by
      simpa only [pow_succ', pow_zero, mul_one] using lineCycle_cube
    rw [← Module.End.mul_apply, ← map_mul, hc, map_one, Module.End.one_apply] at he'
    exact hab he'.symm
  have h12 : ρ lineCycle m ≠ ρ (lineCycle ^ 2) m := by
    intro he
    apply hab
    apply (ρ.apply_bijective lineCycle).1
    simpa only [pow_two, map_mul, Module.End.mul_apply] using he.symm
  have hn (g : Group) : ρ g m ≠ 0 := by
    intro he
    apply hzero
    exact (ρ.apply_bijective g).1 (he.trans (map_zero (ρ g)).symm)
  have hz := binary_plane_sum (e a) (e b) (e c)
    (fun he => hzero (congrArg Subtype.val (e.injective (he.trans (map_zero e).symm))))
    (fun he => hn lineCycle (congrArg Subtype.val (e.injective (he.trans (map_zero e).symm))))
    (fun he => hn (lineCycle ^ 2) (congrArg Subtype.val (e.injective (he.trans (map_zero e).symm))))
    (fun he => hab (congrArg Subtype.val (e.injective he)).symm)
    (fun he => h2 (congrArg Subtype.val (e.injective he)).symm)
    (fun he => h12 (congrArg Subtype.val (e.injective he)))
  have he : a + b + c = 0 := e.injective (by simpa only [map_add, map_zero] using hz)
  exact congrArg Subtype.val he


/-- Every Borel-fixed covector is also fixed by the marked line three-cycle. -/
theorem borel_fixed_dual_cycle_fixed (φ : Dual)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, W.dual g φ = φ) :
    W.dual lineCycle φ = φ := by
  let g₁ := Matrix.PSL3Two.Bruhat.upper 1
  let g₂ := Matrix.PSL3Two.Bruhat.upper 4
  have hi₁ : g₁⁻¹ = g₁ := inv_eq_of_mul_eq_one_right (by decide)
  have hi₂ : g₂⁻¹ = g₂ := inv_eq_of_mul_eq_one_right (by decide)
  have h₁ := congrArg (fun ψ : Dual => ψ (Pi.single 1 1))
    (hfixed g₁ (Matrix.PSL3Two.Bruhat.upper_mem 1))
  have h₂ := congrArg (fun ψ : Dual => ψ (Pi.single 2 1))
    (hfixed g₂ (Matrix.PSL3Two.Bruhat.upper_mem 4))
  change φ (W g₁⁻¹ (Pi.single 1 1)) = φ (Pi.single 1 1) at h₁
  change φ (W g₂⁻¹ (Pi.single 2 1)) = φ (Pi.single 2 1) at h₂
  rw [hi₁, show W g₁ (Pi.single 1 1) = Pi.single 0 1 + Pi.single 1 1 by decide,
    map_add] at h₁
  rw [hi₂, show W g₂ (Pi.single 2 1) = Pi.single 1 1 + Pi.single 2 1 by decide,
    map_add] at h₂
  have h0 : φ (Pi.single 0 1) = 0 := add_eq_right.mp h₁
  have h1 : φ (Pi.single 1 1) = 0 := add_eq_right.mp h₂
  have hi : lineCycle⁻¹ = lineCycle ^ 2 := by decide
  apply (Pi.basisFun (ZMod 2) (Fin 3)).ext
  intro i
  simp only [Pi.basisFun_apply]
  change φ (W lineCycle⁻¹ (Pi.single i 1)) = φ (Pi.single i 1)
  rw [hi]
  fin_cases i
  · change φ (W (lineCycle ^ 2) (Pi.single (0 : Fin 3) 1)) = φ (Pi.single 0 1)
    rw [show W (lineCycle ^ 2) (Pi.single 0 1) = Pi.single 0 1 + Pi.single 1 1 by decide,
      map_add, h0, h1, add_zero]
  · change φ (W (lineCycle ^ 2) (Pi.single (1 : Fin 3) 1)) = φ (Pi.single 1 1)
    rw [show W (lineCycle ^ 2) (Pi.single 1 1) = Pi.single 0 1 by decide, h0, h1]
  · exact congrArg φ (by decide : W (lineCycle ^ 2) (Pi.single (2 : Fin 3) 1) = Pi.single 2 1)

/-- The seed relation forces a cycle-fixed image of the generator to vanish. -/
theorem seed_image_eq_zero_of_cycle_fixed
    {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    {ρ : Representation (ZMod 2) Group M} {σ : Representation (ZMod 2) Group N}
    (m : M) (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2)
    (f : ρ.IntertwiningMap σ) (hf : σ lineCycle (f m) = f m) : f m = 0 := by
  have he := congrArg f (seed_relation ρ m hfixed hdim)
  rw [map_add, map_add, map_zero, f.isIntertwining, f.isIntertwining] at he
  rw [pow_two, map_mul, Module.End.mul_apply, hf, hf, ZModModule.add_self, zero_add] at he
  exact he

/-- The cyclic module generated by the parabolic seed has no trivial quotient. -/
theorem no_trivial_quotient (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2)
    (f : ρ.IntertwiningMap FanoQuotients.trivialRepresentation) : ¬ Function.Surjective f := by
  have hz : f = 0 := intertwiner_eq_zero_of_cyclic m hgen f
    (seed_image_eq_zero_of_cycle_fixed m hfixed hdim f rfl)
  intro hf
  obtain ⟨v, hv⟩ := hf 1
  simp [hz] at hv

/-- The cyclic module generated by the parabolic seed has no dual-natural quotient. -/
theorem no_dual_quotient (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2)
    (f : ρ.IntertwiningMap W.dual) : ¬ Function.Surjective f := by
  have hz : f = 0 := intertwiner_eq_zero_of_cyclic m hgen f
    (seed_image_eq_zero_of_cycle_fixed m hfixed hdim f (borel_fixed_dual_cycle_fixed (f m) (by
      intro g hg
      rw [← f.isIntertwining, hfixed g hg])))
  intro hf
  obtain ⟨v, hv⟩ := hf (LinearMap.proj 0)
  have he := congrArg (fun φ : Dual => φ (Pi.single 0 1)) hv
  simp [hz] at he

/-- The quotient assertion of H.6.5, from the actual source seed hypotheses. -/
theorem quotient_of_parabolic_seed (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2) :
    ∃ f : (U₂.prod S).IntertwiningMap ρ, Function.Surjective f := by
  have : FiniteDimensional (ZMod 2) M := finiteDimensional_of_cyclic ρ m hgen
  obtain ⟨q, hq, _⟩ := flag_quotient ρ m hfixed hgen
  exact FanoQuotients.quotient_of_flags ρ q hq
    (no_trivial_quotient ρ m hfixed hgen hdim) (no_dual_quotient ρ m hfixed hgen hdim)

end BinaryLinearThree.ParabolicCyclic
