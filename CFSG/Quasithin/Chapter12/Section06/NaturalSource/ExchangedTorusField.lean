module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.BinaryBorel.Actions
public import Theory.SpecificGroups.SL2.SylowNormalizerCubicAction
public import Theory.GroupTheory.AutomorphismSquareRank
/-!
# Field restriction for the actual binary product Borel

A product automorphism preserves or exchanges the two simple factors.
In the preserving case the marked normalizer characters identify the
induced quotient actions with field automorphisms. Cubic displacement is
therefore trivial above field order four. In the exchanging case it would
force every element of a cyclic torus of order 2ⁿ − 1 to have cube one,
which already excludes n > 2.

Both cases retain the chosen product Sylow and its actual normalizer.
The original 12.6.31 application is in AbelianExchangedField; no action
marking or field restriction is added to the source hypotheses.
Source: Aschbacher--Smith, printed pp.836--837, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06.ExchangedField
open Chapter13.Section08.Components.Swapped.LinearTwo
variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem sylow_map_of_borel_map (S : Sylow 2 Q) (a : MulAut Q)
    (hB : (BinaryBorel.borel S).map a.toMonoidHom = BinaryBorel.borel S) :
    (S : Subgroup Q).map a.toMonoidHom = S := by
  let b : MulAut (BinaryBorel.borel S) :=
    (a.subgroupMap _).trans (MulEquiv.subgroupCongr hB)
  have he : a.toMonoidHom.comp (BinaryBorel.borel S).subtype =
      (BinaryBorel.borel S).subtype.comp b.toMonoidHom := rfl
  rw [←BinaryBorel.ambient_twoCore S,Subgroup.map_map,he,←Subgroup.map_map,
    pCore_map_iso]

private theorem factor_displacement (S : Sylow 2 Q) (a : MulAut Q)
    {n : ℕ} (hn : 2 < n) (hm : ClassicalGroup.IsPSL Q 2 (2^n))
    (hb : ∀ x ∈ BinaryBorel.borel S, a x ∈ BinaryBorel.borel S)
    (hc : ∀ x ∈ BinaryBorel.borel S, (a x * x⁻¹)^3 ∈ (S : Subgroup Q)) :
    ∀ x ∈ BinaryBorel.borel S, a x * x⁻¹ ∈ (S : Subgroup Q) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hB : (BinaryBorel.borel S).map a.toMonoidHom = BinaryBorel.borel S := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      exact hb x hx
    · exact (card_map_of_injective a.injective).ge
  exact Matrix.SpecialLinearGroup.sylowNormalizer_displacement_mem_of_cube
    (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm) S a
    (sylow_map_of_borel_map S a hB)
    (by rw [hF]; exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn) hc

/-- In a larger binary field, cubic displacement on a product Borel is
trivial modulo its actual Sylow subgroup. Both factor and exchange cases
are derived from the ambient automorphism. -/
theorem binary_displacement [IsQuasisimple Q]
    {n : ℕ} (hn : 2 < n) (hm : ClassicalGroup.IsPSL Q 2 (2^n))
    (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (hb : ∀ x ∈ BinaryBorel.borel S, a x ∈ BinaryBorel.borel S)
    (hc : ∀ x ∈ BinaryBorel.borel S, (a x * x⁻¹)^3 ∈ (S : Subgroup (Q × Q))) :
    ∀ x ∈ BinaryBorel.borel S, a x * x⁻¹ ∈ (S : Subgroup (Q × Q)) := by
  have hZ : center Q = ⊥ := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    have h : e x ∈ center (PSL(2,F)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot,mem_bot] using h
  rcases AutomorphismSquare.normal_form hZ a with ⟨a₁,a₂,rfl⟩ | ⟨a₁,a₂,rfl⟩
  · have h₁ := factor_displacement (BinaryBorel.firstSylow S) a₁ hn hm
      (fun x hx => by
        have h := hb (x,1) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨hx,one_mem _⟩)
        rw [BinaryBorel.borel_eq_prod] at h
        exact h.1)
      (fun x hx => by
        have h := hc (x,1) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨hx,one_mem _⟩)
        rw [BinaryBorel.sylow_eq_prod] at h
        exact h.1)
    have h₂ := factor_displacement (BinaryBorel.secondSylow S) a₂ hn hm
      (fun x hx => by
        have h := hb (1,x) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨one_mem _,hx⟩)
        rw [BinaryBorel.borel_eq_prod] at h
        exact h.2)
      (fun x hx => by
        have h := hc (1,x) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨one_mem _,hx⟩)
        rw [BinaryBorel.sylow_eq_prod] at h
        exact h.2)
    intro x hx
    rw [BinaryBorel.borel_eq_prod] at hx
    rw [BinaryBorel.sylow_eq_prod]
    exact ⟨h₁ x.1 hx.1,h₂ x.2 hx.2⟩
  · have hpow (x : BinaryBorel.Torus (BinaryBorel.firstSylow S)) : x^3 = 1 := by
      obtain ⟨x,rfl⟩ := BinaryBorel.torusMap_surjective (BinaryBorel.firstSylow S) x
      have h := hc (x.val,1) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨x.property,one_mem _⟩)
      rw [BinaryBorel.sylow_eq_prod] at h
      have hi : (x.val⁻¹)^3 ∈ (BinaryBorel.firstSylow S : Subgroup Q) := by
        have h1 := h.1
        change (a₁ 1 * x.val⁻¹)^3 ∈ (BinaryBorel.firstSylow S : Subgroup Q) at h1
        simpa only [map_one,one_mul] using h1
      have hp : x^3 ∈ pCore 2 (BinaryBorel.borel (BinaryBorel.firstSylow S)) := by
        rw [BinaryBorel.twoCore]
        change x.val^3 ∈ (BinaryBorel.firstSylow S : Subgroup Q)
        simpa only [inv_pow,inv_mem_iff] using hi
      rw [←map_pow]
      exact QuotientGroup.eq_one_iff _ |>.mpr hp
    let := BinaryBorel.torus_cyclic (Nat.le_of_lt hn) hm (BinaryBorel.firstSylow S)
    have hd := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
    rw [IsCyclic.exponent_eq_card,BinaryBorel.torus_card (Nat.le_of_lt hn) hm] at hd
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
    have hlt : 4 < 2^n := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
    omega
end CFSG.Quasithin.Chapter12.Section06.ExchangedField
