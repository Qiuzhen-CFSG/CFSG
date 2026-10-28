module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeFixed
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaQuotient
public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOmega
public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeDerived

/-!
# Assembling the cyclic fixed centralizer from the derived calculations

Write X for the ambient image of K=O₂(N_G(F)) and D for X′. Once
|D|=64 and C_X(Q)≤D are established, the fixed line in F and the index
|D:F|=2 bound |C_X(Q)| by four. Orbit counting modulo three forces
order four. The equality Ω₁(D)=F excludes a four-group and identifies
the square of a generator with the supplied fixed involution v.

The assembly lemma first takes these two derived calculations as explicit
inputs. The final theorem discharges both using the actual derived-core
order and fixed-point containment, retaining the supplied Q and v.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the paragraph beginning “An easy computation shows that K′”.
-/


open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}
/-- The two derived-core calculations produce an actual order-four generator,
with prescribed square, for the centralizer of the supplied Q. -/
public theorem exists_normalizer_three_cyclic_generator_of_derived_calculations
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    Nat.card D = 64 →
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∃ b : G, b ∈ X ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X ⊓ centralizer (A : Set G) = zpowers b := by
  classical
  intro N X D A hDcard hCD v hv hfix
  let C := X ⊓ centralizer (A : Set G)
  have hFD : d.F ≤ D := d.elementary_le_normalizer_core_derived h hN hproper
  have hDX : D ≤ X := map_subtype_le _
  have hCeq : C = D ⊓ centralizer (A : Set G) :=
    le_antisymm (le_inf hCD inf_le_right) (inf_le_inf_right _ hDX)
  have hFidx : d.F.relIndex D = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) d.F D bot_le hFD
    rw [relIndex_bot_left, relIndex_bot_left, d.card, hDcard] at hh
    omega
  have hFfix : Nat.card ((centralizer (A : Set G)).subgroupOf d.F) = 2 := by
    rw [← card_map_of_injective (K := (centralizer (A : Set G)).subgroupOf d.F)
      d.F.subtype_injective, subgroupOf_map_subtype, inf_comm, hfix, Nat.card_zpowers, hv]
  have hsmall : Nat.card C ≤ 4 := by
    have hh := card_le_centralizer_card_mul_relIndex C d.F (A : Set G) inf_le_right
    rw [hFfix] at hh
    have hi := relIndex_le_of_le_right hCD (show d.F.relIndex D ≠ 0 by omega)
    rw [hFidx] at hi
    change d.F.relIndex C ≤ 2 at hi
    omega
  have hbig : 2 ≤ Nat.card C := by
    have hh := card_le_of_le (inf_le_inf_right (centralizer (A : Set G)) d.le_normalizer_core)
    rw [hfix, Nat.card_zpowers, hv] at hh
    exact hh
  have hCcard : Nat.card C = 4 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hAcard : Nat.card A = 3 :=
      (card_map_of_injective N.subtype_injective).trans (d.normalizer_three_card h hN hproper Q)
    have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
    have hh := A.card_modEq_card_inf_centralizer D hp
      ((map_subtype_le (Q : Subgroup N)).trans d.normalizer_core_derived_normalized)
    rw [← hCeq, hDcard] at hh
    change 64 % 3 = Nat.card C % 3 at hh
    omega
  have hnot : ¬ C ≤ zpowers v := by
    intro hh
    have hc := card_le_of_le hh
    rw [hCcard, Nat.card_zpowers, hv] at hc
    omega
  obtain ⟨b, hb, hbv⟩ := SetLike.not_le_iff_exists.mp hnot
  have hb4 : b ^ 4 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨b, hb⟩ : C))
    rw [hCcard] at hh
    exact congrArg C.subtype hh
  have hb2 : b ^ 2 ≠ 1 := by
    intro hh
    have hbF := (d.normalizer_core_derived_square_one_iff h hN hproper b (hCD hb)).mp hh
    exact hbv (hfix ▸ ⟨hbF, hb.2⟩)
  have horder : orderOf b = 4 := by
    have hd := orderOf_dvd_of_pow_eq_one hb4
    have hn : orderOf b ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with h1 | h2 | h4
    · have hh := pow_orderOf_eq_one b
      rw [h1, pow_one] at hh
      exact (hb2 (by rw [hh, one_pow])).elim
    · exact (hb2 (h2 ▸ pow_orderOf_eq_one b)).elim
    · exact h4
  have hsquare : b ^ 2 = v := by
    have hp : (b ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hb4
    have hm : b ^ 2 ∈ zpowers v := by
      rw [← hfix]
      exact ⟨(d.normalizer_core_derived_square_one_iff h hN hproper (b ^ 2)
        (D.pow_mem (hCD hb) 2)).mp hp, (C.pow_mem hb 2).2⟩
    rw [mem_zpowers_iff_mem_range_orderOf, hv] at hm
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hm
    have hlt := Finset.mem_range.mp hn
    interval_cases n
    · exact (hb2 (by simpa using heq.symm)).elim
    · simpa using heq.symm
  refine ⟨b, hb.1, horder, hsquare, ?_⟩
  exact (eq_of_le_of_card_ge (zpowers_le.mpr hb)
    (by rw [Nat.card_zpowers, horder, hCcard])).symm

/-- The centralizer in the actual normalizer core of the supplied Sylow
three-subgroup is generated by an element of order four whose square is the
supplied fixed involution. -/
public theorem exists_normalizer_three_cyclic_generator
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let A := (Q : Subgroup N).map N.subtype
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∃ b : G, b ∈ X ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X ⊓ centralizer (A : Set G) = zpowers b := by
  exact d.exists_normalizer_three_cyclic_generator_of_derived_calculations h hN hproper Q
    (d.normalizer_core_derived_order h hN hproper)
    (d.normalizer_three_centralizer_le_derived h hN hproper Q)

end Stellmacher.Recognition.ParrottSecondElementaryData
