module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors.Quotient

/-!
# The two quotient inductions in B.1.10

`SmallerCases n` is the strong-induction hypothesis for groups of order less
than n, with their own faithful binary representations. Given a normal odd
nilpotent subgroup N not centralized by K, the action on the literal quotient
NKA/O₂(NKA) is another counterexample. Its order cannot be smaller, and the
subgroup and quotient order bounds therefore force NKA = G and O₂(NKA) = 1.

The two applications use N = F(G) and N = C_F(G)(J*) respectively. The
noncentrality premise for the latter is an output of the B.1.9 decomposition,
not a claim made here. Final induction assembly retains responsibility for
proving the strong-induction hypothesis and that decomposition consequence.

Source: Aschbacher–Smith, B.1.10, printed p.72 (PDF p.83).
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
universe u v

def SmallerCases (n : ℕ) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) D W), Nat.card D < n →
    Function.Injective σ → pCore 2 D = ⊥ →
    ∀ K A : Subgroup D, (IsQuasisimple K ∨ Nat.card K = 3) →
      IsBestOffender σ A → K = ⁅K,A⁆ → K ≤ centralizer (fittingSubgroup D : Set D)

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem normalOdd_reduction (hsmall : SmallerCases.{u,v} (Nat.card G))
    (hfaith : Function.Injective ρ) (N K A : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] (hN : Nat.Coprime 2 (Nat.card N))
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K,A⁆) (hne : ⁅N,K⁆ ≠ ⊥) :
    N ⊔ (K ⊔ A) = ⊤ ∧ pCore 2 ↥(N ⊔ (K ⊔ A)) = ⊥ := by
  let H := N ⊔ (K ⊔ A)
  let τ := ρ.comp H.subtype
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let N₀ := N.subgroupOf H
  let K₀ := K.subgroupOf H
  let A₀ := A.subgroupOf H
  have hNH : N ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_left.trans le_sup_right
  have hAH : A ≤ H := le_sup_right.trans le_sup_right
  have hN₀ : Nat.Coprime 2 (Nat.card N₀) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]
  let : Group.IsNilpotent N₀ := Group.nilpotent_of_mulEquiv
    (subgroupOfEquivOfLe hNH).symm
  have hK₀ : IsQuasisimple K₀ ∨ Nat.card K₀ = 3 := by
    rcases hK with hK | hK
    · let : IsQuasisimple K := hK
      exact Or.inl (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKH).symm)
    · right
      rwa [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv]
  have hcomm : K₀ = ⁅K₀,A₀⁆ := by
    apply Subgroup.map_injective H.subtype_injective
    simp only [K₀, A₀, map_commutator, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le hAH, ← hKA]
  have hNmove : ⁅N₀,K₀⁆ ≠ ⊥ := by
    intro hz
    apply hne
    have hh := congrArg (Subgroup.map H.subtype) hz
    simpa only [N₀, K₀, map_commutator, map_subgroupOf_eq_of_le hNH,
      map_subgroupOf_eq_of_le hKH, Subgroup.map_bot] using hh
  obtain ⟨_, hQNK, hk⟩ := normalOdd_fixedSpace_kernel ρ hfaith N K A hN hK hA hKA
  have hQK : Q ≤ centralizer (K₀ : Set H) := hQNK.trans
    (centralizer_le (show K₀ ≤ (N ⊔ K).subgroupOf H from fun _ hx => (show K ≤ N ⊔ K from le_sup_right) hx))
  let σ := quotientAction τ hk
  have hbest : IsBestOffender σ (A₀.map q) :=
    quotient_bestOffender τ hk K₀ A₀ hK₀ hcomm (hA.subgroupOf ρ hAH) hQK
  have hKq : K₀.map q = ⁅K₀.map q, A₀.map q⁆ := by rw [← map_commutator, ← hcomm]
  have hcore : pCore 2 (H ⧸ Q) = ⊥ :=
    irreducibleReduction_image_core_eq_bot q (QuotientGroup.mk'_surjective Q)
      (QuotientGroup.ker_mk' Q)
  have hnlt : ¬ Nat.card (H ⧸ Q) < Nat.card G := by
    intro hlt
    exact quotient_not_centralizes_fitting N₀ K₀ hN₀ hNmove
      (hsmall (H ⧸ Q) (fixedSpace τ Q) σ hlt
        (quotientAction_injective τ hk) hcore (K₀.map q) (A₀.map q)
        (quotient_factor K₀ hK₀) hbest hKq)
  have hDH : Nat.card (H ⧸ Q) ≤ Nat.card H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card Q)
  have hHG : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective H.subtype H.subtype_injective
  have hHeq : Nat.card H = Nat.card G := by omega
  have hDeq : Nat.card (H ⧸ Q) = Nat.card H := by omega
  refine ⟨H.eq_top_of_card_eq hHeq, ?_⟩
  apply Subgroup.card_eq_one.mp
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
  have hp : 0 < Nat.card H := Nat.card_pos
  rw [hDeq] at hc
  nlinarith

theorem fitting_reduction (hsmall : SmallerCases.{u,v} (Nat.card G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K,A⁆)
    (hne : ⁅fittingSubgroup G,K⁆ ≠ ⊥) :
    fittingSubgroup G ⊔ (K ⊔ A) = ⊤ ∧
      pCore 2 ↥(fittingSubgroup G ⊔ (K ⊔ A)) = ⊥ := by
  apply normalOdd_reduction ρ hsmall hfaith (fittingSubgroup G) K A _ hK hA hKA hne
  exact (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
    (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))

theorem centralizer_reduction (hsmall : SmallerCases.{u,v} (Nat.card G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K,A⁆)
    (hne : ⁅fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G), K⁆ ≠ ⊥) :
    let E := fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)
    E ⊔ (K ⊔ A) = ⊤ ∧ pCore 2 ↥(E ⊔ (K ⊔ A)) = ⊥ := by
  let E := fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)
  let : Group.IsNilpotent E := Group.nilpotent_of_mulEquiv
    (subgroupOfEquivOfLe (show E ≤ fittingSubgroup G from inf_le_left))
  apply normalOdd_reduction ρ hsmall hfaith E K A _ hK hA hKA hne
  exact (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
    (card_dvd_of_le ((show E ≤ fittingSubgroup G from inf_le_left).trans
      (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)))

end CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
