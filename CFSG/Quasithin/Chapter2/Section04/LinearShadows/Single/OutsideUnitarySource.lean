module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFixedCardSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideCardSource

/-!
# The numerical unitary-type outside fixed row

For a centerless block, a noncentral outside involution fixes a subgroup of
order 2^(3m), with n=2m. Its derived and Frattini subgroups are the literal
fixed part of Z(R), of order 2^m. The Singer center action and exchanged
maximum elementary subgroups discharge every local premise.

These are precisely the numerical outputs of Aschbacher–Smith, 2.4.14(2),
needed for the transfer counting argument on printed p.539.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_outside_noncentral_fixed_data
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype) = ⊥)
    (a : G) (haT : a ∈ T) (haS : a ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ha2 : a^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    let I := R ⊓ centralizer ({a} : Set G)
    let Z₀ := Z ⊓ centralizer ({a} : Set G)
    a ∉ centralizer (Z : Set G) →
    ∃ m : ℕ, 0<m ∧ n=2*m ∧ Nat.card Z₀=2^m ∧ Nat.card I=2^(3*m) ∧
      ⁅I,I⁆=Z₀ ∧ (frattini I).map I.subtype=Z₀ := by
  intro R Z I Z₀ han
  obtain ⟨m,hm,hn,hc⟩ := source_centerless_center_involution_fixed_card d hG T hST hsingle hL
    hM hTM hunique c hZ a haT ha2 han
  have ht := source_centerless_center_involution_coboundary d hG T hST hsingle hL
    hM hTM hunique c hZ a haT ha2 han
  refine ⟨m,hm,hn,hc,?_,?_,?_⟩
  · have hi := source_centerless_outside_fixed_card_of_coboundaries d hG T hST hsingle hL
      hM hTM hunique a haT haS ha2 ht hZ
    change Nat.card I=2^n*Nat.card Z₀ at hi
    rw [hi,hc,hn,←pow_add]
    congr 1
    omega
  · exact source_outside_fixed_derived_of_coboundaries d hG T hST hsingle hL
      hM hTM hunique a haT haS ha2 ht
  · exact source_outside_fixed_frattini_of_coboundaries d hG T hST hsingle hL
      hM hTM hunique a haT haS ha2 ht
end CFSG.Quasithin.Chapter2.LinearShadows.Single
