module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Terminal.LocalCentralizers
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# Relative conjugacy in Held's terminal overgroup

`terminalOrbit K x` is the actual set of conjugates of x by elements of K.
Orbit--stabilizer computes its size using K intersected with the ambient
centralizer. Conjugation transports these relative centralizers as groups,
and therefore preserves the orders of their centers. The proofs use the
ordinary conjugacy class inside K and explicit subgroup equivalences.

Source application: D. Held, "A Characterization of some multiply transitive
permutation groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.6, printed p.229.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

universe u
variable {G : Type u} [Group G]

/-- Conjugates by actual elements of K, written with left conjugation. -/
@[expose] public def terminalOrbit (K : Subgroup G) (x : G) : Set G :=
  Set.range (fun g : K => (g : G) * x * (g : G)⁻¹)

public theorem mem_terminalOrbit (K : Subgroup G) (x y : G) :
    y ∈ terminalOrbit K x ↔ ∃ g ∈ K, g * x * g⁻¹ = y := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, g.property, hg⟩
  · rintro ⟨g, hg, he⟩
    exact ⟨⟨g, hg⟩, he⟩

private theorem terminalOrbit_card_eq_class (K : Subgroup G) (x : G) (hx : x ∈ K) :
    Nat.card (terminalOrbit K x) = Nat.card (ConjClasses.mk (⟨x, hx⟩ : K)).carrier := by
  let f : (ConjClasses.mk (⟨x, hx⟩ : K)).carrier → terminalOrbit K x := fun y =>
    ⟨y.1.1, by
      obtain ⟨g, hg⟩ := isConj_iff.mp (show IsConj (⟨x, hx⟩ : K) y.1 from y.2)
      exact ⟨g, congrArg Subtype.val hg⟩⟩
  apply (Nat.card_congr (Equiv.ofBijective f ?_)).symm
  constructor
  · intro a b h
    have he : a.1.1 = b.1.1 := congrArg (fun z : terminalOrbit K x => z.val) h
    exact Subtype.ext (Subtype.ext he)
  · rintro ⟨y, g, rfl⟩
    refine ⟨⟨g * ⟨x, hx⟩ * g⁻¹, ?_⟩, rfl⟩
    exact isConj_iff.mpr ⟨g, rfl⟩

private def terminalIntersectionEquiv (K : Subgroup G) (x : G) (hx : x ∈ K) :
    centralizer ({(⟨x, hx⟩ : K)} : Set K) ≃* (K ⊓ centralizer ({x} : Set G) : Subgroup G) where
  toFun a := ⟨a.1.1, a.1.2, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.2))⟩
  invFun a := ⟨⟨a.1, a.2.1⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp a.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

public theorem terminalOrbit_card_mul (K : Subgroup G) (x : G) (hx : x ∈ K) :
    Nat.card (terminalOrbit K x) *
      Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card K := by
  rw [terminalOrbit_card_eq_class K x hx,
    ← Nat.card_congr (terminalIntersectionEquiv K x hx).toEquiv]
  exact ConjClasses.nat_card_carrier_mul_card_centralizer _

private theorem terminal_conj_mem (K : Subgroup G) (g : K) (a : G) :
    a ∈ K ↔ MulAut.conj (g : G) a ∈ K := by
  constructor
  · intro ha
    exact K.mul_mem (K.mul_mem g.property ha) (K.inv_mem g.property)
  · intro ha
    have h := K.mul_mem (K.mul_mem (K.inv_mem g.property) ha) g.property
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using h

private noncomputable def terminalCentralizerConjEquiv (K : Subgroup G) {x y : G}
    (hy : y ∈ terminalOrbit K x) :
    (K ⊓ centralizer ({x} : Set G) : Subgroup G) ≃*
      (K ⊓ centralizer ({y} : Set G) : Subgroup G) := by
  let g : K := Classical.choose hy
  have hg : (g : G) * x * (g : G)⁻¹ = y := Classical.choose_spec hy
  let e := MulAut.conj (g : G)
  have he : e x = y := hg
  have hm (a : G) : a ∈ (K ⊓ centralizer ({x} : Set G) : Subgroup G) ↔
      e a ∈ (K ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    simp only [mem_inf, mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff]
    exact and_congr (terminal_conj_mem K g a) Iff.rfl
  exact { Equiv.subtypeEquiv e.toEquiv hm with map_mul' := fun a b => Subtype.ext (e.map_mul a b) }

public theorem terminalCentralizer_card_eq (K : Subgroup G) {x y : G}
    (hy : y ∈ terminalOrbit K x) :
    Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) =
      Nat.card (K ⊓ centralizer ({y} : Set G) : Subgroup G) :=
  Nat.card_congr (terminalCentralizerConjEquiv K hy).toEquiv

public theorem terminalCentralizer_center_card_eq (K : Subgroup G) {x y : G}
    (hy : y ∈ terminalOrbit K x) :
    Nat.card (center (K ⊓ centralizer ({x} : Set G) : Subgroup G)) =
      Nat.card (center (K ⊓ centralizer ({y} : Set G) : Subgroup G)) :=
  Nat.card_congr (centerCongr (terminalCentralizerConjEquiv K hy)).toEquiv

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
