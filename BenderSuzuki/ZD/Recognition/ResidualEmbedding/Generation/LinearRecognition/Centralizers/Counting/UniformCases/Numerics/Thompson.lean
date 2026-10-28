module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Support

/-!
# The supported Thompson order formula for proper residual centralizers

Partition mixed pairs by the two classes in the proved half-order support.
Conjugation identifies all fibers over one class, and the class-size formula
cancels the ambient order to give the two-term integral order identity.
There may be other involution classes in the ambient group.

Source: GLS4, Chapter 2, Lemma 12.8, `refs/KGroup/GLS4/Chapter2.tex`.
The finite counting argument adapts `Theory.GroupTheory.TwoInvolutionClassOrder`
by requiring completeness only on the image of the half-order map.
-/

open scoped BigOperators
noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G]
namespace ResidualNumerics

private abbrev MixedPairs (z v : G) :=
  {p : G × G // IsConj z p.1 ∧ IsConj v p.2}

private noncomputable def classFiberEquiv (z v c : G) :
    (Σ u : {u : G // IsConj c u}, Fiber z v u.val) ≃
      {p : MixedPairs z v // IsConj c (halfOrder p.val.1 p.val.2)} where
  toFun p := ⟨⟨p.2.val, p.2.property.1, p.2.property.2.1⟩,
    p.2.property.2.2.symm ▸ p.1.property⟩
  invFun p := ⟨⟨halfOrder p.val.val.1 p.val.val.2, p.property⟩,
    ⟨p.val.val, p.val.property.1, p.val.property.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨u, hu⟩, ⟨⟨a, b⟩, ha, hb, he⟩⟩
    dsimp at he
    subst u
    rfl
  right_inv := by intro p; rfl

private theorem card_class_part [Finite G] (z v c : G) :
    Nat.card {p : MixedPairs z v // IsConj c (halfOrder p.val.1 p.val.2)} =
      Nat.card {u : G // IsConj c u} * kappa z v c := by
  classical
  let : Fintype {u : G // IsConj c u} := Fintype.ofFinite _
  rw [← Nat.card_congr (classFiberEquiv z v c), Nat.card_sigma]
  have hf (u : {u : G // IsConj c u}) : Nat.card (Fiber z v u.val) = kappa z v c := by
    simpa only [kappa_def, Fiber, halfOrder_def] using
      (kappa_eq_of_isConj z v u.property).symm
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.cast_id]

/-- Count mixed pairs by the two possible conjugacy classes of their canonical involution. -/
private theorem mixed_pair_count [Finite G] (z v : G)
    (hn : ¬ IsConj z v)
    (hsupport : ∀ a b : G, IsConj z a → IsConj v b →
      IsConj z (halfOrder a b) ∨ IsConj v (halfOrder a b)) :
    Nat.card {p : G × G // IsConj z p.1 ∧ IsConj v p.2} =
      Nat.card {u : G // IsConj z u} * kappa z v z +
      Nat.card {u : G // IsConj v u} * kappa z v v := by
  classical
  have hiff (p : MixedPairs z v) :
      (¬ IsConj z (halfOrder p.val.1 p.val.2)) ↔
        IsConj v (halfOrder p.val.1 p.val.2) := by
    have hu := hsupport _ _ p.property.1 p.property.2
    exact ⟨fun h => hu.resolve_left h, fun h h' => hn (h'.trans h.symm)⟩
  have hc := Nat.card_congr (Equiv.sumCompl
    (fun p : MixedPairs z v => IsConj z (halfOrder p.val.1 p.val.2)))
  rw [Nat.card_sum,
    Nat.card_congr (Equiv.subtypeEquivRight hiff),
    card_class_part, card_class_part] at hc
  exact hc.symm

/-- Only the support of the mixed fibers is required. -/
private theorem card_eq [Finite G] (z v : G)
    (hn : ¬ IsConj z v)
    (hsupport : ∀ a b : G, IsConj z a → IsConj v b →
      IsConj z (halfOrder a b) ∨ IsConj v (halfOrder a b)) :
    Nat.card G = kappa z v z * Nat.card (Subgroup.centralizer ({v} : Set G)) +
      kappa z v v * Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  have hc := mixed_pair_count z v hn hsupport
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
    (p := IsConj z) (q := IsConj v)), Nat.card_prod] at hc
  have hzclass : Nat.card {u : G // IsConj z u} *
      Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card G :=
    ConjClasses.nat_card_carrier_mul_card_centralizer z
  have hvclass : Nat.card {u : G // IsConj v u} *
      Nat.card (Subgroup.centralizer ({v} : Set G)) = Nat.card G :=
    ConjClasses.nat_card_carrier_mul_card_centralizer v
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
  calc
    Nat.card G * Nat.card G =
        (Nat.card {u : G // IsConj z u} * Nat.card {u : G // IsConj v u}) *
          (Nat.card (Subgroup.centralizer ({z} : Set G)) *
            Nat.card (Subgroup.centralizer ({v} : Set G))) := by
      calc
        _ = (Nat.card {u : G // IsConj z u} *
              Nat.card (Subgroup.centralizer ({z} : Set G))) *
            (Nat.card {u : G // IsConj v u} *
              Nat.card (Subgroup.centralizer ({v} : Set G))) :=
          congrArg₂ (· * ·) hzclass.symm hvclass.symm
        _ = _ := by ring
    _ = (Nat.card {u : G // IsConj z u} *
          Nat.card (Subgroup.centralizer ({z} : Set G))) *
          (kappa z v z * Nat.card (Subgroup.centralizer ({v} : Set G))) +
        (Nat.card {u : G // IsConj v u} *
          Nat.card (Subgroup.centralizer ({v} : Set G))) *
          (kappa z v v * Nat.card (Subgroup.centralizer ({z} : Set G))) := by
      rw [hc]; ring
    _ = _ := by rw [hzclass, hvclass]; ring


end ResidualNumerics

variable [Finite G] {Z : Set G} {M : Subgroup G}

/-- The two-term Thompson formula for a distinguished involution and any
involution of D, before the individual fiber cardinalities are evaluated. -/
public theorem proper_residualGenerated_thompson_order
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    Nat.card G = kappa z v z * Nat.card (centralizer ({v} : Set G)) +
      kappa z v v * Nat.card (centralizer ({z} : Set G)) := by
  have hn : ¬ IsConj z v := by
    intro hc
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    exact not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM hvD
      (hg ▸ h.disconnected.invariant g z hz)
  apply ResidualNumerics.card_eq z v hn
  intro a b hab hb
  exact (proper_residualGenerated_mixed_support h r ha hz hzM ht htM hL heven hlocal
    hvD hv a b hab hb).imp And.left id

end BenderSuzuki.ZD
