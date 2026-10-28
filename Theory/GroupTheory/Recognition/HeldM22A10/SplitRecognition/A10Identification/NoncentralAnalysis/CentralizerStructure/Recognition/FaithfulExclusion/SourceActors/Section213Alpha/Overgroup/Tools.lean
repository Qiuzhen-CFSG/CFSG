module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Sylow
public import Mathlib.GroupTheory.IndexNormal

/-!
# Normalizer and Sylow tools for Held's Section 2.13

A normalizer preserves the center of a subgroup. If its only nonidentity
square is q, the normalizer centralizes q as well. The nonfusion Sylow bound
for C_G(mu) transports along conjugacy: every Sylow two-subgroup of a
conjugate involution centralizer has order 64, and every two-subgroup therein
has order at most 64. These arguments require no centralizer order or simple
section recognition.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 2.13, p.231.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
universe u
variable {G : Type u} [Group G]

public theorem overgroup_normalizer_centralizes_square (B : Subgroup G) (q : G)
    (hq : q ≠ 1) (hs : ∀ x ∈ B, x ^ 2 = 1 ∨ x ^ 2 = q)
    (hw : ∃ x ∈ B, x ^ 2 = q) :
    normalizer (B : Set G) ≤ centralizer ({q} : Set G) := by
  intro g hg
  obtain ⟨x, hx, hxx⟩ := hw
  have hm := (mem_normalizer_iff.mp hg x).mp hx
  have he : (g * x * g⁻¹) ^ 2 = g * q * g⁻¹ := by
    rw [← MulAut.conj_apply, ← map_pow, hxx, MulAut.conj_apply]
  have hfix : g * q * g⁻¹ = q := by
    rcases hs _ hm with h | h
    · rw [he] at h
      have : q = 1 := by
        have hh := congrArg (fun z => g⁻¹ * z * g) h
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
      exact (hq this).elim
    · exact he.symm.trans h
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)

public theorem overgroup_normalizer_center (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer ((B ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
  have step (g : G) (hg : g ∈ normalizer (B : Set G)) (x : G)
      (hx : x ∈ B ⊓ centralizer (B : Set G)) :
      g * x * g⁻¹ ∈ B ⊓ centralizer (B : Set G) := by
    refine ⟨(mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    intro y hy
    have hy' : g⁻¹ * y * g ∈ B := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp ((normalizer _).inv_mem hg) y).mp hy
    have hc := mem_centralizer_iff.mp hx.2 _ hy'
    have hh := congrArg (fun z => g * z * g⁻¹) hc
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hh
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact step g hg x
  · intro hx
    have hh := step g⁻¹ ((normalizer _).inv_mem hg) _ hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

private def overgroupCentralizerConjEquiv {x y : G} (g : G) (h : g * x * g⁻¹ = y) :
    centralizer ({x} : Set G) ≃* centralizer ({y} : Set G) := by
  let f := MulAut.conj g
  have he : f x = y := h
  have hm (a : G) : a ∈ centralizer ({x} : Set G) ↔ f a ∈ centralizer ({y} : Set G) := by
    simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, f.injective.eq_iff]
  exact { Equiv.subtypeEquiv f.toEquiv hm with map_mul' := fun a b => Subtype.ext (f.map_mul a b) }

variable [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem overgroup_sylow_card (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    {x : G} (hx : IsConj x (D.a10NoncentralInvolution e))
    (T : Sylow 2 (centralizer ({x} : Set G))) : Nat.card T = 64 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  let f := overgroupCentralizerConjEquiv g hg
  obtain ⟨S, hS⟩ := exists_sylow_eq_P D e hfusion
  have hc : Nat.card (centralizer ({x} : Set G)) = Nat.card (C D e) := Nat.card_congr f.toEquiv
  rw [T.card_eq_multiplicity, hc, ← S.card_eq_multiplicity]
  change Nat.card (S : Subgroup (C D e)) = 64
  rw [hS, P_card]

public theorem overgroup_two_subgroup_card_le (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    {x : G} (hx : IsConj x (D.a10NoncentralInvolution e))
    (K : Subgroup G) (hK : IsPGroup 2 K) (hKx : K ≤ centralizer ({x} : Set G)) :
    Nat.card K ≤ 64 := by
  have hp : IsPGroup 2 (K.subgroupOf (centralizer ({x} : Set G))) :=
    hK.of_equiv (subgroupOfEquivOfLe hKx).symm
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hc := card_le_of_le hT
  rw [Nat.card_congr (subgroupOfEquivOfLe hKx).toEquiv, overgroup_sylow_card D e hfusion hx T] at hc
  exact hc

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
