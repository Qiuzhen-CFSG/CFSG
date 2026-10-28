module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal.FrattiniSource
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.SylowAction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups.Restriction

/-!
# Constructing the actual common E₉ and its Frattini actor

The original cubic X lies in K and outside Kˣ. Its conjugate lies in the
normal intersection of Kˣ with the literal common normalizer. Hence this
intersection has three-divisible order. Restricting the marked projective
action to its actual Sylow retains a three-prime kernel. The resulting
root action constructs a Sylow E₉ above X; Frattini's argument rechooses the
original crossing while preserving every marked conjugate normalized by
that same intersection.

The original projective action, its Sylow invariance, and its three-prime
kernel are retained as earlier source inputs. The kernel comes from the
rank-two component action in N(Dˣ), not from an assumed E₉ or faithful root
action. Source: Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/
public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal
open Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G]

theorem exists_nine_common_sylow (D R K X : Subgroup G) (x : G)
    (hD : x ^ 2 ∈ normalizer (D : Set G)) (hR : x ∈ normalizer (R : Set G))
    (hX : Nat.card X = 3) (hXK : X ≤ K)
    (hXN : X ≤ pairNormalizer D R x⁻¹)
    (hXnot : ¬ X ≤ K.conjBy x⁻¹)
    (hnK : pairNormalizer D R x⁻¹ ≤ normalizer (K.conjBy x⁻¹ : Set G))
    (α : pairNormalizer D R x⁻¹ →* MulAut Matrix.PSL3Four.PSL)
    (P₀ : Sylow 2 Matrix.PSL3Four.PSL)
    (hP₀ : ∀ a, (P₀ : Subgroup Matrix.PSL3Four.PSL).map (α a).toMonoidHom = P₀)
    (hker : Nat.Coprime 3 (Nat.card α.ker)) :
    ∃ Y : Subgroup G, X ≤ Y ∧ Y ≤ pairNormalizer D R x⁻¹ ∧
      Nat.card Y = 9 ∧ IsElementaryAbelian 3 Y ∧
      (∃ P : Sylow 3 (pairNormalizer D R x⁻¹),
        (P : Subgroup (pairNormalizer D R x⁻¹)).map (pairNormalizer D R x⁻¹).subtype = Y) ∧
      ∃ y : G, y ∈ normalizer (Y : Set G) ∧
        ∀ A : Subgroup G, pairNormalizer D R x⁻¹ ≤ normalizer (A.conjBy x⁻¹ : Set G) →
          A.conjBy y⁻¹ = A.conjBy x⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let N := pairNormalizer D R x⁻¹
  let J := (K.conjBy x⁻¹).subgroupOf N
  let XN := X.subgroupOf N
  have hDinv : (x⁻¹) ^ 2 ∈ normalizer (D : Set G) := by
    rw [inv_pow]
    exact (normalizer (D : Set G)).inv_mem hD
  have hN : x⁻¹ ∈ normalizer (N : Set G) :=
    mem_normalizer_pairNormalizer D R x⁻¹ hDinv ((normalizer (R : Set G)).inv_mem hR)
  let : J.Normal := normal_subgroupOf_of_le_normalizer hnK
  have hXNcard : Nat.card XN = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv).trans hX
  have hXNJ : ¬ XN ≤ J := by
    intro h
    apply hXnot
    intro a ha
    exact h (show (⟨a, hXN ha⟩ : N) ∈ XN from ha)
  have hXxN : X.conjBy x⁻¹ ≤ N := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hXN
    change X.conjBy x⁻¹ ≤ N.conjBy x⁻¹ at hh
    have he : N.conjBy x⁻¹ = N := mem_normalizer_iff_map_conj_eq.mp hN
    rwa [he] at hh
  have hXxK : X.conjBy x⁻¹ ≤ K.conjBy x⁻¹ := map_mono hXK
  have hJ3 : 3 ∣ Nat.card J := by
    let i : (X.conjBy x⁻¹) →* J := {
      toFun a := ⟨⟨a, hXxN a.property⟩, hXxK a.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hi : Function.Injective i := by
      intro a b h
      exact Subtype.ext (congrArg (fun t : J => ((t : N) : G)) h)
    have hh := card_dvd_of_injective i hi
    have hc : Nat.card (X.conjBy x⁻¹) = 3 := by
      rw [conjBy, card_map_of_injective (MulAut.conj x⁻¹).injective, hX]
    rwa [hc] at hh
  obtain ⟨_, β, _, hk⟩ := exists_root_action α P₀ hP₀ hker
  obtain ⟨P, hXP, hPcard, hPe⟩ := exists_nine_sylow_above_external_cubic β hk J XN
    hJ3 hXNcard hXNJ
  let Y := (P : Subgroup N).map N.subtype
  have hXY : X ≤ Y := by
    rw [← map_subgroupOf_eq_of_le hXN]
    exact map_mono hXP
  let : IsElementaryAbelian 3 (P : Subgroup N) := hPe
  have hYe : IsElementaryAbelian 3 Y := IsElementaryAbelian.map N.subtype
  have hYcard : Nat.card Y = 9 := by
    rw [card_map_of_injective N.subtype_injective]
    exact hPcard
  obtain ⟨y, hy, _, hpres⟩ := exists_frattini_adjustment_preserving N P x⁻¹ hN
  refine ⟨Y, hXY, map_subtype_le _, hYcard, hYe, ⟨P, rfl⟩,
    y⁻¹, (normalizer _).inv_mem hy, ?_⟩
  intro A hA
  simpa only [inv_inv] using hpres A hA
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal
