module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
public import Theory.Mathieu.M22.Properties.PairHexadIncidence

/-!
# Arbitrary source J-subgroups in the native M₂₂ geometry

The relative S₅/E₁₆ hypothesis gives order 1920. Native Sylow geometry
recognizes every such subgroup as a genuine pair stabilizer and selects an
incident hexad whose pointwise kernel lies in it. The two elementary kernels
are distinct: equality would make J normalize the hexad kernel, forcing J
inside an impossible index-three subgroup of the hexad stabilizer.

Source: Aschbacher–Smith I.2.2(6a) and its intersection argument, printed
pp.410 and 412 / PDF pp.421 and 423. This module proves geometry only;
central residual placement requires the compatible cover action calculation.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open Subgroup Sporadic.Mathieu
open scoped Pointwise

theorem sourceJ_card (H : Subgroup M22) (hH : IsSourceJ H) : Nat.card H = 1920 := by
  obtain ⟨N, hN, _, hc, ⟨a⟩⟩ := hH
  let := hN
  have hi : N.index = 120 := by
    rw [index_eq_card, Nat.card_congr a.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  rw [← N.card_mul_index, hi, hc]

theorem sourceJ_index (H : Subgroup M22) (hH : IsSourceJ H) : H.index = 231 := by
  have h := H.card_mul_index
  rw [sourceJ_card H hH, m22_order] at h
  omega

/-- The arbitrary source subgroup is an actual native pair stabilizer. -/
theorem sourceJ_eq_pair_stabilizer (H : Subgroup M22) (hH : IsSourceJ H) :
    ∃ S : Finset (Fin 22), S.card = 2 ∧ H = MulAction.stabilizer M22 S :=
  m22_card1920_eq_pair_stabilizer H (sourceJ_card H hH)

/-- The source E₁₆ is never a hexad pointwise kernel. In particular it must
not be silently substituted for the different kernel in an incident hexad. -/
theorem sourceJ_twoCore_ne_hexadKernel (H : Subgroup M22) (hH : IsSourceJ H)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (pCore 2 H).map H.subtype ≠ m22HexadPointwiseKernel B := by
  intro he
  have hn : H ≤ normalizer ((pCore 2 H).map H.subtype : Set M22) := by
    have h := (pCore 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  rw [he, m22HexadPointwiseKernel_normalizer hB] at hn
  exact m22_card1920_not_le_hexad H (sourceJ_card H hH) hB hn

/-- A genuine incident hexad for arbitrary H, with both kernels kept separate. -/
theorem sourceJ_incident_hexad (H : Subgroup M22) (hH : IsSourceJ H) :
    ∃ S B : Finset (Fin 22), S.card = 2 ∧ B ∈ m22Blocks ∧ S ⊆ B ∧
      H = MulAction.stabilizer M22 S ∧ m22HexadPointwiseKernel B ≤ H ∧
      (pCore 2 H).map H.subtype ≠ m22HexadPointwiseKernel B := by
  obtain ⟨S, B, hS, hB, hSB, hHS, hk⟩ :=
    m22_card1920_incident_hexad H (sourceJ_card H hH)
  exact ⟨S, B, hS, hB, hSB, hHS, hk, sourceJ_twoCore_ne_hexadKernel H hH hB⟩

/-- Arbitrary H also admits the disjoint relative position. This retains the
literal base subgroup and the conjugator needed for a cover calculation. -/
theorem sourceJ_disjoint_flag (H : Subgroup M22) (hH : IsSourceJ H) :
    ∃ g : M22, H = m22DisjointPairStabilizer.map (MulAut.conj g).toMonoidHom ∧
      g • m22Hexad123 ∈ m22Blocks ∧
      Disjoint (g • m22DisjointPair04) (g • m22Hexad123) ∧
      (m22HexadStabilizer ⊓ m22DisjointPairStabilizer).map
          (MulAut.conj g).toMonoidHom = MulAction.stabilizer M22 (g • m22Hexad123) ⊓ H :=
  m22_card1920_disjoint_flag H (sourceJ_card H hH)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
