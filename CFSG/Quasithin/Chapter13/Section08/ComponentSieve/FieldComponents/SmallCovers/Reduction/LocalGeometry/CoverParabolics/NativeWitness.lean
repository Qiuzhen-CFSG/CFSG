module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.HexadCoverRestriction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan
public import Theory.GroupAction.PCoreCentralModelAction

/-!
# The actual local triple-cover witness in the Mathieu branch

The conjugation image of T is a two-group acting on the 77 native hexads.
An invariant hexad lifts to a T-normalized subgroup of K. Its solvable
residual is a C-component with the required Sylow and nontrivial two-core
conditions. Central-cover restriction identifies its two-core quotient as
a genuine triple cover of A₆, retaining the six-point projection.

This constructs K₁ < K in Aschbacher–Smith 13.8.21(2), printed p.956
(PDF p.973). Normality of K is relative to H; no arbitrary cover carrier
or assumed local-family membership is used.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open Theory.GroupAction.PCoreCentralModelAction
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
variable {G : Type*} [Group G]

theorem exists_normalized_hexad (H K T : Subgroup G)
    (hn : H ≤ normalizer (K : Set G)) (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22) :
    ∃ B ∈ m22Blocks, T ≤ normalizer (hexadLift K e B : Set G) := by
  let a := centralModelAction H K hn e
  let S := (T.subgroupOf H).map a
  have hp : IsPGroup 2 S := hT.comap_subtype.map a
  obtain ⟨B, hB⟩ := MathieuSolvableSpan.exists_invariant_hexad S hp
  refine ⟨B.val, B.property, ?_⟩
  intro t ht
  apply centralModelAction_normalizes_lift H K hn e m22_center_eq_bot
    (MulAction.stabilizer M22 B.val) ⟨t, hTH ht⟩
  exact MathieuSolvableSpan.innerHexad_normalized B
    (hB (mem_map.mpr ⟨⟨t, hTH ht⟩, ht, rfl⟩))

variable [Finite G]

noncomputable def localSix_hexad (H K T : Subgroup G)
    (hH : H.pCoreIn 2 ≠ ⊥) (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hn : T ≤ normalizer (hexadLift K e B : Set G)) : LocalSix K T where
  subgroup := hexadResidualIn K e B
  local_mem := hexadResidualIn_mem_LIn H K T hH hKH hT e hB hn
  centralQuotient := (centralPreimageQuotientEquiv _).trans
    (hexadResidualCentralQuotientEquiv K e hc hB)

theorem exists_localSix_mathieu (H K T : Subgroup G)
    (hH : H.pCoreIn 2 ≠ ⊥) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hT : Chapter1.IsSylowIn 2 T H)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* M22)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3) :
    ∃ s : LocalSix K T, s.subgroup < K ∧
      SolvableExclusion.IsTripleCoverSix (s.subgroup ⧸ pCore 2 s.subgroup) := by
  have ht := Chapter1.isSylowIn_iff.mp hT
  obtain ⟨B, hB, hn⟩ := exists_normalized_hexad H K T
    (le_normalizer_of_normal_subgroupOf hKH) ht.2.1 ht.1 e
  exact ⟨localSix_hexad H K T hH hKH hT e hc hB hn,
    hexadResidualIn_lt K e hB, hexadResidualIn_isTripleCoverSix K e hc hB⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
