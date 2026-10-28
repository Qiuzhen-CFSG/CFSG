module
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.WreathTwoElementaryCard
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Residual normality in subgroups of the binary-plane wreath group

An injective map into SL₂(2) wreath C₂ bounds elementary two-subgroups by
four and places the two-residual in the abelian cubic base. Consequently a
two-perfect subgroup normalized by a Sylow two-subgroup is normal: the
ambient two-residual centralizes it and the Sylow subgroup supplements that
residual. The HS source application uses this for its actual dotted L₁.

Source: Aschbacher--Smith, 14.3.23 and 14.3.32, pp.1000,1004.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.WreathTwoResidual
variable {D : Type*} [Group D] [Finite D]

/-- The dihedral Sylow model bounds every faithfully embedded actor. -/
theorem rank_le_two_of_injective (f : D →* Actor) (hf : Function.Injective f) :
    primeRank 2 D ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le D).mpr
  intro A hA
  let := hA
  have h := wreath_two_elementary_subgroup_card_le_four (A.map f)
    (IsElementaryAbelian.map (A := A) f)
  rw [card_map_of_injective hf] at h
  exact h

omit [Finite D] in
/-- The two-residual embeds in the concrete abelian cubic base. -/
theorem residual_commutative_of_injective (f : D →* Actor) (hf : Function.Injective f) :
    IsMulCommutative (pResidual 2 D) := by
  obtain ⟨e⟩ := residual_equiv_elementaryNine
  let : IsMulCommutative (pResidual 2 Actor) :=
    ⟨⟨fun a b => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  have hle := map_pResidual_le 2 f
  refine ⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩
  exact (map_mul f (a : D) (b : D)).trans ((congrArg Subtype.val
    (mul_comm (⟨f (a : D), hle (mem_map_of_mem f a.property)⟩ : pResidual 2 Actor)
      ⟨f (b : D), hle (mem_map_of_mem f b.property)⟩)).trans
        (map_mul f (b : D) (a : D)).symm)

/-- Sylow normalization suffices for a two-perfect subgroup in this wreath group. -/
theorem normal_of_injective_of_twoPerfect (f : D →* Actor) (hf : Function.Injective f)
    (S : Sylow 2 D) (N : Subgroup D) (hp : IsPPerfect 2 N)
    (hn : (S : Subgroup D) ≤ normalizer (N : Set D)) : N.Normal := by
  let := residual_commutative_of_injective f hf
  have hN : N ≤ pResidual 2 D := by
    intro x hx
    apply map_pResidual_le 2 N.subtype
    exact ⟨⟨x, hx⟩, by rw [(pResidual_eq_top_iff 2 N).mpr hp]; trivial, rfl⟩
  have hC : pResidual 2 D ≤ centralizer (N : Set D) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hN hy⟩ : pResidual 2 D) ⟨x, hx⟩)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top S]
  exact sup_le (hC.trans (centralizer_le_normalizer _)) hn

end Theory.GroupTheory.WreathTwoResidual
