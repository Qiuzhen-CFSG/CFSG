module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.NaturalTwo

/-!
# Excluding the centralizing one-factor case of 13.8.5

Suppose the normal closure of the given transvection is the natural
SL₂(2) factor and commutes with L₁*. Its natural moved space is fixed by
L₁*, so [Ũ_H,L₁] is fixed by the normal closure. The earlier source identity
V₃=[V₃,L₁] puts the actual seed in this fixed space. Its H*-orbit spans
Ũ_H by the definition of U_H, and normality propagates fixedness through
that orbit. The source centralizer bound makes the action faithful,
contradicting the nonidentity transvection.

This proves the last case on printed p.948. It does not assert the preceding
S₃-factor decomposition, the s=2 obstruction, or the s=1 residual alternatives.
Their assembly owner must construct the natural-factor and commuting witnesses.
No fixed-seed or orbit-spanning assertion is an input to the final theorem.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, Lemma 13.8.5, pp.947–948 (PDF pp.964–965).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : IsConjugation H V₃ V₁ ρ)
include hρ

/-- In the centralizing one-factor case the actual V₃ seed is fixed. -/
theorem seed_fixed_of_naturalTwo (L₁ : Subgroup G) (hL : L₁ ≤ H)
    (hgen : V₃ = ⁅V₃, L₁⁆) (K : Subgroup (Source.Hstar H)) [K.Normal]
    (d : NaturalTwo ρ K)
    (hcomm : ∀ l ∈ Source.starImage H L₁, ∀ k ∈ K, Commute l k)
    (k : K) (v : V₃) : ρ k (seedVector H V₃ V₁ v) = seedVector H V₃ V₁ v := by
  exact commutator_le_fixed_of_naturalTwo ρ K d (Source.starImage H L₁) hcomm
    (seed_mem_commutator ρ hρ L₁ hL hgen v) k

/-- The centralizing one-factor normal closure in 13.8.5 is trivial.
The action is the literal H/O₂(H)-action on U_H/V₁. Its faithfulness,
the fixedness of the seed and the spanning orbit are all derived here. -/
theorem centralizing_normalClosure_eq_one
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hgen : V₃ = ⁅V₃, L₁⁆)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (t : Source.Hstar H)
    (d : NaturalTwo ρ (normalClosure ({t} : Set (Source.Hstar H))))
    (hcomm : ∀ l ∈ Source.starImage H L₁,
      ∀ k ∈ normalClosure ({t} : Set (Source.Hstar H)), Commute l k) : t = 1 := by
  have hbot := normal_eq_bot_of_seed_fixed ρ hρ hcentralizer
    (normalClosure ({t} : Set (Source.Hstar H))) (by
      intro k hk v
      exact seed_fixed_of_naturalTwo ρ hρ L₁ hL hgen _ d hcomm ⟨k, hk⟩ v)
  have ht : t ∈ normalClosure ({t} : Set (Source.Hstar H)) :=
    subset_normalClosure (Set.mem_singleton t)
  rwa [hbot, mem_bot] at ht

/-- No nonidentity actor, in particular no transvection, can lie in this
centralizing normal-closure case. -/
theorem centralizing_normalClosure_impossible
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hgen : V₃ = ⁅V₃, L₁⁆)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (t : Source.Hstar H) (ht : t ≠ 1)
    (d : NaturalTwo ρ (normalClosure ({t} : Set (Source.Hstar H))))
    (hcomm : ∀ l ∈ Source.starImage H L₁,
      ∀ k ∈ normalClosure ({t} : Set (Source.Hstar H)), Commute l k) : False :=
  ht (centralizing_normalClosure_eq_one ρ hρ L₁ hL hgen hcentralizer t d hcomm)

/-- The remaining centralizing S₃ case is impossible for the actual
transvection. The natural moved-space witness and commuting alternative
are the outputs still required from the solvable-factor case analysis. -/
theorem centralizing_transvection_impossible
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hgen : V₃ = ⁅V₃, L₁⁆)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (d : NaturalTwo ρ (normalClosure ({t} : Set (Source.Hstar H))))
    (hcomm : ∀ l ∈ Source.starImage H L₁,
      ∀ k ∈ normalClosure ({t} : Set (Source.Hstar H)), Commute l k) : False :=
  centralizing_normalClosure_impossible ρ hρ L₁ hL hgen hcentralizer t ht.ne_one d hcomm

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

end
