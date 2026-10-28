module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.Contracts

/-!
# Alternating factors in the envelope centralizer

For an alternating factor, E.6.7 gives a fixed hyperplane in V. If U
does not centralize that factor, U and this fixed hyperplane generate V.
Consequently the centralizer of U in the factor already centralizes V
and lies in M. This proves the alternating-factor part of the remaining
centralizer geometry without identifying its module with the natural
L₂(4) module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7(2),
printed p.246, used in E.6.23 on printed p.254.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
open InvariantSubspaces.BlockSelection

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sup_eq_of_index_two {F U V : Subgroup G}
    (hFV : F ≤ V) (hUV : U ≤ V) (hindex : F.relIndex V = 2) (hne : ¬ U ≤ F) :
    U ⊔ F = V := by
  have hsV : U ⊔ F ≤ V := sup_le hUV hFV
  have ht := relIndex_mul_relIndex F (U ⊔ F) V le_sup_right hsV
  rw [hindex] at ht
  have hd : F.relIndex (U ⊔ F) ∣ 2 := ⟨(U ⊔ F).relIndex V, ht.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact (hne (le_sup_left.trans (relIndex_eq_one.mp h1))).elim
  · rw [h2] at ht
    have hindex' : (U ⊔ F).relIndex V = 1 := by omega
    exact le_antisymm hsV (relIndex_eq_one.mp hindex')

/-- Every alternating factor moved by U has its U-centralizer already
inside C_G(V), and hence inside M. The rank-one conclusion used here is
the actual ambient conclusion of E.6.7(2). -/
theorem alternating_factor_centralizer_le
    {K : GroupClass} {T : Sylow 2 G} {M V A R U : Subgroup G}
    (h : HypothesisE61 K T M V)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A R)
    (hUV : U ≤ V) (i : Fin d.count) (n : ℕ)
    (ha : ChapterC.IsAlternatingBlock (d.block i) n)
    (hmoved : ¬ d.block i ≤ centralizer (U : Set G)) :
    d.block i ⊓ centralizer (U : Set G) ≤ centralizer (V : Set G) ∧
      d.block i ⊓ centralizer (U : Set G) ≤ M := by
  let _ := h.elementary
  let F := V ⊓ centralizer (d.block i : Set G)
  have hi : F.relIndex V = 2 := by
    calc
      F.relIndex V = 2 ^ subgroupCorank V F := by
        rw [subgroupCorank_eq_quotient_finrank]
        exact Subgroup.relIndex_eq_two_pow_quotient_finrank V F
      _ = 2 := by rw [(d.alternating i n ha).1]; rfl
  have hne : ¬ U ≤ F := fun he => hmoved (le_centralizer_iff.mpr (he.trans inf_le_right))
  have hgen : U ⊔ F = V := sup_eq_of_index_two inf_le_left hUV hi hne
  have hz : d.block i ⊓ centralizer (U : Set G) ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    apply hgen.ge.trans
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (inf_le_right.trans (Subgroup.centralizer_le inf_le_left))
  exact ⟨hz, hz.trans h.centralizer_le⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
