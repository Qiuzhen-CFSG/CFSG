module
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Full movement under a normal subgroup with prime-group quotient

If V is a normal p-subgroup of a finite group A and [V,A]=V, every normal
subgroup K with A/K a p-group also satisfies [V,K]=V. A Sylow p-subgroup
supplements K; nilpotent saturation removes its commutator supplement.
The relative version retains the embedding in an arbitrary ambient group.

Consequently, if [V,Q] is nontrivial and fixed by A, a normal K for which
[Q,K] centralizes V cannot have p-group quotient. Three-subgroups rotation
would otherwise make [V,K]=V centralize Q. This detects the odd action on
the literal second-kernel layer in DGS85 (12.6), printed p.183, including
the binary Suzuki actor.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Full movement survives restriction to a normal subgroup with p-group quotient. -/
theorem commutator_eq_self_of_normal_prime_quotient (V K : Subgroup G) [V.Normal] [K.Normal]
    (hp : IsPGroup p V) (hquot : IsPGroup p (G ⧸ K))
    (hfull : ⁅V, (⊤ : Subgroup G)⁆ = V) : ⁅V,K⁆ = V := by
  let T : Sylow p G := Classical.choice inferInstance
  have hgen : K ⊔ (T : Subgroup G) = ⊤ := by
    rw [sup_comm]
    exact T.sup_eq_top_of_quotient_isPGroup K hquot
  let H := ⁅V,K⁆
  let C := H ⊔ ⁅V,(T : Subgroup G)⁆
  have hHV : H ≤ V := commutator_le_left _ _
  have hCV : C ≤ V := sup_le hHV (commutator_le_left _ _)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf le_normalizer_of_normal (normalizer_commutator_ge_right V (T : Subgroup G))).trans
      (normalizer_inf_normalizer_le_normalizer_sup H ⁅V,(T : Subgroup G)⁆)
  have hKC : K ≤ normalizer (C : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr ((commutator_mono hCV le_rfl).trans le_sup_left)
  have hC : (⊤ : Subgroup G) ≤ normalizer (C : Set G) := by
    rw [←hgen]
    exact sup_le hKC hTC
  have hcover : V ≤ H ⊔ ⁅V,(T : Subgroup G)⁆ := by
    calc
      V = ⁅V,(⊤ : Subgroup G)⁆ := hfull.symm
      _ = ⁅K ⊔ (T : Subgroup G),V⁆ := by rw [←hgen,commutator_comm]
      _ ≤ C := commutator_sup_le_of_relative_normal ⊤ K (T : Subgroup G) V C hC le_top le_top
        (by rw [commutator_comm]; exact le_sup_left)
        (by rw [commutator_comm]; exact le_sup_right)
  exact le_antisymm hHV (le_of_le_sup_commutator_of_isPGroup V H (T : Subgroup G)
    hp T.isPGroup' hHV le_normalizer_of_normal le_normalizer_of_normal hcover)
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- The same movement identity with the actual ambient inclusion retained. -/
theorem commutator_eq_self_of_relative_normal_prime_quotient (A V : Subgroup G) [Finite A]
    (hVA : V ≤ A) (hn : A ≤ normalizer (V : Set G))
    (K : Subgroup A) [K.Normal]
    (hp : IsPGroup p V) (hquot : IsPGroup p (A ⧸ K))
    (hfull : ⁅V,A⁆ = V) : ⁅V,K.map A.subtype⁆ = V := by
  let W := V.subgroupOf A
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  have hfullW : ⁅W,(⊤ : Subgroup A)⁆ = W := by
    apply map_injective A.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVA,
      ← MonoidHom.range_eq_map, range_subtype, hfull]
  have hh := congrArg (Subgroup.map A.subtype)
    (commutator_eq_self_of_normal_prime_quotient W K hp.comap_subtype hquot hfullW)
  rwa [map_commutator, map_subgroupOf_eq_of_le hVA] at hh

/-- A kernel centralizing the reciprocal action cannot leave a p-group quotient. -/
theorem not_isPGroup_quotient_of_reciprocal_centralizer (A V Q Z : Subgroup G) [Finite A]
    (hVA : V ≤ A) (hn : A ≤ normalizer (V : Set G))
    (hp : IsPGroup p V) (hfull : ⁅V,A⁆ = V)
    (hcomm : ⁅V,Q⁆ ≤ Z) (hcentral : Z ≤ centralizer (A : Set G))
    (hmove : ⁅V,Q⁆ ≠ ⊥)
    (K : Subgroup A) [K.Normal]
    (hker : ⁅Q,K.map A.subtype⁆ ≤ centralizer (V : Set G)) :
    ¬ IsPGroup p (A ⧸ K) := by
  intro hk
  have hVK := commutator_eq_self_of_relative_normal_prime_quotient A V hVA hn K hp hk hfull
  have h1 : ⁅⁅K.map A.subtype,Q⁆,V⁆ = ⊥ := by
    rw [commutator_comm (K.map A.subtype) Q]
    exact commutator_eq_bot_iff_le_centralizer.mpr hker
  have h2 : ⁅⁅Q,V⁆,K.map A.subtype⁆ = ⊥ := by
    rw [commutator_comm Q V]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hcomm.trans (hcentral.trans (centralizer_le (map_subtype_le K))))
  have h3 : ⁅⁅V,K.map A.subtype⁆,Q⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hVK] at h3
  exact hmove h3
end Subgroup
