module
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer.Representatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
/-!
# All abstract HS automorphisms act on the defining 100 points

The two stabilizer generators have only one common fixed point. Transitivity
then makes the permutation centralizer trivial, so the already proved
surjectivity of the normalizer action gives the full automorphism equivalence.
In particular every outer involution lifts to an actual permutation involution.

Adapted from CFSG Chapter16 OtherPreliminaries/JankoTwoHigmanSims/HSOuter.lean,
preserving the original. Source: Aschbacher–Smith 16.1.5(10), p.1172;
ATLAS HSG1-p100B0, with original attribution in LICENSES/ATLAS.txt.
-/
public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.OrderCertificate

set_option maxRecDepth 20000

private theorem stabilizer_common_fixed :
    ∀ x : Fin 100, p2 x = x → p3 x = x → x = 0 := by
  decide +kernel

/-- No nonidentity permutation centralizes the exact degree-100 HS carrier. -/
theorem permutation_centralizer_eq_bot :
    centralizer (generated : Set (Equiv.Perm (Fin 100))) = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  have hcomm (g : Carrier) (x : Fin 100) : g.val (c x) = c (g.val x) :=
    congrArg (fun p : Equiv.Perm (Fin 100) => p x)
      (mem_centralizer_iff.mp hc g.val g.property)
  have hfix (i : Fin 17) : gen1 i (c 0) = c 0 := by
    have hm : gen1 i ∈ H1 := ⟨[i], mul_one _⟩
    have hg : gen1 i ∈ generated := NormalizerIndex.H0_eq_generated ▸ H1_le hm
    exact (hcomm ⟨gen1 i, hg⟩ 0).trans (congrArg c (next0_fix ⟨_, hm⟩))
  have hc0 : c 0 = 0 := stabilizer_common_fixed (c 0) (hfix 0) (hfix 1)
  apply mem_bot.mpr
  apply Equiv.ext
  intro x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier (0 : Fin 100) x
  change g.val 0 = x at hg
  change c x = x
  rw [← hg, ← hcomm, hc0]

/-- The full permutation normalizer acts faithfully on the exact HS carrier. -/
theorem normalizer_action_injective : Function.Injective generated.normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [normalizerMonoidHom_ker, permutation_centralizer_eq_bot]
  simp

/-- The actual permutation normalizer is the full abstract automorphism group. -/
noncomputable def fullAutomorphismEquiv :
    normalizer (generated : Set (Equiv.Perm (Fin 100))) ≃* MulAut Carrier :=
  MulEquiv.ofBijective generated.normalizerMonoidHom
    ⟨normalizer_action_injective,
      normalizer_surjective_of_pointStabilizer_map pointStabilizer_map⟩

/-- Fixed points of the induced automorphism are the centralizer inside HS. -/
theorem fixedSubgroup_eq_permutationCentralizer
    (n : normalizer (generated : Set (Equiv.Perm (Fin 100)))) :
    (generated.normalizerMonoidHom n).fixedSubgroup = permutationCentralizer n.val := by
  ext x
  rw [MulAut.mem_fixedSubgroup]
  change (⟨n.val * x.val * n.val⁻¹, _⟩ : Carrier) = x ↔
    x.val ∈ centralizer ({n.val} : Set (Equiv.Perm (Fin 100)))
  rw [Subtype.ext_iff, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

/-- Every abstract outer involution comes from a genuine permutation involution. -/
theorem outer_involution_lift (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) :
    ∃ n : normalizer (generated : Set (Equiv.Perm (Fin 100))),
      generated.normalizerMonoidHom n = r ∧ orderOf n = 2 ∧ n.val ∉ generated := by
  obtain ⟨n, hn⟩ := fullAutomorphismEquiv.surjective r
  refine ⟨n, hn, (fullAutomorphismEquiv.orderOf_eq n).symm.trans (hn ▸ hr), ?_⟩
  intro hmem
  exact ho ⟨⟨n.val, hmem⟩, hn.symm⟩


end Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer
