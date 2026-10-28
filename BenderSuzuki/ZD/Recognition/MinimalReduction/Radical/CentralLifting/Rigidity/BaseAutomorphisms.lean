module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Linear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Suzuki

/-!
# Automorphism centralizers of Sylow subgroups in the exceptional bases

For the actual matrix groups PSL₂(4) and Sz(8), every automorphism fixing a
Sylow 2-subgroup pointwise is conjugation by an element of that same Sylow
subgroup. The imported calculations establish this for the standard root
subgroups using the actual inner-field actions. Sylow conjugacy transports
both pointwise fixation and the location of the conjugating element.

These are precisely the quotient automorphism inputs from GLS, Volume 3,
Theorem 2.6.5(e), needed in Volume 4, Chapter 4, Lemma 2.8(c). No restriction
on the order of the automorphism is imposed. Perfect-cover descent and the
Sylow-center calculations are separate inputs to the cover rigidity proof.
-/

namespace BenderSuzuki.ZD.BaseAutomorphisms
open Converse Linear _root_.BenderSuzuki.MatrixGroups
open scoped Pointwise

private theorem fixing_inner_map {G : Type*} [Group G] (U : Subgroup G)
    (hU : ∀ β : MulAut G, (∀ x ∈ U, β x = x) → ∃ x ∈ U, β = MulAut.conj x)
    (e β : MulAut G) (hfix : ∀ x ∈ U.map e.toMonoidHom, β x = x) :
    ∃ x ∈ U.map e.toMonoidHom, β = MulAut.conj x := by
  let γ := e⁻¹ * β * e
  have hγfix : ∀ x ∈ U, γ x = x := by
    intro x hx
    change e.symm (β (e x)) = x
    rw [hfix (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx), e.symm_apply_apply]
  obtain ⟨u, hu, hγ⟩ := hU γ hγfix
  refine ⟨e u, Subgroup.mem_map_of_mem e.toMonoidHom hu, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have he := congrArg (fun f : MulAut G => e (f x)) hγ
  change e (e.symm (β (e x))) = e (u * x * u⁻¹) at he
  simpa only [e.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply] using he

private theorem fixing_inner_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P Q : Sylow p G)
    (hP : ∀ β : MulAut G, (∀ x ∈ P, β x = x) → ∃ x ∈ P, β = MulAut.conj x)
    (β : MulAut G) (hfix : ∀ x ∈ Q, β x = x) :
    ∃ x ∈ Q, β = MulAut.conj x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hm : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = Q :=
    congrArg (fun R : Sylow p G => (R : Subgroup G)) hg
  change ∀ x ∈ (Q : Subgroup G), β x = x at hfix
  change ∃ x ∈ (Q : Subgroup G), β = MulAut.conj x
  have he := fixing_inner_map (P : Subgroup G) hP (MulAut.conj g) β
    (by simpa only [hm] using hfix)
  simpa only [hm] using he

private theorem psl2_standard_sylow (K : Type*) [Field K] [Finite K] [CharP K 2] :
    ∃ P : Sylow 2 (PSL2MatrixGroup K), (P : Subgroup _) = PUnip K := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  refine ⟨U.mapSurjective (f := pi K) pi_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective]
  change (Matrix.SpecialLinearGroup.upperUnipotent K).map (pi K) = (Unip K).map (pi K)
  congr 1
  ext g
  rw [Matrix.SpecialLinearGroup.mem_upperUnipotent, mem_Unip_iff]
  simp only [upper_transvection_eq_uni, eq_comm]

/-- The PSL₂(4) quotient input to double-cover rigidity: the conjugating
matrix lies in the given Sylow subgroup. -/
public theorem psl2_four_aut_fixing_sylow_inner
    (Q : Sylow 2 (PSL2BinaryMatrixGroup 2))
    (β : MulAut (PSL2BinaryMatrixGroup 2))
    (hfix : ∀ b ∈ Q, β b = b) :
    ∃ b ∈ Q, β = MulAut.conj b := by
  obtain ⟨P, hP⟩ := psl2_standard_sylow (PFAppendixIII.BinaryGaloisField 2)
  apply fixing_inner_sylow P Q _ β hfix
  intro α hα
  change ∀ b ∈ (P : Subgroup _), α b = b at hα
  change ∃ b ∈ (P : Subgroup _), α = MulAut.conj b
  rw [hP] at hα ⊢
  exact psl2_aut_fixing_unipotent_inner α hα

/-- The Sz(8) quotient input to double-cover rigidity: the conjugating
matrix lies in the given Sylow subgroup. -/
public theorem suzuki_eight_aut_fixing_sylow_inner
    (Q : Sylow 2 (SuzukiMatrixGroup 1))
    (β : MulAut (SuzukiMatrixGroup 1))
    (hfix : ∀ b ∈ Q, β b = b) :
    ∃ b ∈ Q, β = MulAut.conj b := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow 1 (by decide)
  apply fixing_inner_sylow P Q _ β hfix
  intro α hα
  change ∀ b ∈ (P : Subgroup _), α b = b at hα
  change ∃ b ∈ (P : Subgroup _), α = MulAut.conj b
  rw [hP] at hα ⊢
  exact suzuki_aut_fixing_root_inner 1 (by decide) α hα

end BenderSuzuki.ZD.BaseAutomorphisms
