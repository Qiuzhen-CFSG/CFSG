module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Centralizing
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Choices
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Quasithin.Rank

/-!
# Rank and natural-space consequences of the actual B.1.8 factors

The product of order-three Sylow subgroups in the independent SL₂(2)
factors embeds an elementary abelian group of order 3^s. Thus s is at most
the three-rank. For a subgroup of H/O₂(H), the odd-rank quotient theorem
gives 1 ≤ s ≤ 2 from m₃(H) ≤ 2.

When the offender subgroup is the whole normal closure and s=1, its unique
factor is the whole group. Transport through the literal subgroup inclusion
identifies its moved space with the ambient moved space and constructs the
`NaturalTwo` witness, including equivariance. These results do not assume or
establish the marked local exclusions for s=2 or the one-factor residual
alternatives.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the proof
of 13.8.5, printed pp.947–948 (PDF pp.964–965).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable
open ChapterB
variable {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E}

omit [Finite A] in
/-- The concrete symmetric-group model, through its action on the three
nonzero binary vectors. -/
noncomputable def factorSymmetricModel (d : SolvableFFFactors ρ) (i : Fin d.count) :
    d.factor i ≃* Equiv.Perm (Fin 3) :=
  (d.factorModel i).trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)

theorem factor_count_le_threeRank (d : SolvableFFFactors ρ) : d.count ≤ primeRank 3 A := by
  classical
  let P (i : Fin d.count) : Sylow 3 (d.factor i) := Classical.choice inferInstance
  let C (i : Fin d.count) : Subgroup (d.factor i) := P i
  have hc (i : Fin d.count) : Nat.card (C i) = 3 := by
    change Nat.card (P i) = 3
    rw [(P i).card_eq_multiplicity, d.factor_card]
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization, Nat.prime_three.factorization]
    norm_num
  let (i : Fin d.count) : IsCyclic (C i) := isCyclic_of_prime_card (hc i)
  let (i : Fin d.count) : CommGroup (C i) := IsCyclic.commGroup
  let f : ((i : Fin d.count) → C i) →* A :=
    d.productInclusion.comp
      { toFun x i := (x i : d.factor i)
        map_one' := rfl
        map_mul' _ _ := rfl }
  apply primeRank_ge_of_elementary_embedding (f := f)
  · intro x
    funext i
    change x i ^ 3 = 1
    have hp := pow_card_eq_one' (x := x i)
    rwa [hc i] at hp
  · rw [Nat.card_pi]
    simp_rw [hc]
    simp
  · intro x y h
    have he := d.productInclusion_injective h
    funext i
    exact Subtype.ext (congrFun he i)

theorem factor_count_le_two (H : Subgroup A)
    (σ : Representation (ZMod 2) (Source.Hstar H) E)
    (K : Subgroup (Source.Hstar H))
    (d : SolvableFFFactors (σ.comp K.subtype)) (hrank : primeRank 3 H ≤ 2) :
    1 ≤ d.count ∧ d.count ≤ 2 := by
  refine ⟨d.count_pos, (factor_count_le_threeRank d).trans ?_⟩
  exact (primeRank_subgroup_le 3 K).trans
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide)
      (pCore 2 H) pCore_isPGroup).trans hrank)

omit [Finite A] in
theorem factor_eq_top_of_count_one (d : SolvableFFFactors ρ)
    (hJ : offenderSubgroup ρ = ⊤) (hc : d.count = 1) :
    d.factor ⟨0, d.count_pos⟩ = ⊤ := by
  rw [← hJ, ← d.iSup_factor]
  apply le_antisymm (le_iSup _ _)
  apply iSup_le
  intro i
  have he : i = (⟨0, d.count_pos⟩ : Fin d.count) := by
    apply Fin.ext
    have := i.isLt
    omega
  rw [he]

omit [Finite A] in
theorem movedSpace_restrict_top (K : Subgroup A) :
    subspaceCommutator (ρ.comp K.subtype) ⊤ ⊤ = subspaceCommutator ρ ⊤ K := by
  unfold subspaceCommutator
  congr 1
  ext w
  constructor
  · rintro ⟨k, _, v, _, rfl⟩
    exact ⟨k, k.property, v, Submodule.mem_top, rfl⟩
  · rintro ⟨k, hk, v, _, rfl⟩
    exact ⟨⟨k, hk⟩, Subgroup.mem_top _, v, Submodule.mem_top, rfl⟩

omit [Finite A] in
noncomputable def naturalTwo_of_count_one (K : Subgroup A) [K.Normal]
    (d : SolvableFFFactors (ρ.comp K.subtype))
    (hJ : offenderSubgroup (ρ.comp K.subtype) = ⊤) (hc : d.count = 1) :
    NaturalTwo ρ K := by
  let i : Fin d.count := ⟨0, d.count_pos⟩
  have hi : d.factor i = ⊤ := factor_eq_top_of_count_one d hJ hc
  let e : d.factor i ≃* K := (MulEquiv.subgroupCongr hi).trans (Subgroup.topEquiv)
  have hW : subspaceCommutator (ρ.comp K.subtype) ⊤ (d.factor i) =
      subspaceCommutator ρ ⊤ K := by
    rw [hi, movedSpace_restrict_top]
  let c := LinearEquiv.ofEq _ _ hW.symm
  refine ⟨e.symm.trans (d.factorModel i), c.trans (d.naturalEquiv i), ?_⟩
  intro k w
  apply (d.naturalEquiv i).symm.injective
  change (d.naturalEquiv i).symm (d.naturalEquiv i (c (movedRepresentation ρ K k w))) = _
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact d.naturalEquiv_action i (e.symm k) (c w)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable

end
