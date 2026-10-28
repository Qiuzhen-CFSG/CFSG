module

public import Stellmacher.SectionsOneToFourDefs
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Stellmacher.SectionOne.OneSevenOddCoreProduct
public import Stellmacher.SectionOne.OneSevenBaumann

/-!
# Stellmacher (1.7): the global offender structure

Under the faithful elementary-abelian action hypotheses of Section 1,
nontrivial J(V,S) has the stated Baumann, odd-core and SL₂(2) product
structure. The proved local classification in the range m≤1 supplies a
conjugacy-invariant family of small factors. Their global product is
normal, its Sylow intersection is an offender, and hence it identifies
with the normal closure E of J(V,S).

This assembly imports the odd-core splitting and the Baumann equality,
then enumerates the finite factor family by Fin n. Its internal group
product and four-element support decomposition give precisely part (c),
with the fixed space indexed separately by none. Only proved small-m
classification results are used in these dependencies.

Source: Stellmacher (1.7), journal p.19 of
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u

public structure LemmaOneSevenConclusion
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) : Prop where
  part_a :
    IsInternalDirectProductFamily (oddCore G)
      (fun i : Fin 2 =>
        if i = 0 then
          (commutator (↥(oneE (G := G) (V := V) S))).map
            (oneE (G := G) (V := V) S).subtype
        else
          oddCore G ⊓ Subgroup.centralizer
            (oneE (G := G) (V := V) S : Set G))
  part_b :
    oneB (G := G) (V := V) S = oneJ (G := G) (V := V) S ∧
      oneA (G := G) (V := V) S (oneJ (G := G) (V := V) S)
  part_c :
    ∃ (n : ℕ) (E : Fin n → Subgroup G) (Vf : Fin n → Subgroup V),
      IsInternalDirectProductFamily (oneE (G := G) (V := V) S) E ∧
      (∀ i : Fin n, IsSL2Two (↥(E i))) ∧
      (∀ i : Fin n, Vf i = commutatorAction (E i) V ∧ Nat.card (Vf i) = 4) ∧
      IsInternalDirectProductFamily (⊤ : Subgroup V)
        (fun i : Option (Fin n) =>
          match i with
          | none => FixedPoints.subgroup (oneE (G := G) (V := V) S) V
          | some i => Vf i)

/-- **Stellmacher (1.7).**  If `J(V,S) ≠ 1`, the Baumann subgroup and the
normal closure of `J(V,S)` have the direct-product structure stated in the
paper. -/
public theorem lemma_one_seven
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hJ : oneJ (G := G) (V := V) (S : Subgroup G) ≠ ⊥) :
    LemmaOneSevenConclusion (G := G) (V := V) (S : Subgroup G) := by
  classical
  by_cases hJbot : oneJ (V := V) (S : Subgroup G) = ⊥
  · exact (hJ hJbot).elim
  have hBJ := oneSeven_baumann_eq_j h S
  obtain ⟨hEnormal,hprod,hJE⟩ := oneSeven_global_product h S
  obtain ⟨hJid,hEid⟩ := oneSeven_global_identification h S
  let E₀ := oneSevenGenerated (G := G) (V := V)
  let F := oneSevenFactors (G := G) (V := V)
  change IsInternalDirectProduct E₀ F at hprod
  have hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D :=
    fun D hD => (mem_oneSevenFactors_iff D).mp hD
  have hA := oneSevenFactor_product_sylow_oneA h S E₀ hEnormal F hprod hF
  refine ⟨?_, ⟨hBJ, ?_⟩, ?_⟩
  · rw [hEid]
    exact oneSevenFactor_oddCore_product E₀ F hprod hF
  · rw [hJid]
    exact hA
  let I := {D : Subgroup G // D ∈ F}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup G := fun i => (eI i).val
  have hDi (i : Fin n) : D i ∈ F := (eI i).property
  have hinj : Function.Injective D := by
    intro i j hij
    exact eI.injective (Subtype.ext hij)
  have hgen : E₀ = ⨆ i : Fin n, D i := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro K
      obtain ⟨i,rfl⟩ := eI.surjective K
      exact le_iSup D i
    · apply iSup_le
      intro i
      exact le_iSup (fun K : I => (K : Subgroup G)) (eI i)
  have hfamily : IsInternalDirectProductFamily E₀ D := by
    refine ⟨hgen, ?_, ?_⟩
    · intro i j hij
      exact hprod.2.2.1 (D i) (hDi i) (D j) (hDi j) (fun heq => hij (hinj heq))
    · intro i j hij
      exact hprod.2.2.2 (D i) (hDi i) (D j) (hDi j) (fun heq => hij (hinj heq))
  refine ⟨n,D,(fun i => commutatorAction (D i) V), ?_, ?_, ?_, ?_⟩
  · rw [hEid]
    exact hfamily
  · exact fun i => (hF (D i) (hDi i)).1
  · exact fun i => ⟨rfl,(hF (D i) (hDi i)).2.2.1⟩
  · rw [hEid]
    exact oneSevenFactor_module_product h D (fun i => hF (D i) (hDi i)) hinj E₀ hgen

end Stellmacher.SectionOne
