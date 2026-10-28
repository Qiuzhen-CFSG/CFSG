module

public import Glauberman.SylowAutomorphisms.NormalComplement.ComplementObstruction
public import Glauberman.SylowAutomorphisms.NormalComplement.FusionGeometry
public import Glauberman.SylowAutomorphisms.NormalComplement.OddActor
public import Theory.GroupAction.NormalComplement
public import Theory.GroupTheory.ZStar.SylowAutomorphismAction

/-!
# The normal odd complement in a Sylow pointwise fixer

Burnside transfer reduces the normal-complement conclusion to centrality of
the Sylow subgroup in its normalizer. The source argument contradicts failure
of that centrality by constructing an odd-actor displacement subgroup and
excluding it through Z-star, central-involution fusion and Lemma 4.

The imported modules construct the nonzero elementary displacement subgroup,
prove Lemma 4 by averaging over the Sylow index, and exclude displacement
through the actual semidirect-product fusion geometry. Combining them gives
a normal odd complement in the pointwise automorphism fixer of S whenever
the ambient group has trivial odd core. Only central-involution fusion and
the abelian-Sylow input from part (a) remain explicit; the parent theorem
supplies these independent source inputs.

Source: Glauberman, Math. Z. 93 (1966), Theorem 1(b), p.158 and Lemmas 3–4,
pp.156–157, DOI 10.1007/BF01111033.
-/

public section

namespace Glauberman.SylowAutomorphisms.NormalComplement
open Subgroup

universe u

/-- Burnside transfer after construction and exclusion of an odd displacement
subgroup. Each displayed input is a separate source proof obligation. -/
theorem normalComplement_of_displacement_inputs
    {A : Type*} [Group A]
    [Finite A] (P : Sylow 2 A)
    (construct : ¬ normalizer (P : Set A) ≤ centralizer (P : Set A) →
      Nonempty (OddDisplacement A))
    (exclude : OddDisplacement A → False) : HasNormalPComplement 2 A := by
  have hNC : normalizer (P : Set A) ≤ centralizer (P : Set A) := by
    by_contra hn
    obtain ⟨d⟩ := construct hn
    exact exclude d
  apply exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer 2 P
  intro a ha
  refine ⟨(P : Subgroup A).le_normalizer ha, ?_⟩
  intro b hb
  exact (Subgroup.mem_centralizer_iff.mp (hNC hb) a ha).symm

/-- Glauberman's Theorem 1(b), with central-involution fusion and the
abelian-Sylow conclusion of part (a) explicit. The normalizer construction
and its fusion exclusion are both discharged here. -/
theorem fixingSubgroup_normalComplement_of_abelian_sylows
    (fusion : SylowCentralFusion.CentralInvolutionFusion.{u})
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (abelian : ∀ P : Sylow 2 (fixingSubgroup (MulAut G) (S : Set G)),
      IsMulCommutative P) :
    HasNormalPComplement 2 (fixingSubgroup (MulAut G) (S : Set G)) := by
  let P : Sylow 2 (fixingSubgroup (MulAut G) (S : Set G)) :=
    Classical.choice inferInstance
  apply normalComplement_of_displacement_inputs P _
    (fixingSubgroup_no_oddDisplacement fusion hcore S)
  intro hnot
  obtain ⟨d, _, _⟩ := exists_oddDisplacement_of_not_normalizer_le_centralizer
    P (abelian P) hnot
  exact ⟨d⟩

end Glauberman.SylowAutomorphisms.NormalComplement
