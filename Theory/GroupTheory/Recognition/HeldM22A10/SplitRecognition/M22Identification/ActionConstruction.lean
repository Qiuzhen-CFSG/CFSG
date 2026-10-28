module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.CosetAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.IndexSubgroup

/-!
# Conditional assembly of Janko's degree-22 action

The local subgroup censuses and the genuine degree-21 character construct a
proper subgroup of index 22. Its left coset action is faithful and even, and
its character is `1 + chi`. Relabeling the cosets gives the exact fixed-point
counts on `Fin 22`. The normalizer elements are retained with Lean's left
conjugation convention.

The existence of the character, the actual local subgroups, and the compatible
normalizer elements remains to be proved. In particular, this module does not
yet construct `PermutationData G` from `D : LocalData G`, an equivalence
`D.centralizer ≃* CentralizerModels.m22Centralizer`, ambient order 443520,
and Sylow-three normalizer order 72 alone. The final assembly of those
source inputs belongs here once these three prerequisites are discharged.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, DOI 10.1016/0021-8693(68)90002-1,
Sections 7--8 and the start of Section 9, pp.15--17.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction

universe u

/-- Assemble the actual degree-22 action from the character and local subgroup
construction and compatible normalizer elements. This is a conditional theorem,
not the existence of those prerequisites from the local recognition hypotheses. -/
public noncomputable def permutationDataOfPrerequisites
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 443520) (C : Degree21Character G) (L : LocalConfiguration G)
    (ell m n : G) (hell : orderOf ell = 11) (hm : orderOf m = 5) (hn : orderOf n = 4)
    (hmell : m * ell * m⁻¹ = ell ^ 4) (hnm : n * m * n⁻¹ = m ^ 2) :
    PermutationData G where
  rho := cosetAction (L.X ⊔ L.Y) (L.generated_index C hcard)
  faithful := cosetAction_faithful (L.X ⊔ L.Y) (L.generated_index C hcard)
  even := even_of_simple (by rw [hcard]; decide) _
  order_fixed := cosetAction_order_fixed C (L.X ⊔ L.Y) (L.generated_index C hcard)
  ell := ell
  m := m
  n := n
  ell_order := hell
  m_order := hm
  n_order := hn
  m_conjugates_ell := hmell
  n_conjugates_m := hnm

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
