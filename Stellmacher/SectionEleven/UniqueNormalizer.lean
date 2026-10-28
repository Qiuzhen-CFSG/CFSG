module

public import Stellmacher.LaterDefs
public import Theory.GroupTheory.SymmetricFourCoreOvergroup

/-!
# The two-core normalizer in the unique-maximal branch

For a Hypothesis Two pair with S strictly smaller than the ambient Sylow
two-subgroup, suppose P1 is isomorphic to S4 or C2 × S4. Then P1 is the
normalizer of its ambient two-core Q. The model is an explicit hypothesis;
this module does not depend on the classification theorem (8.2).

Clause (5.1)(c2) puts S in Syl₂(N), where N = N_H(Q). The nontriviality
of Q makes N two-local, and the Baumann subgroup lies in S, so local_B
gives solvability and characteristic two for N. Now O₂(N) lies in S ≤ P1
and is normal in P1, hence lies in Q. Consequently an element of C_H(Q)
belongs to N and centralizes O₂(N); characteristic two puts it in O₂(N) ≤ Q.
This proves the exact centralizer bound needed by the imported small-model
normalizer rigidity theorem, which concludes N = P1. In particular, neither
normality of P1 in N nor equality of their two-cores is assumed.

This supplies the normalizer identification before cases (I) and (II) in
Stellmacher Section 11, `refs/latex/stellmacher-n-group.tex`, lines 2076–2081.
The terminal calculations consume the resulting equality without further
classification assumptions.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven Later

universe u

variable {H : Type u} [Group H]

private theorem core_le (P : Subgroup H) : twoCoreIn P ≤ P :=
  Subgroup.map_subtype_le _

private theorem le_core_normalizer (P : Subgroup H) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set H) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (core_le P)).mp
  change (Subgroup.comap P.subtype ((pCore 2 P).map P.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

private theorem normal_two_le_core (Q P : Subgroup H)
    (hQP : Q ≤ P) (hQp : IsPGroup 2 Q)
    (hQnormal : (Q.subgroupOf P).Normal) : Q ≤ twoCoreIn P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle

private theorem normalizer_sylow [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) (hne : S ≠ (S0 : Subgroup H)) :
    IsSylowTwoIn S (Subgroup.normalizer (twoCoreIn P1 : Set H)) := by
  cases h.fiveOne.alternative with
  | a heq _ _ => exact (hne heq).elim
  | b heq _ => exact (hne heq).elim
  | c _ _ _ _ _ _ _ _ _ hSylow _ _ _ => exact hSylow

private theorem normalizer_control [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) (hne : S ≠ (S0 : Subgroup H)) :
    Group.IsSolvable (Subgroup.normalizer (twoCoreIn P1 : Set H)) ∧
      Subgroup.centralizer (twoCoreIn P1 : Set H) ≤ twoCoreIn P1 := by
  let Q := twoCoreIn P1
  let N := Subgroup.normalizer (Q : Set H)
  have hPN : P1 ≤ N := le_core_normalizer P1
  have hSylow : IsSylowTwoIn S N := normalizer_sylow h hne
  have hlocal : IsTwoLocal N :=
    ⟨Q, h.fiveOne.P1_mem.1.2.2.1,
      (pCore_isPGroup (p := 2) (G := P1)).map P1.subtype, rfl⟩
  obtain ⟨hsolv, hchar⟩ := h.local_B N hlocal (inf_le_left.trans hSylow.1)
  refine ⟨hsolv, ?_⟩
  have hcoreNS : twoCoreIn N ≤ S := by
    obtain ⟨T, hT⟩ := hSylow.2
    rw [← hT]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := N)).le_sylow_of_normal T)
  have hcoreNP : twoCoreIn N ≤ P1 := hcoreNS.trans h.fiveOne.P1_mem.1.2.1.1
  have hcoreNQ : twoCoreIn N ≤ Q := normal_two_le_core _ P1 hcoreNP
    ((pCore_isPGroup (p := 2) (G := N)).map N.subtype)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hcoreNP).mpr
      (hPN.trans (le_core_normalizer N)))
  intro x hx
  have hxN : x ∈ N := Subgroup.centralizer_le_normalizer (Q : Set H) hx
  let xN : N := ⟨x, hxN⟩
  have hxcent : xN ∈ Subgroup.centralizer (pCore 2 N : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (y : H)
      (hcoreNQ (Subgroup.mem_map_of_mem N.subtype hy)))
  exact hcoreNQ (Subgroup.mem_map_of_mem N.subtype (hchar hxcent))

public theorem unique_normalizer [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) (hne : S ≠ (S0 : Subgroup H))
    (hModel : IsModel P1 S4 ∨ IsModel P1 (C2 × S4)) :
    Subgroup.normalizer (twoCoreIn P1 : Set H) = P1 := by
  obtain ⟨hsolv, hcent⟩ := normalizer_control h hne
  apply normalizer_twoCore_eq_of_symmetric_four_model P1 hsolv hcent
  · obtain ⟨T, hT⟩ := (normalizer_sylow h hne).2
    exact ⟨T, hT.le.trans h.fiveOne.P1_mem.1.2.1.1⟩
  · exact hModel

end Stellmacher.SectionEleven
