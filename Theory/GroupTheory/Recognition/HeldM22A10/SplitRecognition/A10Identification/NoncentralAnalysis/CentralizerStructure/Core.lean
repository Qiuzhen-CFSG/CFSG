module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Sylow
public import Theory.PGroupCore

/-!
# The intermediate subgroup in Held's central quotient

This is the mathematical interface between the transfer argument and the
recognition argument on printed p.234 of Held's Lemma 4.2. In Q = C/<mu>,
transfer constructs a normal subgroup M of index four, with trivial odd
core and no subgroup of index two. Its Sylow two-subgroup is dihedral of
order eight and is exactly the centralizer in M of the image p of pi.

`QuotientCore` records this intermediate subgroup and the actual Sylow
equivalence. Its existence is an open source obligation; it neither records
nor proves an A6 subgroup. Recognition must identify M, split its inverse
image in C, exclude the PSL2(7) alternative, and identify C/A separately.
No choice of the source's lambda or xi normalization is fixed by this
interface. Those choices must be justified when using the source actors.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2, p.234.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The subgroup produced by transfer in Q, before simple-group recognition. -/
public structure QuotientCore where
  subgroup : Subgroup (Q D e)
  normal : subgroup.Normal
  index : subgroup.index = 4
  p_mem : p D e ∈ subgroup
  sylow : Sylow 2 subgroup
  sylowEquiv : sylow ≃* DihedralGroup 4
  centralizer_eq : centralizer ({⟨p D e, p_mem⟩} : Set subgroup) =
    (sylow : Subgroup subgroup)
  oddCore : pPrimeCore 2 subgroup = ⊥
  no_index_two : ∀ N : Subgroup subgroup, N.Normal → N.index ≠ 2

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
