module

public import Theory.GroupTheory.Gaschutz

/-!
# A.1.39: Gaschütz's splitting theorem

The source statement concerns an arbitrary abelian normal p-subgroup of a
finite group. The normal p-subgroup is contained in the chosen Sylow
subgroup, and the local complement is taken inside that actual subgroup.
The reusable coprime-index transfer argument constructs the global complement.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.39, printed p.31 (1 March 2004 manuscript).
-/

namespace CFSG.Quasithin.ChapterA

/-- A.1.39: `G` splits over the abelian normal p-subgroup `V` if and only
if its Sylow p-subgroup `P` splits over the same `V`, viewed inside `P`. -/
public theorem lemma_A_1_39
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V]
    (hV : IsPGroup p V) (P : Sylow p G) :
    (∃ K : Subgroup G, V.IsComplement' K) ↔
      ∃ K : Subgroup P, (V.subgroupOf (P : Subgroup G)).IsComplement' K :=
  V.exists_complement_iff_sylow hV P

end CFSG.Quasithin.ChapterA
