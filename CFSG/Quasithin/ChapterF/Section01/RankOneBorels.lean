module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.QuotientGeometry
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Dihedral
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# Rank-one Borels for Aschbacher–Smith F.1.3(1)

Source: `refs/quasithin.pdf`, printed pp.259–260, Remark F.1.2 and
Lemma F.1.3(1), together with the local Cartan and solvability observations
in its proof.

Each concrete rank-one model has a proper Sylow normalizer containing every
proper Sylow overgroup, with two-core the Sylow subgroup and an abelian
odd-order complement. Actual multiplicative equivalences transport these
facts to the quotient in F.1.1(c), including all the small parameters.
The quotient correspondence and Schur–Zassenhaus lift the facts through
O₂(Lᵢ), and the local embedding identifies the resulting normalizer with Bᵢ.
Finiteness of Lᵢ is derived from F.1.1; no Borel conclusions are assumed.

`AmbientQuotient` constructs the actual restricted quotient projection and
identifies its kernel with O₂(Lᵢ) inside Bᵢ. Its equivalences commute with
projection and with the chosen concrete model isomorphism. The imported
model modules identify the resulting normalizers with natural point
stabilizers or conjugates of the concrete matrix Borels.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source

variable {H : Type*} [Group H]

/-- Every actual rank-one model in F.1.1(c) has the required Sylow-normalizer
structure, including PSL₂(2), Sz(2), SU₃(2), PSU₃(2), and D₁₀. -/
theorem IsRankOneModel.rankOneSylowFacts (h : IsRankOneModel H) (T : Sylow 2 H) :
    RankOneSylowFacts T := by
  let : Finite H := h.finite
  cases h with
  | linear n hn h =>
    rcases h with ⟨F, _, _, hcard, ⟨e⟩⟩
    apply rankOneSylowFacts_of_equiv T e
    exact rankOneSylowFacts_psl2 F n hn hcard _
  | suzuki m h =>
    rcases h with ⟨e⟩
    apply rankOneSylowFacts_of_equiv T e
    exact suzuki_rankOneSylowFacts m _
  | projective_unitary n hn h =>
    rcases h with ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩
    apply rankOneSylowFacts_of_equiv T e
    exact rankOneSylowFacts_psu3 J n hn hcard hconj _
  | special_unitary n hn h =>
    rcases h with ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩
    apply rankOneSylowFacts_of_equiv T e
    exact rankOneSylowFacts_su3 J n hn hcard hconj _
  | dihedral h =>
    rcases h with ⟨e⟩
    exact rankOneSylowFacts_of_dihedral_equiv e T

/-- A finite group with a rank-one quotient by its two-core has the full
rank-one Sylow-normalizer structure. All concrete model premises are discharged. -/
theorem rankOneSylowFacts_of_rankOneQuotient [Finite H]
    (h : IsRankOneModel (H ⧸ pCore 2 H)) (T : Sylow 2 H) : RankOneSylowFacts T :=
  rankOneSylowFacts_of_quotient T (h.rankOneSylowFacts (quotientSylow T))

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The local Borel conclusions of F.1.3(1), including solvability and the
abelian odd-order Cartan complement, follow from the source F.1.1 hypotheses. -/
theorem HypothesisF11.rankOneBorelFacts (h : HypothesisF11 L S) (i : Fin 2) :
    RankOneBorelFacts (L i) S := by
  let : Finite (L i) := h.finite_local i
  obtain ⟨T, hT⟩ := h.sylow i
  exact rankOneBorelFacts_of_sylow (L i) S T hT
    (rankOneSylowFacts_of_rankOneQuotient (h.quotient i) T)

/-- F.1.3(1): the local Borel is the unique maximal proper Sylow overgroup,
its two-core is S ∩ Lᵢ, and its quotient by O₂(Lᵢ) is the actual quotient
Sylow normalizer. The isomorphism is constructed by `borelQuotientEquiv`,
whose representative formula is the restricted quotient projection. -/
theorem lemma_F_1_3_1 (h : HypothesisF11 L S) (i : Fin 2) :
    letI := h.finite_local i
    letI := twoCore_normal_in_borel (L i) S
    RankOneBorelFacts (L i) S ∧
      ∃ T : Sylow 2 (L i), (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i ∧
        RankOneSylowFacts (quotientSylow T) ∧
        Nonempty (borel (L i) S ⧸ (twoCore (L i)).subgroupOf (borel (L i) S) ≃*
          sylowNormalizer (quotientSylow T)) := by
  let := h.finite_local i
  let := twoCore_normal_in_borel (L i) S
  obtain ⟨T, hT⟩ := h.sylow i
  exact ⟨h.rankOneBorelFacts i, T, hT, (h.quotient i).rankOneSylowFacts _,
    ⟨borelQuotientEquiv (L i) S T hT⟩⟩

end CFSG.Quasithin.ChapterF.Source
