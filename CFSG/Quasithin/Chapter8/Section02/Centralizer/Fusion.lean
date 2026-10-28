module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Sextet.Geometry
public import CFSG.Quasithin.Chapter8.Section02.NormalClosure
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions

/-!
# A distinct cocode conjugate in the involution-centralizer closure

Two pairs in different sextet tetrads give a four-point class in the geometric
seven-space which differs from the sextet's common tetrad class. Native M₂₄
four-transitivity gives an actual conjugating element. A marking of L/V and
its conjugation module transports this witness into the original group, then
into the literal normal closure inside C_G(z).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the fusion
assertion in the proof of 8.2.14, printed p.723 (PDF p.740). The native witness
has no extra hypotheses. Its ambient application retains the module and
subspace markings from 8.2.11 and 8.2.13 as explicit source obligations.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open scoped Pointwise

namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
noncomputable section

private theorem tetrad_transitive (B D : Finset (Fin 24))
    (hB : B.card = 4) (hD : D.card = 4) : ∃ g : M24, g • B = D := by
  let := m24_isFivePretransitive
  have ht : MulAction.IsMultiplyPretransitive M24 (Fin 24) 4 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by decide) (by simp)
  let : MulAction.IsPretransitive M24 (Set.powersetCard (Fin 24) 4) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive M24 ht
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24
    (⟨B, hB⟩ : Set.powersetCard (Fin 24) 4) ⟨D, hD⟩
  exact ⟨g, congrArg Subtype.val hg⟩

private theorem pair_union_vector (P Q : PointPair) (hd : Disjoint P.val Q.val) :
    evenSetVector (P.val ∪ Q.val)
      (by rw [Finset.card_union_of_disjoint hd, P.property, Q.property]; decide) =
      pairVector P + pairVector Q := by
  change codeInCore.mkQ _ = codeInCore.mkQ _ + codeInCore.mkQ _
  rw [← map_add]
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  ext i
  have hdisj := Finset.disjoint_left.mp hd
  by_cases hi : i ∈ P.val <;> by_cases hj : i ∈ Q.val
  · exact (hdisj hi hj).elim
  · simp [wordOfSet, hi, hj]
  · simp [wordOfSet, hi, hj]
  · simp [wordOfSet, hi, hj]

/-- The sextet line has a distinct M₂₄-conjugate in the literal geometric
seven-space. This is the native module calculation used at the end of §8.2. -/
theorem exists_distinct_sextet_conjugate (S : Sextet) :
    ∃ g : M24, cocodeRepresentation g (sextetVector S) ∈ sextetPairSpace S ∧
      cocodeRepresentation g (sextetVector S) ≠ sextetVector S := by
  obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp
    (show 1 < S.parts.card by rw [S.card]; decide)
  obtain ⟨P, hPB, hP⟩ := Finset.exists_subset_card_eq
    (show 2 ≤ B.card by rw [S.tetrad B hB]; decide)
  obtain ⟨Q, hQC, hQ⟩ := Finset.exists_subset_card_eq
    (show 2 ≤ C.card by rw [S.tetrad C hC]; decide)
  have hdisj := S.disjoint B hB C hC hBC
  have hd : Disjoint P Q := hdisj.mono hPB hQC
  have hcard : (P ∪ Q).card = 4 := by
    rw [Finset.card_union_of_disjoint hd, hP, hQ]
  have heven : Even (P ∪ Q).card := by rw [hcard]; decide
  obtain ⟨g, hg⟩ := tetrad_transitive B (P ∪ Q) (S.tetrad B hB) hcard
  have he : cocodeRepresentation g (sextetVector S) = evenSetVector (P ∪ Q) heven := by
    rw [sextetVector_eq S hB, evenSetVector_equivariant]
    simp only [hg]
  refine ⟨g, ?_, ?_⟩
  · rw [he, pair_union_vector ⟨P, hP⟩ ⟨Q, hQ⟩ hd]
    have hleB : supportedPairSpace B ≤ sextetPairSpace S :=
      le_iSup_of_le B (le_iSup_of_le hB le_rfl)
    have hleC : supportedPairSpace C ≤ sextetPairSpace S :=
      le_iSup_of_le C (le_iSup_of_le hC le_rfl)
    exact (sextetPairSpace S).add_mem
      (hleB (pairVector_mem_supportedPairSpace ⟨P, hP⟩ hPB))
      (hleC (pairVector_mem_supportedPairSpace ⟨Q, hQ⟩ hQC))
  · rw [he]
    intro heq
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
    have hEq : P ∪ Q = B := tetrad_eq_of_vector_eq_of_inter hcard (S.tetrad B hB)
      ⟨p, Finset.mem_inter.mpr ⟨Finset.mem_union_left Q hp, hPB hp⟩⟩
      (heq.trans (sextetVector_eq S hB))
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < Q.card by omega)
    exact Finset.disjoint_left.mp hdisj
      (hEq ▸ Finset.mem_union_right P hq) (hQC hq)

end
end CFSG.Quasithin.Chapter8.Section02.Centralizer

namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
noncomputable section
open Subgroup

/-- A marking of the actual quotient L/V and its conjugation module. The
kernel identity retains the source quotient, and equivariance retains the
ambient conjugation action. -/
structure CocodeMarking {G : Type*} [Group G] (L V : Subgroup G) where
  le_actor : V ≤ L
  projection : L →* M24
  surjective : Function.Surjective projection
  kernel : projection.ker = V.subgroupOf L
  moduleEquiv : Multiplicative Cocode ≃* V
  equivariant : ∀ (l : L) (v : Cocode),
    (moduleEquiv (Multiplicative.ofAdd (cocodeRepresentation (projection l) v)) : G) =
      (l : G) * (moduleEquiv (Multiplicative.ofAdd v) : G) * (l : G)⁻¹

/-- The actual marked module is abelian. -/
theorem CocodeMarking.isMulCommutative {G : Type*} [Group G]
    {L V : Subgroup G} (D : CocodeMarking L V) : IsMulCommutative V := by
  apply isMulCommutative_iff.mpr
  intro a b
  apply D.moduleEquiv.symm.injective
  simp only [map_mul, mul_comm]

/-- Equivariance forces normalization of the literal ambient module subgroup. -/
theorem CocodeMarking.normalizes {G : Type*} [Group G]
    {L V : Subgroup G} (D : CocodeMarking L V) : L ≤ normalizer (V : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl v hv
  obtain ⟨w, hw⟩ := D.moduleEquiv.surjective ⟨v, hv⟩
  have he := D.equivariant ⟨l, hl⟩ (Multiplicative.toAdd w)
  have hew : (D.moduleEquiv w : G) = v := congrArg Subtype.val hw
  change (D.moduleEquiv (Multiplicative.ofAdd
    (cocodeRepresentation (D.projection ⟨l, hl⟩) (Multiplicative.toAdd w))) : G) =
      l * (D.moduleEquiv w : G) * l⁻¹ at he
  rw [hew] at he
  exact he ▸ (D.moduleEquiv _).property

/-- Transport the native geometric witness to an actual L-conjugate. Only the
module and subspace markings remain explicit, not a fusion premise. -/
theorem exists_distinct_conjugate_in_marked_space {G : Type*} [Group G]
    (L V : Subgroup G) (D : CocodeMarking L V) (S : Sextet)
    (z : G) (Vz : Subgroup G)
    (hz : (D.moduleEquiv (Multiplicative.ofAdd (sextetVector S)) : G) = z)
    (hVz : ∀ v : Cocode, v ∈ sextetPairSpace S →
      (D.moduleEquiv (Multiplicative.ofAdd v) : G) ∈ Vz) :
    ∃ l : L, (l : G) * z * (l : G)⁻¹ ∈ Vz ∧
      (l : G) * z * (l : G)⁻¹ ≠ z := by
  obtain ⟨g, hg, hne⟩ := exists_distinct_sextet_conjugate S
  obtain ⟨l, hl⟩ := D.surjective g
  have he := D.equivariant l (sextetVector S)
  rw [hl, hz] at he
  refine ⟨l, he ▸ hVz _ hg, ?_⟩
  intro h
  apply hne
  have hx : D.moduleEquiv (Multiplicative.ofAdd (cocodeRepresentation g (sextetVector S))) =
      D.moduleEquiv (Multiplicative.ofAdd (sextetVector S)) :=
    Subtype.ext (he.trans (h.trans hz.symm))
  exact D.moduleEquiv.injective hx

/-- The normal closure is formed inside C_G(z), then mapped to G. This
transport makes the geometric witness a failure of ambient weak closure in E. -/
theorem not_weakly_closed_centralizerClosure_of_cocode {G : Type*} [Group G]
    (L V : Subgroup G) (D : CocodeMarking L V) (S : Sextet)
    (z : G) (Vz : Subgroup (centralizer ({z} : Set G)))
    (hz : (D.moduleEquiv (Multiplicative.ofAdd (sextetVector S)) : G) = z)
    (hVz : ∀ v : Cocode, v ∈ sextetPairSpace S →
      (D.moduleEquiv (Multiplicative.ofAdd v) : G) ∈
        Vz.map (centralizer ({z} : Set G)).subtype) :
    (∃ l : L, (l : G) * z * (l : G)⁻¹ ∈
        (centralizerClosure z Vz).map (centralizer ({z} : Set G)).subtype ∧
      (l : G) * z * (l : G)⁻¹ ≠ z) ∧
    ¬ (∀ t ∈ (centralizerClosure z Vz).map (centralizer ({z} : Set G)).subtype,
      IsConj z t → t = z) := by
  obtain ⟨l, hl, hne⟩ := exists_distinct_conjugate_in_marked_space L V D S z
    (Vz.map (centralizer ({z} : Set G)).subtype) hz hVz
  have hle : Vz ≤ centralizerClosure z Vz := le_normalClosure
  have hm := map_mono hle hl
  refine ⟨⟨l, hm, hne⟩, ?_⟩
  intro hweak
  exact hne (hweak _ hm (isConj_iff.mpr ⟨(l : G), rfl⟩))

end
end CFSG.Quasithin.Chapter8.Section02.Centralizer
namespace CFSG.Quasithin.Chapter8.Section02.Centralizer
open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

/-- The fusion clause for the literal source constructions. The remaining
markings are the module and commutator-space identifications in 8.2.11 and
8.2.13; no conjugacy or weak-closure conclusion is among the premises. -/
theorem sourceClosure_fusion_of_cocode {G : Type*} [Group G]
    (L V : Subgroup G) (D : CocodeMarking L V) (S : Sextet) (z : G)
    (hz : (D.moduleEquiv (Multiplicative.ofAdd (sextetVector S)) : G) = z)
    (hVz : ∀ v : Cocode, v ∈ sextetPairSpace S →
      (D.moduleEquiv (Multiplicative.ofAdd v) : G) ∈ commutatorSpace L V z) :
    (∃ l : L, (l : G) * z * (l : G)⁻¹ ∈
        (sourceClosure L V z).map (centralizer ({z} : Set G)).subtype ∧
      (l : G) * z * (l : G)⁻¹ ≠ z) ∧
    ¬ (∀ t ∈ (sourceClosure L V z).map (centralizer ({z} : Set G)).subtype,
      IsConj z t → t = z) := by
  let := D.isMulCommutative
  have hzV : z ∈ V := hz ▸ (D.moduleEquiv _).property
  apply not_weakly_closed_centralizerClosure_of_cocode L V D S z
    ((commutatorSpace L V z).subgroupOf (centralizer ({z} : Set G))) hz
  intro v hv
  rw [map_subgroupOf_eq_of_le
    (commutatorSpace_le_centralizer L V z hzV D.normalizes)]
  exact hVz v hv

end CFSG.Quasithin.Chapter8.Section02.Centralizer

