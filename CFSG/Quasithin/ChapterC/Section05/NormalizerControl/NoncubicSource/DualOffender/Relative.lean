module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Transport
/-!
# Dual displacement bounds inside the actual auxiliary normalizer

The ambient commutator, fixed intersection and cardinality are transported
through the literal subgroup inclusions. This preserves the original actor
in N/C_N(V), rather than replacing it by an abstract isomorphic action.
Source: Aschbacher–Smith C.5.13 and B.4.7, printed pp.162 and90.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
variable {G : Type*} [Group G] [Finite G]
/-- The B.4.7 estimates in an ambient normalizer, using its literal quotient. -/
theorem relative_dual_bounds (N V B E : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 B]
    (hVN : V ≤ N) (hNV : N ≤ normalizer (V : Set G)) (hBN : B ≤ N)
    (hcomm : ⁅B,V⁆ ≤ E) (hEC : E ≤ centralizer (B : Set G))
    (hne : ¬ B ≤ centralizer (V : Set G)) (hker : B ⊓ centralizer (V : Set G) = E) :
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    let A := (B.subgroupOf N).map q
    IsElementaryTwo A ∧ IsQuadratic (centralizerQuotient (V.subgroupOf N)).dual A ∧
      fixedCodim (centralizerQuotient (V.subgroupOf N)).dual A ≤ Nat.log 2 (Nat.card E) ∧
      Nat.card A = E.relIndex B := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  let : IsElementaryAbelian 2 (B.subgroupOf N) := IsElementaryAbelian.subgroupOf hBN
  have hEN : E ≤ N := hker.symm.le.trans (inf_le_left.trans hBN)
  have hi : ⁅B.subgroupOf N,V.subgroupOf N⁆ ≤ E.subgroupOf N := by
    apply commutator_le.mpr
    intro b hb v hv
    exact hcomm (commutator_mem_commutator hb hv)
  have hc : E.subgroupOf N ≤ centralizer (B.subgroupOf N : Set N) := by
    intro e he b hb
    exact Subtype.ext (hEC he b hb)
  have hnon : ¬ B.subgroupOf N ≤ centralizer (V.subgroupOf N : Set N) := by
    intro hh
    apply hne
    intro b hb v hv
    exact congrArg N.subtype (hh (show (⟨b,hBN hb⟩ : N) ∈ B.subgroupOf N from hb)
      ⟨v,hVN hv⟩ hv)
  have hk : B.subgroupOf N ⊓ centralizer (V.subgroupOf N : Set N) = E.subgroupOf N := by
    ext b
    constructor
    · rintro ⟨hb,hc⟩
      apply hker.le
      exact ⟨hb,fun v hv => congrArg N.subtype (hc ⟨v,hVN hv⟩ hv)⟩
    · intro hb
      have he := hker.ge hb
      exact ⟨he.1,fun v hv => Subtype.ext (he.2 v hv)⟩
  have hb := canonical_dual_bounds (V.subgroupOf N) (B.subgroupOf N) (E.subgroupOf N) hi hc hnon
  refine ⟨hb.1,hb.2.1,?_,?_⟩
  · simpa only [Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv] using hb.2.2
  · rw [canonical_actor_card _ _ _ hk,relIndex_subgroupOf hBN]
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
