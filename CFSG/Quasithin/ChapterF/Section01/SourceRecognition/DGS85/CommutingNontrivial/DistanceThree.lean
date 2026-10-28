module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CoreProductComparison

/-!
# Critical distance three in the nontrivial commuting case

The prior exhaustive reduction leaves only a small unitary starting
quotient with a proper adjacent-core product. Its edge index is at most
four. Compute the same index at the other endpoint: a linear quotient
forces the full product, while a larger unitary or Suzuki quotient gives
an index greater than four. The remaining small models are transported
along the actual vertex orbit to the terminal vertex, where the proved
rank-one-terminal theorem already excludes distance five.

This proves DGS 8.4 under the original earlier local obstruction and full
rank-one catalogue. It retains both critical orientations and the literal
quotients. The order-144 enlargement outside that catalogue is not an
input to this theorem. The identifications in 8.5--8.7 remain separate.

Source: DGS, *Groups and Graphs* (1985), 8.4, pp.137--138.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original nontrivial commuting configuration has critical distance three,
with both orientations, all local models and the original quotient maps. -/
theorem reduced_distance_three
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    : b (Reduction.reducedFamily J S₀) = 3 := by
  rcases reduced_distance_three_or_small_unitary_start h hob models hc hab hd hb hcomm hne with
    he | ⟨hfive,hu,hproper⟩
  · exact he
  exfalso
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let L := d.localGroup beta
  let L' := d.localGroup a'
  let : Finite L := Finite.of_injective (inclusion (d.local_le beta)) (inclusion_injective _)
  let : Finite L' := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d hab
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d hab.symm
  have hupper := source_small_unitary_core_product_index_le_four ht d hab (models a) R hR
    (hob beta a hab.symm) hu
  have hp : ¬ (stabilizer F beta ⊓ stabilizer F a).pCoreIn 2 ≤ Q F beta ⊔ Q F a := by
    intro hh
    apply hproper
    apply le_antisymm
    · exact sup_le (Noncommuting.graph_Q_le_edgeCore ht hab)
        (by simpa only [Reduction.reducedFamily,inf_comm] using Noncommuting.graph_Q_le_edgeCore ht hab.symm)
    · simpa only [inf_comm,sup_comm] using hh
  have hupper' : (Q F beta ⊔ Q F a).relIndex
      ((stabilizer F beta ⊓ stabilizer F a).pCoreIn 2) ≤ 4 := by
    change (Q F a ⊔ Q F beta).relIndex ((stabilizer F a ⊓ stabilizer F beta).pCoreIn 2) ≤ 4 at hupper
    simpa only [sup_comm,inf_comm] using hupper
  have heven : Even ((graph F).dist beta a') := by
    have he : (graph F).dist beta a' = 4 := by
      change (graph F).dist beta a' + 1 = b F at hd
      change b F = 5 at hfive
      omega
    rw [he]
    decide
  obtain ⟨g,hg⟩ := (same_orbit_iff F beta a').mpr ((even_dist_iff F ht.generate beta a').mp heven)
  have hL : (d.localGroup beta).map (MulAut.conj g).toMonoidHom = d.localGroup a' := by
    rw [←d.conjugate,hg]
  let f := ((d.localGroup beta).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hL)
  let e : (L ⧸ pCore 2 L) ≃* (L' ⧸ pCore 2 L') :=
    QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have hsmall (hs : ClassicalGroup.IsPSL (L' ⧸ pCore 2 L') 2 2 ∨
      Nonempty ((L' ⧸ pCore 2 L') ≃* DihedralGroup 5) ∨
      Nonempty ((L' ⧸ pCore 2 L') ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU (L' ⧸ pCore 2 L') 3 2 ∨ IsSU (L' ⧸ pCore 2 L') 3 2) : False := by
    have he := reduced_small_terminal_distance_three h hob models hc hab hd hb hcomm hne hs
    omega
  have hunit {n : ℕ} (hn : 2 ≤ n)
      (hi : ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2^n) ∨ IsSU (L ⧸ pCore 2 L) 3 (2^n)) : False := by
    have hlo := source_large_unitary_core_product_index_lower ht d hab.symm (models beta) T hT hn hi hp
    have hn4 : 4 ≤ 2^n := by
      calc
        4 = 2^2 := rfl
        _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
    change (2^n)^2 ≤ (Q F beta ⊔ Q F a).relIndex
      ((stabilizer F beta ⊓ stabilizer F a).pCoreIn 2) at hlo
    nlinarith
  cases models a' with
  | linear n hn hi =>
    obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hi
    have hi' : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n) := ⟨K,inferInstance,inferInstance,hK,⟨e.trans eK⟩⟩
    have hfull := source_linear_edge_core_product ht d hab.symm (models beta) T hT
      (hob a beta hab) hn hi'
    exact hp hfull.ge
  | dihedral hi => exact hsmall (Or.inr (Or.inl hi))
  | suzuki m hi =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact hsmall (Or.inr (Or.inr (Or.inl hi)))
    have hlo := source_suzuki_core_product_index_lower ht d hab.symm (models beta) T hT m
      (e.trans hi.some) hp
    have hn8 : 8 ≤ 2^(2*m+1) := by
      calc
        8 = 2^3 := rfl
        _ ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide) (by omega)
    change 2^(2*m+1) ≤ (Q F beta ⊔ Q F a).relIndex
      ((stabilizer F beta ⊓ stabilizer F a).pCoreIn 2) at hlo
    omega
  | projective_unitary n hn hi =>
    change ClassicalGroup.IsPSU (L' ⧸ pCore 2 L') 3 (2^n) at hi
    by_cases hn2 : 2 ≤ n
    · obtain ⟨K,_,_,H,hK,hconj,⟨eK⟩⟩ := hi
      exact hunit hn2 (Or.inl ⟨K,inferInstance,inferInstance,H,hK,hconj,⟨e.trans eK⟩⟩)
    · have hn1 : n=1 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hn1,pow_one] using hi)))))
  | special_unitary n hn hi =>
    change IsSU (L' ⧸ pCore 2 L') 3 (2^n) at hi
    by_cases hn2 : 2 ≤ n
    · obtain ⟨K,_,_,H,hK,hconj,⟨eK⟩⟩ := hi
      exact hunit hn2 (Or.inr ⟨K,inferInstance,inferInstance,H,hK,hconj,⟨e.trans eK⟩⟩)
    · have hn1 : n=1 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [hn1,pow_one] using hi)))))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
