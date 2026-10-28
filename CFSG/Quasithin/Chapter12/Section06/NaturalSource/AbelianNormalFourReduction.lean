module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianLinearFourSieve
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedCubic

/-!
# A normal PSL₂(4) component in the original reduced actor

Apply the complete exchanged-component exclusion to the component already
selected outside M. The same reduced actor J = K₀L₁T still belongs to Hz;
its component K is now normal, and both K/O₂(K) and its literal image in
J/O₂(J) are PSL₂(4). Normality also identifies K₀ with K. This closes the
exchanged branch of the reduced catalogue without replacing J by Gz.

Earlier singular-point, TI, intersection and nonsingular-centralizer inputs
remain explicit. Recognition of the full symmetric-product quotient and
the universal natural reduction remain subsequent source obligations.

Source: Aschbacher--Smith, 12.6.32--33, printed pp.837--838.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)

include hz hTz hTV hbound hTI hns hH in
/-- The same selected escaping component is normal PSL₂(4) in the actual
reduced actor, retaining both quotient carriers and its original orbit. -/
theorem SourceHypothesis.original_abelian_reduced_normal_linearFour :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧ (K.subgroupOf J).Normal ∧ K₀ = K ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
      ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage J K) 2 4 := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,halt⟩ :=
    S.original_abelian_reduced_linearFour_models D hZ z hz hTz hTV hbound hTI hns hH
  let K₀ := conjugateSpanBy K (T : Subgroup G)
  let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
  have hKle : K ≤ J := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans le_sup_left)
  have hTle : (T : Subgroup G) ≤ J := le_sup_right
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with ⟨hn,hm,hms⟩ | hexchanged
  · exact ⟨hn,conjugateSpan_eq_of_normal J K T hKle hTle hn,hm,hms⟩
  · exact (S.original_abelian_exchanged_impossible D hZ z hz hTV hTz
      hbound hTI hns hJ hKle hKJ rfl hexchanged.1 hexchanged.2.2.1 hout).elim

end CFSG.Quasithin.Chapter12.Section06
