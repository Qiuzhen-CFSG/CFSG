module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointCubicApplication
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# A cubic in the original exchanged component

The original Sylow three-subgroup of the point residual is elementary of
order nine and lies in the product of the two exchanged components. Each
component has order with three-part exactly three: its intrinsic two-core
quotient is PSL₂(4). The relative-index formula therefore forces the Sylow
subgroup to meet the first component nontrivially. This constructs a cubic
in the literal intersection K ∩ L, before taking any quotient.

The canonical point marking and this cubic discharge both extra witnesses
in the tensor/non-tensor filtration contradiction. All earlier geometric
hypotheses and the original reduced actor H remain explicit.

Source: Aschbacher--Smith, 12.6.33, printed pp.837--838.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

private theorem inf_ne_bot_of_nine {G : Type*} [Group G] [Finite G]
    (A B X : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) (hX : X ≤ A ⊔ B)
    (hc : Nat.card X = 9) (hB : ¬ 9 ∣ Nat.card B) : X ⊓ A ≠ ⊥ := by
  let N := A ⊔ B
  let : (A.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer hn)
  have hi := relIndex_sup_left (B.subgroupOf N) (A.subgroupOf N)
  rw [← subgroupOf_sup (show A ≤ N from le_sup_left) (show B ≤ N from le_sup_right),
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf (show B ≤ N from le_sup_right)] at hi
  intro he
  have hd := relIndex_dvd_index_of_normal (H := A.subgroupOf N) (K := X.subgroupOf N)
  rw [relIndex_subgroupOf hX] at hd
  change A.relIndex X ∣ A.relIndex N at hd
  rw [← inf_relIndex_right A X, inf_comm, he, relIndex_bot_left, hc, hi] at hd
  exact hB (hd.trans (relIndex_dvd_card A B))

private theorem not_nine_dvd_card_of_pslFour (X : Type*) [Group X] [Finite X]
    (hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 4) : ¬ 9 ∣ Nat.card X := by
  obtain ⟨F,hF,hfin,hFcard,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hFcard
  have hc : Nat.card (X ⧸ pCore 2 X) = 60 := by
    rw [Nat.card_congr (e.trans a).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hh := (pCore 2 X).card_mul_index
  change Nat.card (pCore 2 X) * Nat.card (X ⧸ pCore 2 X) = Nat.card X at hh
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  rw [hn,hc] at hh
  intro hd
  rw [← hh] at hd
  exact (by decide : ¬ 9 ∣ 60)
    (((by decide : Nat.Coprime 9 2).pow_right n).dvd_mul_left.mp hd)

namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes)
  (hZ : ZV L V = ⊥) (z : V) (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original exchanged component contains a nonidentity cubic of L. -/
theorem SourceHypothesis.original_abelian_exchanged_cubic
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ x : K, (x : G) ∈ L ∧ x ^ 3 = 1 ∧ x ≠ 1 := by
  let E := D.fullSetup hZ T z
  obtain ⟨t,ht,hTH,htn,hOH,e,Q,he,hQ,hstar,hsol,hLB,hBM,hnB,
    heven,hrank,hOT,hBeq,hMeq⟩ :=
    S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn (n := 2) (by decide) hm
  have hi : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact (cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans
      (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn).1
  have ho := orbit_eq_two_conjugates H K T hKH hTH hi ht htn
  have hLO : E.L₁ ≤ conjugateSpanBy K (T : Subgroup G) :=
    hLB.trans (hBeq.le.trans inf_le_left)
  obtain ⟨hBH,hB⟩ := conjugate_isCComponent H K hKH hK (hTH ht)
  have hBK : K.conjBy t ≤ normalizer (K : Set G) := by
    have hn := (le_cComponentLayer hB).trans (cComponentLayer_le_normalizer hK)
    rw [← subgroupOf_normalizer_eq hKH] at hn
    intro k hk
    exact hn (show (⟨k,hBH hk⟩ : H) ∈ (K.conjBy t).subgroupOf H from hk)
  have hnine : ¬ 9 ∣ Nat.card (K.conjBy t) := by
    change ¬ 9 ∣ Nat.card (K.map (MulAut.conj t).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj t).injective]
    exact not_nine_dvd_card_of_pslFour K hm
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  obtain ⟨hP,hPc⟩ := S.original_point_residual_sylow D hZ z hz hTz P
  let := hP
  let X : Subgroup G := (P : Subgroup E.L₁).map E.L₁.subtype
  let : IsElementaryAbelian 3 X := IsElementaryAbelian.map_subtype
  have hXL : X ≤ E.L₁ := map_subtype_le _
  have hXc : Nat.card X = 9 := by
    rw [card_map_of_injective E.L₁.subtype_injective]
    exact hPc
  have hXK : X ⊓ K ≠ ⊥ := inf_ne_bot_of_nine K (K.conjBy t) X hBK
    (hXL.trans (hLO.trans ho.le)) hXc hnine
  obtain ⟨x,hx,hxn⟩ := (X ⊓ K).bot_or_exists_ne_one.resolve_left hXK
  refine ⟨⟨x,hx.2⟩,(hXL.trans ((map_subtype_le _).trans inf_le_left)) hx.1,?_,?_⟩
  · apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 3) x hx.1
  · intro he
    exact hxn (congrArg Subtype.val he)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Exclude the original exchanged PSL₂(4) branch, with its point marking
and cubic constructed from the retained source hypotheses. -/
theorem SourceHypothesis.original_abelian_exchanged_impossible
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    (hout : ¬ K ≤ M L) : False := by
  obtain ⟨x,hxL,hx3,hxn⟩ := S.original_abelian_exchanged_cubic D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hgen hn hm
  exact S.original_abelian_exchanged_impossible_of_original_point D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hgen hn hm hout x hxL hx3 hxn
end CFSG.Quasithin.Chapter12.Section06
