module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphCounting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreExclusions

/-!
# Chapter 11 exclusions on the literal graph

An intersection bound on the adjacent cores forces their commutator into
Zα. The source triple supplies all relative normalization, centralization
and characteristic-two hypotheses, so the Frattini argument makes S/Qβ
elementary. Together with the actual two-seed count this excludes the small
core in the nonelementary branch. In the binary elementary branch, the
actual core and elementary eight exclude the marked dihedral-ten quotient
inside the original beta stabilizer.

These applications remove the auxiliary algebraic hypotheses of the
terminal exclusions. The earlier core-generation, seed-size, intersection
and noncommutativity assertions are still explicit and are not supplied by
a classification hypothesis. The source profiles remain unfinished.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.7)--(11.8), printed pp.174--176.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The literal beta quotient is elementary once the core intersection lies in Zα. -/
theorem source_beta_quotient_elementary_of_core_intersection
    (h : LocallyRankOneTriple P B) {a b : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (S : Subgroup G)
    (hS : S = Q (family P) a ⊔ Q (family P) b)
    (hi : Q (family P) a ⊓ Q (family P) b ≤ Z (family P) a) :
    letI : ((Q (family P) b).subgroupOf S).Normal :=
      normal_subgroupOf_of_le_normalizer (hS ▸ sup_le
        (source_adjacent_core_normalizes_core h hab) (Q (family P) b).le_normalizer)
    IsElementaryAbelian 2 (S ⧸ (Q (family P) b).subgroupOf S) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let : Finite (Q (family P) a) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  let : ((Q (family P) b).subgroupOf S).Normal :=
    normal_subgroupOf_of_le_normalizer (hS ▸ sup_le
      (source_adjacent_core_normalizes_core h hab) (Q (family P) b).le_normalizer)
  apply beta_quotient_elementary_of_core_commutator
    (Q (family P) a) (Q (family P) b) (Z (family P) a) S
    (isPGroup_pCoreIn 2 _) hS (source_adjacent_core_normalizes_core h hab)
    ((source_adjacent_core_commutator h hab).trans hi) (source_core_centralizes_center h a)
  apply (inf_le_inf_right _ ?_).trans (source_core_selfCentralizing_in_vertex h b)
  rw [hS]
  exact sup_le ((source_Z_Q_U h a).2.trans
    ((ballKernel_one_le_edge _ hab).trans inf_le_right)) (Q_le_stabilizer _ b)

/-- The nonelementary branch forces core order strictly greater than the Suzuki candidate bound. -/
theorem source_nonElementary_beta_excludes_small_core
    (h : LocallyRankOneTriple P B) {a b c : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (hbc : (graph (family P)).Adj b c)
    (S : Subgroup G) (hS : S = Q (family P) a ⊔ Q (family P) b)
    (hi : Q (family P) a ⊓
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ≤ Z (family P) a)
    (qα qβ : ℕ) (hqβ : 0 < qβ)
    (hZ : Nat.card (Z (family P) a) = qα * qβ ^ 2)
    (hindex : (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = qβ)
    (hinter : Nat.card ((Z (family P) a ⊓ Q (family P) b) ⊓
      (Z (family P) c ⊓ Q (family P) b) : Subgroup G) = qβ) :
    letI : ((Q (family P) b).subgroupOf S).Normal :=
      normal_subgroupOf_of_le_normalizer (hS ▸ sup_le
        (source_adjacent_core_normalizes_core h hab) (Q (family P) b).le_normalizer)
    ¬ IsElementaryAbelian 2 (S ⧸ (Q (family P) b).subgroupOf S) →
      qα ^ 2 * qβ < Nat.card (Q (family P) b) := by
  intro he
  by_contra hn
  have hp := source_core_eq_pairSpan_of_small_order h hab hbc qα qβ hqβ hZ hindex hinter
    (Nat.le_of_not_gt hn)
  exact he (source_beta_quotient_elementary_of_core_intersection h hab S hS (hp.symm ▸ hi))

/-- The original marked quotient of the beta stabilizer cannot be dihedral of order ten, from the preceding source seed geometry. -/
theorem source_beta_quotient_not_dihedralTen
    (h : LocallyRankOneTriple P B) {a b c : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (hbc : (graph (family P)).Adj b c)
    (Lβ : Subgroup (stabilizer (family P) b))
    (hgen : Q (family P) b =
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
        (Q (family P) a ⊓ Q (family P) b))
    (hQa : Q (family P) a = Z (family P) a)
    (hZ : Nat.card (Z (family P) a) = 16)
    (hindex : (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = 2)
    (hinter : Nat.card ((Z (family P) a ⊓ Q (family P) b) ⊓
      (Z (family P) c ⊓ Q (family P) b) : Subgroup G) = 2)
    (hnoncomm : ⁅pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b),
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)⁆ ≠ ⊥) :
    ¬ Nonempty ((Lβ ⧸ (pCore 2 (stabilizer (family P) b)).subgroupOf Lβ) ≃*
      DihedralGroup 5) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  have hp := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _ hgen hQa
  obtain ⟨hs,hv⟩ := source_pairSpan_card h hab hbc 4 2 (by decide)
    (by norm_num; exact hZ) hindex hinter
  norm_num at hs hv
  have hQ : Nat.card (Q (family P) b) = 32 :=
    (congrArg (fun A : Subgroup G => Nat.card A) hp).trans hv
  let e : pCore 2 (stabilizer (family P) b) ≃* Q (family P) b :=
    (pCore 2 (stabilizer (family P) b)).equivMapOfInjective
      (stabilizer (family P) b).subtype (stabilizer (family P) b).subtype_injective
  have hQc : Nat.card (pCore 2 (stabilizer (family P) b)) = 32 :=
    (Nat.card_congr e.toEquiv).trans hQ
  have hnc : ¬ IsMulCommutative (pCore 2 (stabilizer (family P) b)) := by
    intro hc
    let := hc
    let : IsMulCommutative (Q (family P) b) :=
      ⟨⟨fun x y => e.symm.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
    apply hnoncomm
    rw [←hp]
    exact commutator_self_eq_bot_iff.mpr inferInstance
  let E := (Z (family P) a ⊓ Q (family P) b).subgroupOf (Q (family P) b)
  let : IsElementaryAbelian 2 (Z (family P) a ⊓ Q (family P) b : Subgroup G) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf inf_le_right
  let E' := E.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  have hE : Nat.card E' = 8 := by
    rw [card_map_of_injective e.symm.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show Z (family P) a ⊓ Q (family P) b ≤ Q (family P) b from inf_le_right)).toEquiv).trans hs
  have hfive := SmallNonabelianTwoGroup.not_five_dvd_card_of_selfCentralizing
    (pCore 2 (stabilizer (family P) b)) pCore_isPGroup hnc hQc E' inferInstance hE
    (source_vertex_core_selfCentralizing h b)
  rintro ⟨eL⟩
  have hc : Nat.card (Lβ ⧸ (pCore 2 (stabilizer (family P) b)).subgroupOf Lβ) = 10 := by
    rw [Nat.card_congr eL.toEquiv,DihedralGroup.nat_card]
  exact hfive ((show 5 ∣ Nat.card (Lβ ⧸
    (pCore 2 (stabilizer (family P) b)).subgroupOf Lβ) by rw [hc]; decide).trans
    (((pCore 2 (stabilizer (family P) b)).subgroupOf Lβ).card_quotient_dvd_card.trans
      Lβ.card_subgroup_dvd_card))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
