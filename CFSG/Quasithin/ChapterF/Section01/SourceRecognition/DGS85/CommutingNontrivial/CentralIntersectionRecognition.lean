module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionEstimate
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex

set_option linter.style.haveILetI false

/-!
# The opposite comparison in DGS 8.6

The opposite centralizer index is at most the product of the two original
quotient omega orders.  The proof splits the index at the terminal core;
the distinct-edge argument identifies the intermediate intersection and
both elementary quotient images lie in the corresponding Sylow omega-centers.
The same bound applies to every literal conjugation section of the opposite
neighbor span.  No action descent or naturality is assumed in this upper bound.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Chapter 8, the second comparison in the proof of 8.6, printed p. 140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem index_product (U Q K : Subgroup G) (h : U ⊓ Q ≤ K) :
    K.relIndex U * Q.relIndex (U ⊓ K) = Q.relIndex U := by
  rw [Nat.mul_comm,inf_comm U K,relIndex_inf_mul_relIndex]
  rw [←inf_relIndex_right (Q ⊓ K) U,←inf_relIndex_right Q U]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,h ⟨hx.2,hx.1⟩⟩,hx.2⟩⟩

/-- The upper half of the opposite comparison in 8.6, retaining the
moving center, both original quotient omega-centers, and both Sylows. -/
theorem source_opposite_centralizer_index_le_omega_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (d.localGroup w.val)) (T : Sylow 2 (d.localGroup a')) :
    (centralizer (Z (family P) w.val : Set G)).relIndex (V (family P) beta 1) ≤
      Nat.card (omegaCenterIn ((T : Subgroup (d.localGroup a')).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a'))))) *
      Nat.card (omegaCenterIn ((R : Subgroup (d.localGroup w.val)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup w.val))))) := by
  let := finite_endpoints h
  let F := family P
  let : Finite (d.localGroup a') := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  let : Finite (d.localGroup w.val) := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingTrivial.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow beta (by omega)
  let A := V F beta 1 ⊓ Q F a'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hVL : V F beta 1 ≤ d.localGroup a' := pGroup_le_localGroup F d a' _
    (IsElementaryAbelian.isPGroup 2 _) (V_le_stabilizer_of_dist_add_le_b F h.generate beta a' 1 hd.le)
  let : Finite (V F beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  have hAL : A ≤ d.localGroup w.val := (source_moving_actor h d hc hab hd hb hcomm w hm).2.1
  have hfirst := source_elementary_core_index_le_omega h d a' (models a') (V F beta 1) hVL T
  have hsecond := source_elementary_core_index_le_omega h d w.val (models w.val) A hAL R
  have hprod := index_product (V F beta 1) (Q F w.val) (Q F a')
    (source_moving_core_intersection h hB d hc hab hd hb hcomm w hm (models a'))
  have hQC : Q F w.val ≤ centralizer (Z F w.val : Set G) :=
    le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1)
  exact (relIndex_le_of_le_left hQC
    (((Q F w.val).subgroupOf (V F beta 1)).index_ne_zero_of_finite)).trans
      (hprod.symm.le.trans (Nat.mul_le_mul hfirst hsecond))

/-- Apply the opposite comparison to the fixed quotient of an actual
conjugation section.  In particular this applies to the residual section
`V_beta / C_(V_beta)(O²(L_beta))`, without any replacement of its kernel. -/
theorem source_opposite_section_index_le_omega_product
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (d.localGroup w.val)) (T : Sylow 2 (d.localGroup a'))
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (π : d.localGroup beta →* D)
    (N : Subgroup G)
    (c : BinaryConjugationSection (d.localGroup beta) (V (family P) beta 1) N (σ.comp π)) :
    Nat.card (W ⧸ fixedSpace σ (((Z (family P) w.val).subgroupOf (d.localGroup beta)).map π)) ≤
      Nat.card (omegaCenterIn ((T : Subgroup (d.localGroup a')).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup a'))))) *
      Nat.card (omegaCenterIn ((R : Subgroup (d.localGroup w.val)).map
        (QuotientGroup.mk' (pCore 2 (d.localGroup w.val))))) := by
  let := finite_endpoints h
  let : Finite (V (family P) beta 1) := Finite.of_injective
    (inclusion (c.section_le.trans (d.local_le beta))) (inclusion_injective _)
  exact (BinaryConjugationSection.fixed_quotient_card_le_centralizer_index σ π c
    (Z (family P) w.val)).trans
    (source_opposite_centralizer_index_le_omega_product h hB d models hc hab hd hb hcomm w hm R T)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
