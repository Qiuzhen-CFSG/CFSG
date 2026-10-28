module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorComparison

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A factor-module bound at the ending vertex rules out reverse containment
for any starting quotient on which the literal starting-center action is
faithful.  The starting model is kept explicit, so the theorem can be
instantiated by the linear, Suzuki and projective-unitary rows without
identifying quotient carriers. -/
theorem source_reciprocal_escape_of_factor_bound_faithful
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',
      V (family P) a' 1⁆ ≠ ⊥)
    {D : Type u} [Group D] [Finite D]
    [IsElementaryAbelian 2 (Z (family P) a)]
    (M : BinaryRankOneModel D)
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D)
    (T : Sylow 2 (stabilizer (family P) a))
    (hAS :
      ((V (family P) a' 1).subgroupOf (d.localGroup a)).map
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))) ≤
        ((T : Subgroup (stabilizer (family P) a)).subgroupOf
          ((d.localGroup a).subgroupOf (stabilizer (family P) a))).map
          ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))).comp
            (subgroupOfEquivOfLe (d.local_le a)).toMonoidHom))
    (ρ : Representation (ZMod 2) D (Additive (Z (family P) a)))
    (hact : ∀ (l : d.localGroup a) (z : Additive (Z (family P) a)),
      ((ρ (e.toMonoidHom (QuotientGroup.mk' (pCore 2 (d.localGroup a)) l)) z).toMul : G) =
        (l : G) * z.toMul * (l : G)⁻¹)
    (hf : Function.Injective ρ)
    (hfactor : (Q (family P) a').relIndex (Z (family P) a) ≤
      (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1)) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  intro hreverse
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let F := family P
  let L := d.localGroup a
  let Z₀ := Z F a
  let A := V F a' 1
  have hZL : Z₀ ≤ L := pGroup_le_localGroup F d a Z₀
    (IsElementaryAbelian.isPGroup 2 Z₀) (Z_le_stabilizer F a)
  have hAP : A ≤ stabilizer F a := hreverse.trans ((source_Z_Q_U h beta).2.trans
    ((ballKernel_one_le_edge F hab.symm).trans inf_le_right))
  let : IsElementaryAbelian 2 A :=
    CommutingThreeProfile.V_elementary F h.generate
      (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by
        have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
        omega) a'
  have hAL : A ≤ L := pGroup_le_localGroup F d a A
    (IsElementaryAbelian.isPGroup 2 A) hAP
  let : Finite L := Finite.of_injective (inclusion (d.local_le a))
    (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion hZL) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAL) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let Aq := (A.subgroupOf L).map q
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 Aq := IsElementaryAbelian.map q
  obtain ⟨S, hS, hgen, hres⟩ := source_center_module_prepared_of_center_eq_bot h d a
    (local_center_eq_bot_of_neighbor_central h d hab
      (source_critical_geometry h d hc hab hd hb hcomm).2.2.1) T e ρ hact
  have hAS' : Aq ≤ ((T : Subgroup (stabilizer F a)).subgroupOf
      (L.subgroupOf (stabilizer F a))).map
      (q.comp (subgroupOfEquivOfLe (d.local_le a)).toMonoidHom) := hAS
  have hquad : IsQuadratic ρ Aq := by
    obtain ⟨_, _, hcenter, hquadratic, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
    let δ := centerSection L Z₀ hZL
      ((d.local_le a).trans (stabilizer_normalizes_Z F a)) q ρ hact
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le L Z₀ ⊥ A ρ q δ
    rw [commutator_comm A, commutator_comm A]
    exact (commutator_mono (commutator_mono (Z_neighbor_le_V F hab.symm) le_rfl) le_rfl).trans
      hquadratic.2.le
  have hsq := source_reverse_containment_square_bound h hB d hc hab hd hb hcomm
    models hne hreverse M T e (A.subgroupOf L) ρ hact hf hAS' hquad
  have hi := center_action_fixed_index L Z₀ A hZL
    ((d.local_le a).trans (stabilizer_normalizes_Z F a)) hAL q ρ hact
  have he := source_reverse_center_centralizer h hB d hc hab hd hb hcomm models hreverse
  have hcidx : (centralizer (A : Set G)).relIndex Z₀ =
      (Q F a').relIndex Z₀ := by
    rw [← inf_relIndex_left Z₀ (centralizer (A : Set G)), he, inf_relIndex_left]
  have hcard : Nat.card Aq = (Q F a).relIndex A :=
    BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F a) A q
      (local_quotient_kernel F d a e) hAL
  have hupper : (centralizer (Z₀ : Set G)).relIndex A ≤ (Q F a).relIndex A :=
    relIndex_le_of_le_left
      (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1))
      (((Q F a).subgroupOf A).index_ne_zero_of_finite)
  have hx : 1 < (Q F a').relIndex Z₀ := by
    have hnz : (Q F a').relIndex Z₀ ≠ 0 := ((Q F a').subgroupOf Z₀).index_ne_zero_of_finite
    have hno : (Q F a').relIndex Z₀ ≠ 1 := by
      intro heq
      exact hc.2 ((relIndex_eq_one.mp heq).trans (source_Z_Q_U h a').2)
    omega
  have hxy : (Q F a').relIndex Z₀ ≤ Nat.card Aq := by
    rw [hcard]
    exact hfactor.trans hupper
  have hstrict : Nat.card (Additive Z₀ ⧸ fixedSpace ρ Aq) < Nat.card Aq ^ 2 := by
    rw [hi, hcidx]
    nlinarith
  exact (Nat.not_lt_of_ge hsq) hstrict

/-! The same argument on the literal reduced F1.11 carrier.  The reduced
local group, Borel core Sylow and quotient maps are supplied by the existing
source transport; the action and faithful factor hypotheses remain explicit.
This is an assembly-facing consumer rather than an alias for the conclusion:
the 6.5 obstruction and every module premise are still visible. -/

theorem reduced_reciprocal_escape_of_factor_bound_faithful
    {J : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a,
      Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) v)))
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓
      Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    {D : Type u} [Group D] [Finite D]
    [IsElementaryAbelian 2 (Z (Reduction.reducedFamily J S) a)]
    (M : BinaryRankOneModel D)
    (e : (graphLocalGroup (Reduction.reducedFamily J S) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) ≃* D)
    (T : Sylow 2 (stabilizer (Reduction.reducedFamily J S) a))
    (hAS :
      ((V (Reduction.reducedFamily J S) a' 1).subgroupOf
          (graphLocalGroup (Reduction.reducedFamily J S) a)).map
          (e.toMonoidHom.comp (QuotientGroup.mk'
            (pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)))) ≤
        ((T : Subgroup (stabilizer (Reduction.reducedFamily J S) a)).subgroupOf
          ((graphLocalGroup (Reduction.reducedFamily J S) a).subgroupOf
            (stabilizer (Reduction.reducedFamily J S) a))).map
          ((e.toMonoidHom.comp (QuotientGroup.mk'
            (pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)))).comp
            (subgroupOfEquivOfLe
              (show graphLocalGroup (Reduction.reducedFamily J S) a ≤
                stabilizer (Reduction.reducedFamily J S) a from
                sylowGenerated_le _)).toMonoidHom))
    (ρ : Representation (ZMod 2) D
      (Additive (Z (Reduction.reducedFamily J S) a)))
    (hact : ∀ (l : graphLocalGroup (Reduction.reducedFamily J S) a)
      (z : Additive (Z (Reduction.reducedFamily J S) a)),
      ((ρ (e.toMonoidHom (QuotientGroup.mk'
        (pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) a)) l)) z).toMul :
          Reduction.G₀ J S) =
        (l : Reduction.G₀ J S) * z.toMul * (l : Reduction.G₀ J S)⁻¹)
    (hf : Function.Injective ρ)
    (hfactor :
      (Q (Reduction.reducedFamily J S) a').relIndex
          (Z (Reduction.reducedFamily J S) a) ≤
        (centralizer (Z (Reduction.reducedFamily J S) a :
          Set (Reduction.G₀ J S))).relIndex
          (V (Reduction.reducedFamily J S) a' 1)) :
    ¬ V (Reduction.reducedFamily J S) a' 1 ≤
      Q (Reduction.reducedFamily J S) beta := by
  let : IsElementaryAbelian 2
      (Z (family (fun i : Fin 2 =>
        (Reduction.P₀ J S i).subgroupOf (Reduction.G₀ J S))) a) :=
    CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) a
  exact source_reciprocal_escape_of_factor_bound_faithful
    (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm models hne M e T
    hAS ρ hact hf hfactor

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
