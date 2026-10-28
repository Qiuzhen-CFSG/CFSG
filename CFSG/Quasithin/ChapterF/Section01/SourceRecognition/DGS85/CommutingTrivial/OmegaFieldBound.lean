module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.InitialAlphaAction

/-!
# The alpha omega order bound from the constructed quadratic action

The whole quotient omega-center acts quadratically on the original Z_alpha.
The local center is trivial, and the original Sylow-center span gives the
fixed-generation hypothesis of corrected 5.12 on this same module. The
full binary catalogue bound, including both small unitary covers, applies.
Its fixed index is at most [Z_alpha : Z_alpha intersect Z(W)] = |F_beta|.
Thus the actual alpha omega-center has order at most the beta field order.

A comparison strictly below the omega order squared selects an actual alpha
SL₂ marking. This comparison is still conditional; neither field equality
nor alpha recognition is assumed or claimed unconditionally here.
InitialAlphaBounds supplies the original two-branch application.
Source: DGS, Groups and Graphs (1985), 9.4, printed p.143, and corrected 5.12.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original alpha omega has order at most the beta field order. The
strict-square case selects a linear quotient from the entire catalogue. -/
theorem reduced_natural_residual_omega_bound (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (Mbin : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    let q := QuotientGroup.mk' (pCore 2 H)
    let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
    let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
    ∃ R : Sylow 2 H,
      (R : Subgroup H).map H.subtype = (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 ∧
      let A := omegaCenterIn ((R : Subgroup H).map q)
      let Y := (A.comap q).map H.subtype
      Y ≤ W ∧ ⁅Z Γ a,Y⁆ ≤ Z₀ ∧ Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) ∧
        ⁅⁅Z Γ a,Y⁆,Y⁆ = ⊥ ∧ Z₀.relIndex (Z Γ a) = Nat.card F ∧
        Nat.card A ≤ Nat.card F ∧
        (Nat.card F < Nat.card A ^ 2 →
          ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
            0 < m ∧ Nat.card K = 2^m ∧ Nonempty ((H ⧸ pCore 2 H) ≃* SL(2,K))) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := graphLocalGroup Γ a
  let D := H ⧸ pCore 2 H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  let : Nontrivial (Z Γ a) := CommutingNontrivial.source_center_nontrivial ht a
  obtain ⟨R,hR,hYW,hYZ,hZY,hquadY,hindex⟩ :=
    reduced_natural_residual_omega_quadratic h hob hc hab hd hb hcomm M hn hF e hres
  let T : Sylow 2 D := R.mapSurjective (QuotientGroup.mk'_surjective _)
  let A := omegaCenterIn ((R : Subgroup H).map q)
  let Y := (A.comap q).map H.subtype
  let Z₀ := Z Γ a ⊓ (Subgroup.center (conjugateSpanBy (Q Γ a) (stabilizer Γ beta))).map
    (conjugateSpanBy (Q Γ a) (stabilizer Γ beta)).subtype
  change Z₀.relIndex (Z Γ a) = Nat.card F at hindex
  change Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) at hZY
  change ⁅⁅Z Γ a,Y⁆,Y⁆ = ⊥ at hquadY
  have hYH : Y ≤ H := map_subtype_le _
  have hYq : (Y.subgroupOf H).map q = A := by
    change ((A.comap q).map H.subtype |>.comap H.subtype).map q = A
    rw [comap_map_eq_self_of_injective H.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  obtain ⟨ρ,hact⟩ := CommutingNontrivial.source_exists_center_quotient_action ht d a (MulEquiv.refl D)
  change Representation (ZMod 2) D (Additive (Z Γ a)) at ρ
  change ∀ (l : H) (z : Additive (Z Γ a)),
    ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
      (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹ at hact
  obtain ⟨T₀⟩ := Sylow.nonempty (p := 2) (G := stabilizer Γ a)
  have hgeom := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hz := intrinsic_local_center_eq_bot_of_neighbor_central ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab hgeom.2.2.1
  obtain ⟨S,hS,hgen,hres₀⟩ := CommutingNontrivial.source_center_module_prepared_of_center_eq_bot
    ht d a hz T₀ (MulEquiv.refl D) ρ hact
  have hgT : GeneratedByFixedSpace ρ (T : Subgroup D) := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D S T
    rw [←hg]
    exact generatedByFixedSpace_of_equivariant_surjection ρ ρ
      (MulAut.conj g).toMonoidHom (ρ g)
      (fun v => ⟨ρ g⁻¹ v,ρ.self_inv_apply g v⟩)
      (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,Module.End.mul_apply,ρ.inv_self_apply]) S hgen
  have hZL : Z Γ a ≤ H := CommutingNontrivial.pGroup_le_localGroup Γ d a _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer Γ a)
  have hnZ : H ≤ normalizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
  have hq : IsQuadratic ρ A := by
    rw [←hYq]
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le H (Z Γ a) ⊥ Y
      ρ q (CommutingNontrivial.centerSection H (Z Γ a) hZL hnZ q ρ hact)
    rw [commutator_comm Y (Z Γ a),commutator_comm]
    exact hquadY.le
  have hi := CommutingNontrivial.center_action_fixed_index H (Z Γ a) Y hZL hnZ hYH q ρ hact
  rw [hYq] at hi
  have hle : Nat.card (Additive (Z Γ a) ⧸ fixedSpace ρ A) ≤ Nat.card F := by
    rw [hi,←hindex]
    exact relIndex_le_of_le_left hZY (by rw [hindex]; exact Nat.card_pos.ne')
  have hbound := generated_rank_one_bound_and_selection (MulEquiv.refl D) Mbin ρ T A
    (map_subtype_le _) hq hgT hres₀
  exact ⟨R,hR,hYW,hYZ,hZY,hquadY,hindex,hbound.1.trans hle,
    fun hs => hbound.2 (hle.trans_lt hs)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
