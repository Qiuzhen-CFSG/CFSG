module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualSquareBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionNatural
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# The large linear branch of DGS 8.6 and the last comparison in 8.7

The commuting-intersection condition makes every moving center escape the
opposite core. The residual square bound and the opposite product bound,
together with actual same-orbit transport of quotient Sylow parameters,
contradict the first square comparison unless that center is natural.
Conjugation then gives naturality at the original starting vertex, and the
natural-span calculation identifies the original commutator H with Z_alpha'.

The same residual bound proves that the centralizer of V_beta intersect
Q_alpha' inside V_alpha' lies in Q_beta: an escaping subgroup would give
q_beta squared at most q_beta. This is the final contradiction in 8.7.

The actual beta SL₂ marking, full opposite Sylow index and 8.5 nonnaturality
remain explicit. The path-Borel theorem supplies the Sylow index outside its
middle-dihedral alternative; the 8.5 owner supplies canonical nonnaturality.
These are earlier-source inputs, not action descent or index-bound premises.
Source: DGS, Groups and Graphs (1985), 8.6--8.7, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem linear_omega_le_field {D F : Type*} [Group D] [Finite D]
    [Field F] [Finite F] [CharP F 2] (e : D ≃* SL(2,F)) (T : Sylow 2 D) :
    Nat.card (omegaCenterIn (T : Subgroup D)) ≤ Nat.card F := by
  have hle : omegaCenterIn (T : Subgroup D) ≤ (T : Subgroup D) := map_subtype_le _
  have hc := card_map_of_injective (K := (T : Subgroup D)) (f := e.toMonoidHom) e.injective
  let R := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : Nat.card (R : Subgroup SL(2,F)) = Nat.card F :=
    Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 R).symm.toEquiv
  exact (Nat.card_le_card_of_injective _ (inclusion_injective hle)).trans_eq (hc.symm.trans hR)

private theorem square_product_contradiction (x y : ℕ)
    (hx : x^2 ≤ y) (hy : y^2 ≤ y*x) (hp : 1 < y) : False := by
  nlinarith

/-- In the large linear terminal branch, 8.6(c), the actual path Sylow
index and 8.5 force naturality at both the moving and starting centers,
and identify H with the terminal center. -/
theorem reduced_linear_terminal_commuting_intersection_natural
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    (hinter : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hactor : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (hnatural : ¬ NaturalResidualSection h beta e n) :
    let Γ := Reduction.reducedFamily L S₀
    Noncommuting.HasNaturalCenter (graphLocalGroup Γ w.val) (Z Γ w.val) (Q Γ w.val) ∧
      Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) ∧
      ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = Z Γ a' := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let R : Sylow 2 (graphLocalGroup Γ w.val) := default
  let T : Sylow 2 (graphLocalGroup Γ a') := default
  let U : Sylow 2 (graphLocalGroup Γ beta) := default
  let : Finite (graphLocalGroup Γ beta) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (graphLocalGroup Γ a') := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  let Tq := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ a')))
  have hU : Nat.card (omegaCenterIn Uq.toSubgroup) ≤ Nat.card F := linear_omega_le_field e Uq
  obtain ⟨_,_,_,_,_,_,hparameters⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hTU := hparameters Tq Uq
  have hT : Nat.card (omegaCenterIn Tq.toSubgroup) ≤ Nat.card F := hTU.le.trans hU
  have hnat : Noncommuting.HasNaturalCenter (graphLocalGroup Γ w.val) (Z Γ w.val) (Q Γ w.val) := by
    rcases source_commuting_intersection_natural_or_square ht (Reduction.reduced_borel_core_sylow h)
      d models hc hab hd hb hcomm w hm R U hinter with hn | hs
    · exact hn
    have hEQ : ¬ Z Γ w.val ≤ Q Γ beta := by
      intro hZ
      exact hm (bot_unique ((commutator_mono le_rfl
        (le_inf (Z_neighbor_le_V Γ w.property) hZ)).trans hinter.le))
    have hlo := reduced_critical_nonnatural_residual_square h hc hab hd hb hcomm
      (Reduction.reduced_graph_core_obstruction h a beta hab) hn hF e hactor
      (Z Γ w.val) (Z_neighbor_le_V Γ w.property) hEQ hnatural
    have hup := source_opposite_centralizer_index_le_omega_product ht
      (Reduction.reduced_borel_core_sylow h) d models hc hab hd hb hcomm w hm R T
    have hs' := hs.trans hU
    have hmul := Nat.mul_le_mul_right (Nat.card (omegaCenterIn ((R : Subgroup
      (graphLocalGroup Γ w.val)).map (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ w.val)))))) hT
    have hprod := hlo.trans (hup.trans hmul)
    have hq : 1 < Nat.card F := by
      rw [hF]
      exact Nat.one_lt_pow (by omega) (by decide)
    let qR := Nat.card (omegaCenterIn ((R : Subgroup (graphLocalGroup Γ w.val)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ w.val)))))
    change qR ^ 2 ≤ Nat.card F at hs'
    exact (square_product_contradiction qR (Nat.card F) hs' hprod hq).elim
  have hodd : Odd ((graph Γ).dist a a') := by
    rw [hc.1]
    exact (source_critical_geometry ht d hc hab hd hb hcomm).1
  have hne : a.type ≠ a'.type := (odd_dist_iff Γ ht.generate a a').mp hodd
  have hwn : a'.type ≠ w.val.type := w.property.1
  have hwa : w.val.type = a.type :=
    (Bool.eq_not_of_ne hwn.symm).trans (Bool.eq_not_of_ne hne).symm
  refine ⟨hnat,source_natural_center_of_type ht d hwa hnat,?_⟩
  have hca := critical_end_center_of_commuting Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (fun v => (source_Z_Q_U ht v).2) hc hcomm (d.localGroup a') (d.sylow_or_center a')
  rw [commutator_comm]
  apply source_natural_span_commutator ht (Reduction.reduced_borel_core_sylow h) d
    w.property.symm rfl hca hnat _ inf_le_right
  intro hz
  exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V Γ w.property)).trans
    (by rwa [commutator_comm] at hz : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥).le))

/-- The centralizer of the opposite core intersection inside the terminal
span cannot escape the beta core: such an escape gives the contradictory
square-versus-linear comparison at the end of DGS 8.7. -/
theorem reduced_linear_terminal_centralizer_le_core
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hactor : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (hnatural : ¬ NaturalResidualSection h beta e n) :
    let Γ := Reduction.reducedFamily L S₀
    V Γ a' 1 ⊓ centralizer ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)) ≤
      Q Γ beta := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let A := V Γ beta 1 ⊓ Q Γ a'
  let E := V Γ a' 1 ⊓ centralizer (A : Set (Reduction.G₀ L S₀))
  change E ≤ Q Γ beta
  by_contra hEQ
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hb3 : 3 ≤ b Γ := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V Γ beta 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) beta (by omega)
  have hVL : V Γ beta 1 ≤ d.localGroup a' := pGroup_le_localGroup Γ d a' _
    (IsElementaryAbelian.isPGroup 2 _) (V_le_stabilizer_of_dist_add_le_b Γ ht.generate beta a' 1 hd.le)
  let : Finite (d.localGroup a') := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  let : Finite (graphLocalGroup Γ beta) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let T : Sylow 2 (d.localGroup a') := default
  let Tq := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (d.localGroup a')))
  let U : Sylow 2 (graphLocalGroup Γ beta) := default
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  obtain ⟨_,_,_,_,_,_,hparameters⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hT : Nat.card (omegaCenterIn Tq.toSubgroup) ≤ Nat.card F :=
    (hparameters Tq Uq).le.trans (linear_omega_le_field e Uq)
  have hlo := reduced_critical_nonnatural_residual_square h hc hab hd hb hcomm
    (Reduction.reduced_graph_core_obstruction h a beta hab) hn hF e hactor E inf_le_left hEQ hnatural
  have hAC : A ≤ centralizer (E : Set (Reduction.G₀ L S₀)) := le_centralizer_iff.mp inf_le_right
  have hupper := relIndex_le_of_le_left hAC (A.subgroupOf (V Γ beta 1)).index_ne_zero_of_finite
  change (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) ≤
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hupper
  rw [inf_relIndex_left] at hupper
  have hcore := source_elementary_core_index_le_omega ht d a' (models a') (V Γ beta 1) hVL T
  have hsq : Nat.card F ^ 2 ≤ Nat.card F := hlo.trans (hupper.trans (hcore.trans hT))
  have hpos : 1 < Nat.card F := by rw [hF]; exact Nat.one_lt_pow (by omega) (by decide)
  exact (Nat.not_lt_of_ge hsq) (by nlinarith only [hpos])

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
