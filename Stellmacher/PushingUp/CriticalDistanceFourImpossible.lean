module
public import Stellmacher.PushingUp.DistanceFourUNormal
public import Stellmacher.PushingUp.DistanceFourResidualAction
public import Stellmacher.PushingUp.DistanceFourActionKernel
public import Stellmacher.PushingUp.FourElementActionInvolution
public import Theory.GroupAction.SubgroupConjugation

/-!
# Critical distance four is impossible

Under Stellmacher's pushing-up hypotheses (P) and (A), the critical distance
cannot equal four. This completes the p = 2 contradiction in (3.3)(f), with
finiteness required only for M and its transported vertex stabilizers.

The chosen three-shift configuration supplies U = Z_a Z_c Z_u and nontrivial
Y = [Z_u,Z_c]. The imported center and normality calculations identify the
actual quotient U/Z_a as an elementary abelian group of order four and give
G_a its conjugation action. We descend this exact action through invariant
Z_a. The factorization Q_a = DU puts Q_a in its kernel, while residual vertex
transport proves that its image is not a two-group. The generation equation
(Z_v Z_a')Q_a = G_a gives two two-group generators modulo that kernel.
Four-element action recognition therefore supplies the natural SL₂(2)
action. An involution in U outside Z_a then forces U itself elementary
abelian, contradicting the nontrivial commutator Y.

The source's barred U is not silently identified with U: the actual center,
quotient cardinality, and normality of U are separately proved prerequisites.
No finiteness of the free amalgam or the vertex set is assumed.

Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.3)(f),
journal pp.14–15, specialized to p = 2.
-/

namespace Stellmacher.PushingUp
open AmalgamGraph
universe u
variable {M : Type u} [Group M]

set_option maxHeartbeats 900000 in
/-- The critical-distance-four case contradicts the nontrivial shifted commutator. -/
public theorem criticalDistance_four_impossible [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M))) :
    criticalDistance S ≠ 4 := by
  intro hb4
  obtain ⟨a, a', c, u, v, cfg⟩ :=
    distanceFour_configuration_exists S T hTS hP hSne hA hb4
  have hi := distanceFour_initialRelations S T hTS hP hSne hA a a' c u v hb4 cfg
  have hc := distanceFour_center_and_index S T hTS hP hSne hA a a' c u v hb4 cfg
  let G := stabilizer S a
  let U := DistanceFour.U S a c u
  let Za := vertexZ S a
  let Z := Za.subgroupOf U
  have hZn : Z.Normal := by
    change ((vertexZ S a).subgroupOf (DistanceFour.U S a c u)).Normal
    rw [← hc.1]
    infer_instance
  let _ : Z.Normal := hZn
  let W := U ⧸ Z
  let _ : IsElementaryAbelian 2 W :=
    distanceFour_centralQuotient_elementary S T hTS hP hSne hA a a' c u v hb4 cfg
  have hcard : Nat.card W = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hc.2
  have hUG : U ≤ G := hi.U_le_core.trans (Subgroup.map_subtype_le _)
  have hGU : G ≤ Subgroup.normalizer U :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUG).mp
      (distanceFour_U_normal S T hTS hP hSne hA a a' c u v hb4 cfg)
  let _ : MulDistribMulAction G U :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer G U hGU
  have hGZa : G ≤ Subgroup.normalizer Za :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (vertexZ_le_stabilizer S a)).mp
      (vertexZ_normal_stabilizer S a)
  have hZinv : IsInvariant G U Z := by
    constructor
    intro g w
    change (w : FreeAmalgam S) ∈ Za ↔
      (g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹ ∈ Za
    exact Subgroup.mem_normalizer_iff.mp (hGZa g.property) w
  let _ : MulDistribMulAction G W := quotientMulDistribMulAction Z hZinv
  have hconjU : ∀ g : G, ∀ w : U,
      (g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹ ∈ U :=
    fun g w => (Subgroup.mem_normalizer_iff.mp (hGU g.property) w).mp w.property
  have hact : ∀ (g : G) (w : U),
      g • (QuotientGroup.mk' Z) w = (QuotientGroup.mk' Z)
        ⟨(g : FreeAmalgam S) * w * (g : FreeAmalgam S)⁻¹, hconjU g w⟩ := by
    intros
    rfl
  let f := MulDistribMulAction.toMulAut G W
  have hQker : pCore 2 G ≤ f.ker := by
    have h := distanceFour_core_le_quotient_fix S T hTS hP hSne hA
      a a' c u v hb4 cfg hZn hconjU hact
    rwa [fixingSubgroup_univ_eq_ker_toMulAut] at h
  have hnp : ¬ IsPGroup 2 f.range :=
    distanceFour_action_image_not_two S T hTS hP hSne hA
      a a' c u v hb4 cfg hZn hconjU hact
  let P := (vertexZ S v).subgroupOf G
  let Q := (vertexZ S a').subgroupOf G
  have hFG : DistanceFour.F S a' v ≤ G := by
    change DistanceFour.F S a' v ≤ stabilizer S a
    rw [← hi.F_generates_modulo_core]
    exact le_sup_left
  have hZvG : vertexZ S v ≤ G := le_sup_left.trans hFG
  have hZa'G : vertexZ S a' ≤ G := le_sup_right.trans hFG
  have hb : 0 < criticalDistance S := by omega
  obtain ⟨_, _, haa⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    a a' cfg.critical hb
  obtain ⟨_, _, hva⟩ := criticalPair_actionInputs S T hTS hP hSne hA
    v a cfg.second_shift.shifted_critical hb
  have hPtwo : IsPGroup 2 P :=
    ((omegaOneCenterAmbient_elementaryAbelian (vertexTwoCore S v)).isPGroup.to_le
      hva.left_Z_le_coreOmega).of_equiv (Subgroup.subgroupOfEquivOfLe hZvG).symm
  have hQtwo : IsPGroup 2 Q :=
    ((omegaOneCenterAmbient_elementaryAbelian (vertexTwoCore S a')).isPGroup.to_le
      haa.right_Z_le_coreOmega).of_equiv (Subgroup.subgroupOfEquivOfLe hZa'G).symm
  have hgenQ : (P ⊔ Q) ⊔ pCore 2 G = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hZvG,
      Subgroup.map_subgroupOf_eq_of_le hZa'G]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hi.F_generates_modulo_core
  have hgen : (P ⊔ Q) ⊔ f.ker = ⊤ :=
    top_unique (hgenQ ▸ sup_le_sup_left hQker (P ⊔ Q))
  have hZaU : Za ≤ U := le_sup_left.trans le_sup_left
  have hZsq : ∀ z : FreeAmalgam S, z ∈ Za → z ^ 2 = 1 := by
    intro z hz
    exact (mem_omegaOneCenterAmbient_iff _ z).mp (haa.left_Z_le_coreOmega hz) |>.2.1
  obtain ⟨x, hxU, hxZ, hxsq⟩ := hi.outside_involution
  let _ : IsElementaryAbelian 2 U :=
    elementaryAbelian_of_four_element_action_involution G U Za hZaU
      hi.Z_centralizes_U hZsq hZn hcard P Q hPtwo hQtwo hgen hnp hconjU hact
      x hxU hxZ hxsq
  apply hi.Y_ne_bot
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hzU : z ∈ U := (show vertexZ S u ≤ U from le_sup_right) hz
  have hwU : w ∈ U := (show vertexZ S c ≤ U from le_sup_right.trans le_sup_left) hw
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm
    (⟨w, hwU⟩ : U) (⟨z, hzU⟩ : U))

end Stellmacher.PushingUp
