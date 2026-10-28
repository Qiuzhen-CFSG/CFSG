module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.LocalRestrictions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Solvable
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Components

/-!
# Assembling the normal reduction in 15.3.58

The earlier source data concern the literal `H = C_G(Z)`, `U = ⟨ZS^H⟩`,
`H* = H/O₂(H)` and `U/Z`. The theorem `normal_reduction_of_earlier_source`
constructs the common starting point for both recognition branches. Its
conclusion includes a minimal normal actor, its actual simple direct-power
isomorphism, its genuine two-residual, and the full alternative in 15.3.57(2).

First the 15.3.54(4) coordinates force `P/V = 1` if `s = 0`, contradicting
15.3.9. The actual preimage of the displacement-plane stabilizer and the
15.3.46 normalizer control yield the three-prime restrictions. Faithful
irreducibility gives commutator generation. The solvable-case proof excludes
two and three, then identifies the odd-prime commutator with C₅ and contradicts
the marked D₈ action constructed inside the earlier extraspecial product.
The nonsolvable minimal-normal theorem and the SQTK rank bound give one or
two simple factors. Their constituent dimension bound feeds the fixed-line
argument proving the irreducible-or-two-transvections alternative.

The source-theorem parent must supply exactly the following earlier facts in
`EarlierSourceInputs`; none is a later recognition conclusion:

* The standing SQTK hypothesis on H, Sylow T, line containments and sizes,
  T-normalization of V, and centrality of ZS/Z from 15.3.48(2).
* The action kernel from 15.3.48(3), and the paired fixed line from 15.3.56(7).
* The order of V*, marked generator, displacement identity and rank, and
  order eight of V∩U from 15.3.53(2); the total degree from 15.3.56(2).
* The strict containment in 15.3.9; the relative Y-normalization and
  `I = YU`, centrality of V in P, and underlying coordinates of the two
  sums of s binary natural planes in 15.3.54(1),(2),(4). The relative
  normality of the quotient denominator is proved from that centrality.
* The nondegenerate four-dimensional quadratic space V, the actual
  singularity implication of 15.3.46(2), and 15.3.49(4),(5).
* For positive s, the marked extraspecial product in 15.3.56(6), whose center
  is V*, containing the elementary group of order `2^(s+1)` in 15.3.56(4).
  The dihedral subgroup itself is constructed, not supplied as an input.

The generic class C is retained for the actual simple carrier, so a source
application can use the full known-simple catalogue. The coordinate-component
embeddings and their normality inside K are re-exported from `Components`.
No normality of individual components in H* is asserted.

This completes the conditional normal-reduction contract. The recognition of
H* as Aut(L₃(2)) remains with the parent, which must discharge these earlier
inputs and the two subsequent recognition branches.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1148–1149 (PDF pp.1165–1166), 15.3.57(2) and the opening of 15.3.58.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

variable {G : Type*} [Group G] [Finite G]
variable (Z ZS V M : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]

/-- Genuine earlier-source inputs for the normal reduction, on the literal
actor and vector quotients. No constituent alternative, positivity,
nonsolvability, or component count is part of this input. -/
structure EarlierSourceInputs (C : GroupClass) (v : ActorQuotient Z) (s : ℕ) where
  sqtk : IsSQTK C (centralizerH Z)
  T : Sylow 2 G
  T_le_H : (T : Subgroup G) ≤ centralizerH Z
  Z_le_ZS : Z ≤ ZS
  Z_card : Nat.card Z = 2
  ZS_card : Nat.card ZS = 4
  ZS_commutator_T : ⁅ZS, (T : Subgroup G)⁆ ≤ Z
  kernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)
  J : Subgroup (centralizerH Z)
  J_le_T : J ≤ (T : Subgroup G).subgroupOf (centralizerH Z)
  fixed_line :
    letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS
  V_le_H : V ≤ centralizerH Z
  T_normalizes_V : (T : Subgroup G) ≤ normalizer (V : Set G)
  Vstar_card : Nat.card (actorImage Z V) = 2
  marking : zpowers v = actorImage Z V
  ZS_le_V : ZS ≤ V
  displacement : LinearMap.range (actorRepresentation Z ZS kernel v - LinearMap.id) =
    LocalRestrictions.vectorSubspace Z ZS (V ⊓ closureU Z ZS)
  displacement_rank : Module.finrank (ZMod 2)
    (LinearMap.range (actorRepresentation Z ZS kernel v - LinearMap.id)) = 2
  dimension : Module.finrank (ZMod 2) (Space Z ZS) = 2 * (s + 2)
  Y : Subgroup G
  g : G
  pair_I : pairI Z ZS g = Y ⊔ closureU Z ZS
  U_normalizes_Y : closureU Z ZS ≤ normalizer (Y : Set G)
  V_lt_coreY : V < Stellmacher.twoCoreAmbient Y
  central_pairP : V ≤ centralizer (pairP Z ZS g : Set G)
  pair_decomposition :
    letI := LocalRestrictions.pair_denominator_normal Z ZS V g central_pairP
    Nonempty ((pairP Z ZS g ⧸ V.subgroupOf (pairP Z ZS g)) ≃*
      (Fin 2 → Fin s → Multiplicative (Fin 2 → ZMod 2)))
  quadratic : QuadraticForm (ZMod 2) (Additive V)
  nondegenerate : quadratic.polarBilin.Nondegenerate
  V_dimension : Module.finrank (ZMod 2) (Additive V) = 4
  singularity_46 : ∀ A : Subgroup G, ⊥ < A → A < V →
    ¬ normalizer (A : Set G) ≤ M → FusionCore.IsTotallySingular quadratic A
  VU_card : Nat.card (V ⊓ closureU Z ZS : Subgroup G) = 8
  MH_three : Nat.Coprime 3 (Nat.card (M ⊓ centralizerH Z : Subgroup G))
  ZS_normalizer_three : Nat.Coprime 3 (Nat.card (normalizer (ZS : Set G)))
  extraspecial_product : 0 < s → ∃ P : Subgroup (ActorQuotient Z),
    IsExtraspecial 2 P ∧ ∃ X : Subgroup P, IsElementaryAbelian 2 X ∧
      Nat.card X = 2 ^ (s + 1) ∧
      (center P).map P.subtype = actorImage Z V

variable {Z ZS V M}

/-- The full 15.3.57(2) conclusion, after discharging fixed-line containment
and centralization by the Sylow image from the earlier marked source facts. -/
theorem constituent_conclusion_of_earlier_source {C : GroupClass}
    {v : ActorQuotient Z} {s : ℕ} (d : EarlierSourceInputs Z ZS V M C v s)
    (K : Subgroup (ActorQuotient Z)) [K.Normal]
    (hsmall : ∀ A : Subrepresentation ((actorRepresentation Z ZS d.kernel).comp K.subtype),
      A.toRepresentation.IsIrreducible → 3 ≤ Module.finrank (ZMod 2) A.toSubmodule) :
    NormalConstituentConclusion (actorRepresentation Z ZS d.kernel) K v s := by
  exact LocalRestrictions.normalConstituentConclusion_of_marked_source Z ZS d.kernel
    d.T d.T_le_H d.Z_le_ZS d.Z_card d.ZS_card d.ZS_commutator_T
    d.J d.J_le_T d.fixed_line V d.V_le_H d.T_normalizes_V d.Vstar_card
    d.ZS_le_V K v s d.marking d.displacement hsmall d.displacement_rank d.dimension

/-- The output for a selected minimal normal actor. The coordinate isomorphism
identifies actual nonabelian simple subgroups and retains the full K-class. -/
structure MinimalNormalConclusion (C : GroupClass)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (K : Subgroup (ActorQuotient Z)) (v : ActorQuotient Z) (s : ℕ) : Prop where
  minimal : IsMinimalNormal K
  nonsolvable : ¬ Group.IsSolvable K
  perfect : Group.IsPerfect K
  two_residual : pResidual 2 K = ⊤
  two_residual_image : (pResidual 2 K).map K.subtype = K
  commutator_span :
    (⨆ a : K, LinearMap.range (actorRepresentation Z ZS hkernel a - LinearMap.id)) = ⊤
  simple_power : ∃ S : Subgroup K, IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧ C S ∧
    ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nonempty (K ≃* (Fin n → S))
  constituent_rank : ∀ A : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype),
    A.toRepresentation.IsIrreducible → 3 ≤ Module.finrank (ZMod 2) A.toSubmodule
  constituents : NormalConstituentConclusion (actorRepresentation Z ZS hkernel) K v s

/-- Common input to both recognition branches of 15.3.58, all on the actual
quotient action. The stabilizer preimage explicitly preserves the quotient
convention; the line centralizer is the pointwise linear fixer. -/
structure SourceReductionConclusion (C : GroupClass)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (V M : Subgroup G) (v : ActorQuotient Z) (s : ℕ) : Prop where
  positive : 0 < s
  involution : IsInvolution v
  irreducible : (actorRepresentation Z ZS hkernel).IsIrreducible
  centralizer_le : centralizer (actorImage Z V : Set (ActorQuotient Z)) ≤ actorImage Z M
  plane_three : Nat.Coprime 3 (Nat.card (subspaceStabilizer (actorRepresentation Z ZS hkernel)
    (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id))))
  line_three : Nat.Coprime 3 (Nat.card (subspaceKernel (actorRepresentation Z ZS hkernel)
    (LocalRestrictions.vectorSubspace Z ZS ZS) ⊤))
  centralizer_three : Nat.Coprime 3
    (Nat.card (centralizer (actorImage Z V : Set (ActorQuotient Z))))
  plane_preimage : (subspaceStabilizer (actorRepresentation Z ZS hkernel)
    (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id))).comap
      (QuotientGroup.mk' (pCore 2 (centralizerH Z))) =
    (normalizer (V ⊓ closureU Z ZS : Set G)).subgroupOf (centralizerH Z)
  normal_actor : ∃ K : Subgroup (ActorQuotient Z), MinimalNormalConclusion C hkernel K v s

/-- The opening normal reduction of 15.3.58 from genuine earlier source inputs.
Positivity, all three quotient restrictions, nonsolvability, the simple-power
bound, and the complete constituent alternative are proved here. -/
theorem normal_reduction_of_earlier_source {C : GroupClass}
    {v : ActorQuotient Z} {s : ℕ} (d : EarlierSourceInputs Z ZS V M C v s) :
    SourceReductionConclusion C d.kernel V M v s := by
  let := LocalRestrictions.pair_denominator_normal Z ZS V d.g d.central_pairP
  have hs := LocalRestrictions.positive_of_source_decomposition Z ZS V d.Y d.g s
    d.pair_I d.U_normalizes_Y d.V_lt_coreY d.pair_decomposition
  have hρ := actorRepresentation_irreducible_of_pair_fixed_line Z ZS d.kernel
    d.T d.T_le_H d.Z_le_ZS d.Z_card d.ZS_card d.ZS_commutator_T
    d.J d.J_le_T d.fixed_line
  obtain ⟨hCM, hplane, hline, hCV⟩ := LocalRestrictions.three_prime_restrictions_of_source
    Z ZS d.kernel V M d.quadratic d.nondegenerate d.V_dimension d.singularity_46
    d.VU_card v d.marking d.ZS_le_V d.Z_le_ZS d.displacement d.MH_three d.ZS_normalizer_three
  have horder : orderOf v = 2 := by
    rw [← Nat.card_zpowers, d.marking, d.Vstar_card]
  have hv : IsInvolution v := ⟨fun he => by simp [he] at horder, by
    have hh := pow_orderOf_eq_one v
    rwa [horder] at hh⟩
  have hC : ¬ 3 ∣ Nat.card (centralizer ({v} : Set (ActorQuotient Z))) := by
    have hc := hCV
    rw [← d.marking, zpowers_eq_closure, centralizer_closure] at hc
    exact Nat.prime_three.coprime_iff_not_dvd.mp hc
  obtain ⟨P, hP, X, hX, hXcard, hcenter⟩ := d.extraspecial_product hs
  let := hP
  let := hX
  have hcenter' : (center P).map P.subtype = zpowers v := hcenter.trans d.marking.symm
  obtain ⟨K, hK, hspan⟩ := exists_minimalNormal_actor Z ZS d.kernel hρ v d.displacement_rank
  let := hK.1
  have hns := actor_minimalNormal_not_solvable Z ZS d.kernel hρ K hK v hv s hs hC
    d.displacement_rank d.dimension P X hXcard hcenter'
  obtain ⟨hperfect, hresidual, _, hsmall⟩ := actor_nonsolvable_minimalNormal_reduction
    Z ZS d.kernel hρ d.sqtk.stronglyQuasithin K hK hns
  refine ⟨hs, hv, hρ, hCM, hplane, hline, hCV, ?_, K, ?_⟩
  · exact LocalRestrictions.displacement_stabilizer_preimage Z ZS d.kernel V v
      (d.Z_le_ZS.trans d.ZS_le_V) d.Z_le_ZS d.displacement
  · exact ⟨hK, hns, hperfect, hresidual, hK.map_twoResidual_eq_self K hns,
      hspan, actor_simple_power_of_sqtk Z d.sqtk K hK hns, hsmall,
      constituent_conclusion_of_earlier_source d K hsmall⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
