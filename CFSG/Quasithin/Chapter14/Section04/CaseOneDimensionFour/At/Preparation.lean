module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.Preparation
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt

/-!
# The actual order-32 closure in the L₃(2) branch at the original G,T

The original higher-rank hypothesis supplies the natural marking on the
chosen seed. The local Chapter 12 structure and escape implications give
the closure's Frattini and center identities. The order-32 case then has
the checked quaternion central product and self-centralizing order-eight
seed, without reconstructing a universal naturality theorem.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.HigherRankHypothesis
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
/-- Centralizer control from the earlier structure at the same G,T. -/
theorem seed_centralizer_le_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    centralizer (V : Set G) ≤ normalizer (L : Set G) :=
  (Subgroup.centralizer_le_normalizer _).trans (h.seed_normalizer_le_at structural)
end CFSG.Quasithin.Chapter12.Section08.HigherRankHypothesis
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original nonabelian closure has the marked Frattini subgroup and
center intersection. Uniqueness is not needed for these conclusions. -/
theorem source_closure (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    let := setup.chosen.elementary
    IsPGroup 2 F.U ∧ frattini F.U = (F.Vi 1).subgroupOf F.U ∧
      V ⊓ F.ZU = F.Vi 1 := by
  let := setup.chosen.elementary
  let h := setup
  have hnat : 3 ≤ 3 → Nonempty (AmbientNaturalMarking L setup.chosen.normalizes 3) :=
    fun _ => ⟨h.naturalMarking⟩
  refine ⟨F.localKernel_UH_isPGroup d.qtke L (normalizer (L : Set G)) F.H
    (by decide) setup.chosen.le_sylow setup.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual hnat (h.point_mem_Hz_at F alternatives), ?_, ?_⟩
  · exact F.localKernel_frattini_eq_point d.qtke L (normalizer (L : Set G))
      (by decide) setup.chosen.le_sylow setup.chosen.normalizes (h.sylow_normalizes_at structural)
      h.residual hnat (h.flag_escape_at F alternatives) hne
  · let := F.localKernel_tilde_seed_elementary
    exact F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne

/-- The original action kernel, using maximal uniqueness supplied by the
same-ambient structural theorem and the proved A/C application. -/
theorem source_action_kernel (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    letI := setup.chosen.elementary
    (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H := by
  let := setup.chosen.elementary
  let h := setup
  exact F.localKernel_eq_pCore d.qtke L (normalizer (L : Set G)) F.H
    (by decide) setup.chosen.le_sylow setup.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2
    (h.seed_centralizer_le_at structural) h.centralizer_L
    (h.point_mem_Hz_at F alternatives)

/-- The closure is contained in the original Sylow subgroup, not merely
isomorphic to a two-subgroup elsewhere. -/
theorem source_closure_le_sylow (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : F.U ≤ (T : Subgroup G) := by
  let := setup.chosen.elementary
  let h := setup
  exact (F.localKernel_closure d.qtke L (normalizer (L : Set G)) F.H
    (by decide) setup.chosen.le_sylow setup.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.point_mem_Hz_at F alternatives)).2.2.1.1

/-- The original extraspecial case has order 32, or order strictly greater
than 64. This is the bound needed by the actual L₄(2) terminal obstruction. -/
theorem source_extraspecial_order (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) :
    IsExtraspecial 2 F.U ∧ (Nat.card F.U = 32 ∨ 64 < Nat.card F.U) := by
  let := setup.chosen.elementary
  obtain ⟨htwo, hphi, hc⟩ := source_closure d setup structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have hcenter : Nat.card (center F.U) = 2 := by
    rw [center_point F hZ]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show F.Vi 1 ≤ F.U from (F.le_seed 1).trans (le_conjugateSpanBy V F.H))).toEquiv).trans
      (by simpa using F.card 1 (by decide))
  refine ⟨⟨hcenter, inferInstance,
    QuotientGroup.nontrivial_iff.mpr (fun ht => hne (center_eq_top_iff.mp ht))⟩, ?_⟩
  obtain ⟨hd, heven⟩ := quotient_dimension F htwo hphi hc
  let r := Module.finrank (ZMod 2) (Additive F.Uhat)
  have hcard : Nat.card F.U = 2 ^ (r + 1) := by
    have hqcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod] at hqcard
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
    change Nat.card (Additive F.Uhat) * 2 = _
    rw [hqcard, pow_succ]
  by_cases hr : r = 4
  · exact Or.inl (by rw [hcard, hr]; decide)
  · right
    obtain ⟨k, hk⟩ := heven
    have hlarge : 6 < r + 1 := by dsimp [r]; omega
    rw [hcard]
    exact (by decide : 64 = 2 ^ 6) ▸ Nat.pow_lt_pow_right (by decide) hlarge


end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem seed_card (F : InvariantFlag T V 3) : Nat.card V = 8 := by
  simpa [F.last] using F.card 3 (by decide)

omit [Finite G] in
private theorem center_le_seed (F : InvariantFlag T V 3) (hZ : F.ZU = F.Vi 1) :
    center F.U ≤ V.subgroupOf F.U := by
  rw [center_point F hZ]
  exact subgroupOf_mono _ (F.le_seed 1)

/-- The original order-32 closure admits embedded commuting quaternion factors. -/
theorem source_quaternion (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (QuaternionCentralProductData F.U) := by
  let := setup.chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d setup structural alternatives F hne hZ).1
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let : IsElementaryAbelian 2 (V.subgroupOf F.U) := IsElementaryAbelian.subgroupOf hVU
  let : (V.subgroupOf F.U).Normal := Normal.of_commutator_le F.U (by
    rw [IsExtraspecial.commutator_eq_center (p := 2)]
    exact center_le_seed F hZ)
  have hV : Nat.card (V.subgroupOf F.U) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans (seed_card F)
  obtain ⟨B, C, hB, hC, hspan, hinter, hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary hcard
      (V.subgroupOf F.U) hV (center_le_seed F hZ)
  exact ⟨⟨B, C, hB, hC, hinter, hcomm, hspan⟩⟩

/-- The original seed is its own centralizer inside the extraspecial closure. -/
theorem source_seed_centralizer (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    F.U ⊓ centralizer (V : Set G) = V := by
  let := setup.chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d setup structural alternatives F hne hZ).1
  have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
  let : IsElementaryAbelian 2 (V.subgroupOf F.U) := IsElementaryAbelian.subgroupOf hVU
  have hV : Nat.card (V.subgroupOf F.U) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv).trans (seed_card F)
  have hc := extraspecial_two_centralizer_eq_of_card_sq (V.subgroupOf F.U)
    (center_le_seed F hZ) (by rw [hV, hcard]; decide)
  apply le_antisymm
  · intro x hx
    have hm : (⟨x, hx.1⟩ : F.U) ∈ centralizer (V.subgroupOf F.U : Set F.U) := by
      intro v hv
      exact Subtype.ext (hx.2 v hv)
    rw [hc] at hm
    exact hm
  · exact le_inf hVU (le_centralizer V)

omit [Finite G] in
/-- The point normalizer is the ambient centralizer of the actual center of U. -/
theorem point_centralizer (F : InvariantFlag T V 3) (hZ : F.ZU = F.Vi 1) :
    F.H = centralizer (F.ZU : Set G) := by
  rw [hZ]
  exact le_antisymm (normalizer_le_centralizer_of_card_two _
    (by simpa using F.card 1 (by decide))) (Subgroup.centralizer_le_normalizer _)

/-- Source 14.4.4(2): the literal omitted-point intersection equals the seed. -/
theorem source_intersection_eq_seed (d : Counterexample T L)
    (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : F.E g = V := by
  let := setup.chosen.elementary
  have hgV := F.P_le_seed_normalizer L setup.chosen.normalizes hgP
  obtain ⟨htwo, hphi, hc⟩ := source_closure d setup structural alternatives F hne
  have hpU : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi, map_subgroupOf_eq_of_le hpU]
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary (by decide) g htwo hPhi
    (disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) hc g hgV hgH))
  have hVE := F.seed_le_E_of_normalizes g hgV
  apply le_antisymm _ hVE
  exact (show F.E g ≤ F.U ⊓ centralizer (V : Set G) from
    le_inf (inf_le_left.trans inf_le_left)
      ((le_centralizer (F.E g)).trans (centralizer_le hVE))).trans_eq
    (source_seed_centralizer d setup structural alternatives F hne hZ hcard)

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
