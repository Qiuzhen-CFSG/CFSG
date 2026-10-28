module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ModelCases
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ResidualReduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.Models
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Inputs to the surviving exchanged-block endgame

This interface retains the initial geometry of the contrary Sylow overgroup,
including the full marked symmetric-three product and its dihedral action.
The modules V(Mᵢ) are the actual conjugate closures of Z, as specified on
printed p.1157; V₁ and V₂ remain the commutators in `Source.Geometry`.
Only that raw geometry is used, not the later `Source.LocalData` record
which already assumes the Sylow conclusion of 15.4.20.

The surviving block is an explicit intermediate input from the block sieve.
It retains relative subnormality, the intrinsic two-core quotient and the
natural-module block type. It contains no Borel placement, field-four bound
or centrality conclusion. The two independent remaining deductions are
the Borel/module placement and centrality once the field order is four.
The source assembly must construct these data from its preceding results.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.4.12, 15.4.14 and the proof of 15.4.20, printed pp.1160–1164.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The source inputs before the Borel or centrality argument. All normal
closures and residuals are formed intrinsically and then embedded in G. -/
structure ContraryData (κ : GroupClass) (d : Source.Geometry G) (i j : Bool) where
  ambient : IsSimpleQTKE κ G
  H : Subgroup G
  K : Subgroup G
  U : Subgroup G
  local_group : H ∈ Chapter1.H G
  amalgam_le : d.I i j ≤ H
  sylow : Sylow 2 H
  sylow_image : (sylow : Subgroup H).map H.subtype = U
  lower_lt : d.T₀ < U
  upper_lt : U < (d.T : Subgroup G)
  lower_index : d.T₀.relIndex U = 2
  upper_index : U.relIndex (d.T : Subgroup G) = 2
  baumann_le : ChapterB.baumann (d.T : Subgroup G) ≤ d.T₀
  thompson : d.J = elementaryAbelianMaxJ (d.T : Subgroup G)
  omega_center : d.Z = omegaOneCenterAmbient (d.T : Subgroup G)
  centralizer_Z : centralizer (d.Z : Set G) = (d.T : Subgroup G)
  Z_card : Nat.card d.Z = 4
  fixed_seed_nontrivial : d.Z ⊓ centralizer (d.wholeX : Set G) ≠ ⊥
  T_le_M₁ : (d.T : Subgroup G) ≤ d.M₁
  T_le_M₂ : (d.T : Subgroup G) ≤ d.M₂
  M₁_maximal : IsMaximalTwoLocal d.M₁
  M₂_maximal : IsMaximalTwoLocal d.M₂
  distinct_locals : d.M₁ ≠ d.M₂
  unique_X : ∀ N : Subgroup G, IsMaximalTwoLocal N →
    d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁
  unique_Y : ∀ N : Subgroup G, IsMaximalTwoLocal N →
    d.wholeY ⊔ (d.T : Subgroup G) ≤ N → N = d.M₂
  outside_Y : ¬ d.Y j ≤ d.M₁
  VM₁_eq : d.VM₁ =
    (normalClosure (d.Z.subgroupOf d.M₁ : Set d.M₁)).map d.M₁.subtype
  VM₂_eq : d.VM₂ =
    (normalClosure (d.Z.subgroupOf d.M₂ : Set d.M₂)).map d.M₂.subtype
  VM₁_elementary : IsElementaryAbelian 2 d.VM₁
  VM₂_elementary : IsElementaryAbelian 2 d.VM₂
  X_action : TwoFactors.MixedLocal.FactorPairAction d.M₁ d.X
  Y_action : TwoFactors.MixedLocal.FactorPairAction d.M₂ d.Y
  X_commutator : ∀ a, ⁅d.X a, d.J⁆ = d.X a
  Y_commutator : ∀ a, ⁅d.Y a, d.J⁆ = d.Y a
  X_perfect : ∀ a, IsPPerfect 2 (d.X a)
  Y_perfect : ∀ a, IsPPerfect 2 (d.Y a)
  X_quotient_card : ∀ a, Nat.card (d.X a ⧸ pCore 2 (d.X a)) = 3
  Y_quotient_card : ∀ a, Nat.card (d.Y a ⧸ pCore 2 (d.Y a)) = 3
  V₁_card : ∀ a, Nat.card (d.V₁ a) = 4
  V₂_card : ∀ a, Nat.card (d.V₂ a) = 4
  V₁_le_X : ∀ a, d.V₁ a ≤ d.X a
  V₂_le_Y : ∀ a, d.V₂ a ≤ d.Y a
  V₁_le_baumann : ∀ a, d.V₁ a ≤ ChapterB.baumann (d.T : Subgroup G)
  V₂_le_baumann : ∀ a, d.V₂ a ≤ ChapterB.baumann (d.T : Subgroup G)
  X_core_nontrivial : d.wholeX.pCoreIn 2 ≠ ⊥
  X_le_H : d.wholeX ≤ H
  X_not_normal : ¬ H ≤ d.M₁
  moved_factor : ¬ U ≤ normalizer (d.X i : Set G)
  product : K ⊔ U = H
  product_set : (K : Set G) * (U : Set G) = (H : Set G)
  residual : (primeToResidual 3 H).map H.subtype = K
  conjugate_closure :
    (normalClosure (d.wholeX.subgroupOf H : Set H)).map H.subtype = K
  characteristic_two : generalizedFitting K = pCore 2 K
  marked : (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G) →*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  marked_surjective : Function.Surjective marked
  marked_kernel : marked.ker =
    pCore 2 (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G)
  marked_first : ((d.X false).subgroupOf
    (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G))).map marked =
      (alternatingGroup (Fin 3)).prod ⊥
  marked_second : ((d.X true).subgroupOf
    (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G))).map marked =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3))
  dihedral : Nonempty (((quotientAut (pCore 2 d.wholeX)).comp
    (d.wholeX.normalizerMonoidHom.comp (inclusion (upper_lt.le.trans T_le_M₁)))).range
      ≃* DihedralGroup 4)

/-- The genuine surviving block and the component input allowed from C.2.7.
The second block is its actual ambient conjugate; no direct-product
identification or independent action of the internal factors is assumed. -/
structure ExchangedBlock {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
    (c : ContraryData κ d i j) where
  first : Subgroup G
  first_le : first ≤ c.H
  relative_block : ChapterC.IsBlock (first.subgroupOf c.H)
  quotient_quasisimple : IsQuasisimple (first ⧸ pCore 2 first)
  n : ℕ
  even_parameter : Even n
  model : ChapterC.IsL2EvenBlock first n
  exchanger : G
  exchanger_mem : exchanger ∈ c.U
  exchanger_moves : exchanger ∉ normalizer (first : Set G)
  product : first ⊔ first.map (MulAut.conj exchanger).toMonoidHom = c.K
  product_set : (first : Set G) *
    (first.map (MulAut.conj exchanger).toMonoidHom : Set G) = (c.K : Set G)
  core_normalizes : (d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2 ≤
    normalizer (first : Set G)

namespace ContraryData
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable (c : ContraryData κ d i j)
include c

/-- The central omega subgroup lies in U through the source Baumann containment. -/
theorem Z_le_U : d.Z ≤ c.U := by
  apply le_trans (show d.Z ≤ ChapterB.baumann (d.T : Subgroup G) from ?_)
    (c.baumann_le.trans c.lower_lt.le)
  intro z hz
  rw [c.omega_center] at hz
  have hzT := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  refine ⟨hzT.1, mem_centralizer_iff.mpr ?_⟩
  intro w hw
  have hJT : elementaryAbelianMaxJ (d.T : Subgroup G) ≤ (d.T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  exact hzT.2.2 w (hJT ((mem_omegaOneCenterAmbient_iff _ _).mp hw).1)

/-- The fixed seed centralizes U because it lies in the center of T. -/
theorem fixed_seed_centralizes_U :
    d.Z ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (c.U : Set G) := by
  intro z hz
  apply mem_centralizer_iff.mpr
  intro u hu
  rw [c.omega_center] at hz
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz.1).2.2 u (c.upper_lt.le hu)

/-- The prescribed conjugate closure supplies normalization of V(M₁). -/
theorem normalizes_VM₁ : d.M₁ ≤ normalizer (d.VM₁ : Set G) := by
  rw [c.VM₁_eq]
  apply le_normalizer_iff.mpr
  intro g hg v hv
  obtain ⟨v, hv, rfl⟩ := hv
  exact ⟨(⟨g, hg⟩ : d.M₁) * v * (⟨g, hg⟩ : d.M₁)⁻¹,
    (normalClosure_normal (s := (d.Z.subgroupOf d.M₁ : Set d.M₁))).conj_mem v hv ⟨g, hg⟩,
    rfl⟩

/-- Two-perfectness and the actual factor action give normalization of V₁. -/
theorem normalizes_four {B : Subgroup G} (hBM : B ≤ d.M₁) (hB : IsPPerfect 2 B) :
    B ≤ normalizer (d.V₁ i : Set G) :=
  twoPerfect_normalizes_factor_modules c.X_action hBM hB c.normalizes_VM₁ i

/-- The actual four-module is generated by its commutators with its source
factor. This uses two-perfectness, not an assumed fixed-point-free action. -/
theorem four_commutator : ⁅d.V₁ i, d.X i⁆ = d.V₁ i := by
  have hXM : d.X i ≤ d.M₁ := by
    apply le_trans (show d.X i ≤ d.wholeX from ?_) d.wholeX.le_normalizer
    cases i
    · exact le_sup_left
    · exact le_sup_right
  let := c.VM₁_elementary
  exact commutator_isPPerfect_idempotent (d.X i) d.VM₁ (c.X_perfect i)
    (IsElementaryAbelian.isPGroup 2 d.VM₁) (hXM.trans c.normalizes_VM₁)

/-- The source four-module lies in the actual core R=O₂(XU). -/
theorem four_le_contrary_core : d.V₁ i ≤ (d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2 := by
  let := c.VM₁_elementary
  let P := d.wholeX ⊔ c.U
  have hPM : P ≤ d.M₁ :=
    sup_le d.wholeX.le_normalizer (c.upper_lt.le.trans c.T_le_M₁)
  have hXP : d.X i ≤ P := by
    cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  have hnorm : P ≤ normalizer ((d.VM₁ ⊓ P : Subgroup G) : Set G) :=
    (le_inf (hPM.trans c.normalizes_VM₁) P.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hVM : d.V₁ i ≤ d.VM₁ :=
    le_normalizer_iff_commutator_le_left.mp
      (hXP.trans (hPM.trans c.normalizes_VM₁))
  exact (le_inf hVM ((c.V₁_le_X i).trans hXP)).trans
    (le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 d.VM₁).to_le inf_le_left) inf_le_right hnorm)

/-- The given core-normalization conclusion applies to the actual four-module. -/
theorem four_normalizes_first (b : ExchangedBlock c) :
    d.V₁ i ≤ normalizer (b.first : Set G) :=
  c.four_le_contrary_core.trans b.core_normalizes


/-- Characteristic normalizers of the contrary core are already controlled
by the source uniqueness assertion. -/
theorem core_characteristic_control :
    characteristicNormalizerClosure ((d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2) ≤ d.M₁ :=
  contrary_core_characteristic_control c.upper_lt.le c.upper_index c.T_le_M₁ c.unique_X

/-- Uniqueness controls the centralizer of the nontrivial fixed seed. -/
theorem fixed_seed_centralizer :
    centralizer ((d.Z ⊓ centralizer (d.wholeX : Set G) : Subgroup G) : Set G) ≤ d.M₁ :=
  fixed_seed_centralizer_le c.omega_center c.fixed_seed_nontrivial c.unique_X

end ContraryData
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
