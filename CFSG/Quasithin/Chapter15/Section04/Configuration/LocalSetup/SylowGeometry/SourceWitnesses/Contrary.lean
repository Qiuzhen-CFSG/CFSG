module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Placed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.LocalFactors
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.SourceData
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.SourceInputs

/-!
# The original source pairs construct the contrary endgame data

Every module, action, marked quotient and dihedral field is constructed from
the same two source pairs and the placed contrary overgroup. The only earlier
module conclusions used here are containment of the original moved modules
in the Baumann subgroup. The construction does not use LocalData, which would
already contain the Sylow conclusion under proof.

The residual-replacement application separately supplies the actual normal
closure and residual equalities retained below. Characteristic two is the
genuine current branch assumption on that same residual subgroup.
Source: Aschbacher–Smith, 15.4.12, 15.4.14 and 15.4.20, pp.1160–1164.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure EmbeddingReduction CoreElimination
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- Construct the full contrary record without assuming its later module or action fields. -/
noncomputable def contraryData
    (hX : Input κ T M₁ X 2) (hY : Input κ T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hWX : movedModule T M₁ X ≤ ChapterB.baumann (T : Subgroup G))
    (hWY : movedModule T M₂ Y ≤ ChapterB.baumann (T : Subgroup G))
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    {i j : Bool} {H U K : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U)
    (hgen : K ⊔ U = H)
    (hclosure : K = normalClosureIn (geometry pX pY).wholeX H)
    (hres : K = (primeToResidual 3 H).map H.subtype)
    (hchar : generalizedFitting K = pCore 2 K) :
    BlockEndgame.ContraryData κ (geometry pX pY) i j := by
  let d := geometry pX pY
  change BlockEndgame.ContraryData κ d i j
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  have hm₁ : d.M₁ = M₁ := by change normalizer (d.wholeX : Set G) = M₁; rw [hx,hM₁]
  have hm₂ : d.M₂ = M₂ := by change normalizer (d.wholeY : Set G) = M₂; rw [hy,hM₂]
  have hKH : K ≤ H := by rw [hclosure]; exact normalClosureIn_le_overgroup _ _
  have hnorm : H ≤ normalizer (K : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hKH).mp
    rw [hclosure]
    exact normalClosureIn_normal _ _
  have hUH : U ≤ H := h.sylow_image ▸ map_subtype_le _
  have hprod : (K : Set G) * (U : Set G) = (H : Set G) := by
    rw [← hgen]
    exact (coe_mul_of_right_le_normalizer_left K U (hUH.trans hnorm)).symm
  have hvX (a) : d.V₁ a ≤ ChapterB.baumann (T : Subgroup G) := by
    apply le_trans ?_ hWX
    rw [← pX.module_join]
    cases a
    · exact le_sup_left
    · exact le_sup_right
  have hvY (a) : d.V₂ a ≤ ChapterB.baumann (T : Subgroup G) := by
    apply le_trans ?_ hWY
    rw [← pY.module_join]
    cases a
    · exact le_sup_left
    · exact le_sup_right
  refine {
    ambient := hX.ambient
    H := H
    K := K
    U := U
    local_group := h.overgroup.1
    amalgam_le := h.overgroup.2
    sylow := h.sylow
    sylow_image := h.sylow_image
    lower_lt := h.lower
    upper_lt := h.upper
    lower_index := h.lower_index
    upper_index := h.upper_index
    baumann_le := baumann_le_geometry_T₀ pX pY
    thompson := ?_
    omega_center := rfl
    centralizer_Z := hX.center_centralizer
    Z_card := hZcard
    fixed_seed_nontrivial := ?_
    T_le_M₁ := h.T_normalizes
    T_le_M₂ := hm₂.symm ▸ hY.sylow_le
    M₁_maximal := hm₁.symm ▸ hX.maximal
    M₂_maximal := hm₂.symm ▸ hY.maximal
    distinct_locals := by simpa only [hm₁,hm₂] using hne
    unique_X := ?_
    unique_Y := ?_
    outside_Y := h.outside
    VM₁_eq := ?_
    VM₂_eq := ?_
    VM₁_elementary := localV_elementary T M₁ hX.sylow_le
      (hX.ambient.evenCharacteristic T M₁ hX.maximal hX.sylow_le)
    VM₂_elementary := localV_elementary T M₂ hY.sylow_le
      (hY.ambient.evenCharacteristic T M₂ hY.maximal hY.sylow_le)
    X_action := ?_
    Y_action := ?_
    X_commutator := pX.thompson_commutator hX
    Y_commutator := pY.thompson_commutator hY
    X_perfect := pX.quotient.factor_perfect
    Y_perfect := pY.quotient.factor_perfect
    X_quotient_card := pX.quotient.factor_quotient_card
    Y_quotient_card := pY.quotient.factor_quotient_card
    V₁_card := pX.module_card
    V₂_card := pY.module_card
    V₁_le_X := pX.module_le_factor hX
    V₂_le_Y := pY.module_le_factor hY
    V₁_le_baumann := hvX
    V₂_le_baumann := hvY
    X_core_nontrivial := h.core_nontrivial
    X_le_H := h.whole_le
    X_not_normal := ?_
    moved_factor := h.moves
    product := hgen
    product_set := hprod
    residual := hres.symm
    conjugate_closure := hclosure.symm
    characteristic_two := hchar
    marked := h.product
    marked_surjective := h.product_surjective
    marked_kernel := h.product_kernel
    marked_first := h.first_image
    marked_second := h.second_image
    dihedral := ?_ }
  · exact ChapterB.thompsonJ_zero _
  · rw [hx]
    exact hCZ
  · rw [hx,hm₁]
    exact huniqueX
  · rw [hy,hm₂]
    exact huniqueY
  · change localV T M₁ = (normalClosure (d.Z.subgroupOf d.M₁ : Set d.M₁)).map d.M₁.subtype
    rw [hm₁]
    rfl
  · change localV T M₂ = (normalClosure (d.Z.subgroupOf d.M₂ : Set d.M₂)).map d.M₂.subtype
    rw [hm₂]
    rfl
  · rw [hm₁]
    exact pX.quotient.action
  · rw [hm₂]
    exact pY.quotient.action
  · intro hHM
    exact h.outside ((d.Y_le_I i j).trans (h.overgroup.2.trans hHM))
  · apply contrary_dihedral_from_full_product d.wholeX
      (ChapterB.baumann (T : Subgroup G)) U
      (h.sylow_image ▸ h.sylow.isPGroup'.map H.subtype) h.baumann_le
      (h.upper.le.trans h.T_normalizes) h.quotient d.X rfl h.product
      h.product_surjective h.product_kernel h.first_image h.second_image _ i h.moves
    intro u hu V hV
    obtain ⟨σ,hσ⟩ := h.permutes u hu
    rcases Set.mem_insert_iff.mp hV with rfl | hV
    · rw [hσ]
      cases σ false <;> simp [d]
    · have hv := Set.mem_singleton_iff.mp hV
      rw [hv,hσ]
      cases σ true <;> simp [d]

/-- The same raw source fields also give the block sieve input. -/
noncomputable def contraryInput
    (hX : Input κ T M₁ X 2) (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    {i j : Bool} {H U K : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U)
    (hgen : K ⊔ U = H)
    (hclosure : K = normalClosureIn (geometry pX pY).wholeX H)
    (hres : K = (primeToResidual 3 H).map H.subtype)
    (hchar : generalizedFitting K = pCore 2 K) :
    BlockSieve.Input (geometry pX pY) i j H U K where
  placed := h
  seed := rfl
  seed_card := hZcard
  seed_centralizer := hX.center_centralizer
  thompson := ChapterB.thompsonJ_zero _
  factor_commutator := (pX.thompson_commutator hX i).symm
  generation := hgen
  closure := hclosure
  residual := hres
  characteristic_two := hchar

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
