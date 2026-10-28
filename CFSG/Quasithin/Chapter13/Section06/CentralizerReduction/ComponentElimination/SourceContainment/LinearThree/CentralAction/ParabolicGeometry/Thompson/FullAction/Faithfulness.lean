module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction.Construction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction.Kernel

/-!
# Faithfulness of the full doubled action

The commuting residual image is normal in the full plus group. Its two-core
vanishes, so the genuine cubic quotient maps onto a group of order dividing
three. Its nontrivial action on U_K makes that action faithful. The marked
component is centerless and faithful, and the quotient by both normal factors
is a two-group. Thus the kernel on U_K is a normal two-group and is trivial.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.11 and the central branch of 13.6.20, printed pp.928 and 931.
-/

@[expose] public section
open Subgroup Representation BinaryLinearThree
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction
open ComponentSelection ModuleAlternatives
variable {G : Type*} [_root_.Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}
variable (e : EarlierData K L T z v)
variable (d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed)

/-- The literal surjection from the residual to its plus image. -/
noncomputable def residualPlus : Lv L v →*
    plusImage K L T z v e.normalizeL e.fixSeed (Lv L v) :=
  ((plusMk K L T z v e.normalizeL e.fixSeed).comp
    (inclusion (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left))).codRestrict _
      (fun l => mem_map.mpr ⟨⟨l, (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left) l.property⟩, l.property, rfl⟩)

omit [Finite G] in
theorem residualPlus_surjective : Function.Surjective (residualPlus e) := by
  rintro ⟨l, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

/-- Nontriviality is measured on U_K itself. -/
theorem residual_action_ne_one
    (hne : ⁅UK K L T z v, Lv L v⁆ ≠ ⊥) :
    (action e d).comp (plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)).subtype ≠ 1 := by
  intro hf
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro u hu l hl
  let a : plusActor K L T v := ⟨l, (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left) hl⟩
  have ha : action e d (plusMk K L T z v e.normalizeL e.fixSeed a) = 1 :=
    DFunLike.congr_fun hf (residualPlus e ⟨l, hl⟩)
  have he := equivariant e d a ⟨u, hu⟩
  rw [ha] at he
  have hfix := d.moduleEquiv.injective he
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix)

/-- Normality and the core-free plus group kill O₂(L_v). The source cubic
quotient therefore bounds the order of its actual image. -/
theorem residual_card_dvd_three
    (hc : ⁅plusImage K L T z v e.normalizeL e.fixSeed K,
      plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)⁆ = ⊥)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3) :
    Nat.card (plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)) ∣ 3 := by
  let C := plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)
  let hn : C.Normal := residual_normal e hc
  have hcore : pCore 2 C = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hn.isSubnormal,
      plus_twoCore_eq_bot K L T z v e.selected.1.1 e.normalizeL e.fixSeed e.tvSylow]
    exact C.subtype.ker_eq_bot_iff.mpr C.subtype_injective
  exact Kernel.card_dvd_cubic_of_corefree_image
    (residualPlus e) (residualPlus_surjective e) hcore hcard

/-- The source residual has a faithful cubic action on U_K. -/
theorem faithful_residual
    (hc : ⁅plusImage K L T z v e.normalizeL e.fixSeed K,
      plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)⁆ = ⊥)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hne : ⁅UK K L T z v, Lv L v⁆ ≠ ⊥) :
    Function.Injective ((action e d).comp
      (plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)).subtype) := by
  have hnontriv := residual_action_ne_one e d hne
  have hc3 : Nat.card (plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (residual_card_dvd_three e hc hcard) with h | h
    · have hbot := (Subgroup.eq_bot_iff_card _).mpr h
      apply (hnontriv ?_).elim
      apply MonoidHom.ext
      intro l
      change action e d (l : Gplus K L T z v e.normalizeL e.fixSeed) = 1
      rw [show (l : Gplus K L T z v e.normalizeL e.fixSeed) = 1 from mem_bot.mp (hbot ▸ l.property), map_one]
    · exact h
  exact Kernel.injective_of_cubic _ hc3 hnontriv

/-- Faithfulness extends to the entire plus actor: the remaining kernel
embeds in the two-group quotient by K+L_v+, hence is killed by O₂(G+)=1. -/
theorem faithful
    (hc : ⁅plusImage K L T z v e.normalizeL e.fixSeed K,
      plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)⁆ = ⊥)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hne : ⁅UK K L T z v, Lv L v⁆ ≠ ⊥) : Function.Injective (action e d) := by
  let C := plusImage K L T z v e.normalizeL e.fixSeed K
  let D := plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)
  let R := plusImage K L T z v e.normalizeL e.fixSeed (Tv T v)
  let := plusImage_K_normal K L T z v e.normalizeL e.fixSeed e.selected e.normalizeK
  let := residual_normal e hc
  have hcenter : center C = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro k hk
    apply d.actor.injective
    rw [map_one]
    exact mem_bot.mp (Matrix.PSL3Two.center_eq_bot ▸
      (MulEquivClass.apply_mem_center d.actor hk))
  obtain ⟨P, hP⟩ := e.internalR_isSylow
  have hp : IsPGroup 2 R := by
    change IsPGroup 2 (e.internalR.map (plusMk K L T z v e.normalizeL e.fixSeed))
    rw [← hP]
    exact P.isPGroup'.map _
  exact Kernel.injective_of_commuting_supplement
    (action e d) C D R hc hcenter (faithful_component e d)
    (faithful_residual e d hc hcard hne) hp (plus_generates e)
    (plus_twoCore_eq_bot K L T z v e.selected.1.1 e.normalizeL e.fixSeed e.tvSylow)

/-- Construct every field of the shared full-action interface. -/
noncomputable def extendedCoordinates
    (hc : ⁅plusImage K L T z v e.normalizeL e.fixSeed K,
      plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)⁆ = ⊥)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hne : ⁅UK K L T z v, Lv L v⁆ ≠ ⊥) : ExtendedCoordinates e d where
  normalizes := normalizes_UK e
  action := action e d
  faithful := faithful e d hc hcard hne
  on_component := on_component e d
  equivariant := equivariant e d
  normalizes_diagonal := normalizes_diagonal e d

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction
