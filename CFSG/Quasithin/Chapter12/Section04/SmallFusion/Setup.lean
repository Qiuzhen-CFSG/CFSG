module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.Representation.SLThreeCentralExtension

/-!
# The actual fixed involution in the small-module counterexample

The marked natural quotient below is the L₃(2) alternative of 12.2.2(3),
on the original chosen subgroup V. The cohomology calculation bounds its
fixed kernel, and nontriviality makes that kernel a line. Uniqueness from
1.2.7 then identifies N_G(L), C_G(z), and N_G(V). In particular the
centralizer of Ω₁(Z(T)) lies in this same subgroup.

The universal structural and marked-module implications of 12.2.2 and the
earlier inputs to 1.2.7 remain explicit. Their source owners must instantiate
them; the fixed-line and normalizer conclusions are derived here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Section 12.4, printed pp.812–813, using I.1.5–6, printed p.408.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion
set_option linter.style.haveILetI false
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal fixed subgroup, in the original ambient group. -/
abbrev fixedSubgroup (L V : Subgroup G) : Subgroup G := V ⊓ centralizer (L : Set G)

/-- A marking of the indecomposable natural-quotient alternative of 12.2.2(3).
The quotient group is literally L/O₂(L); the action equation fixes its
identification with conjugation on the original V. No bound on C_V(L),
centralizer equality, or fusion assertion is part of this datum. -/
structure SLThreeExtension {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) where
  quotientEquiv : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  action : letI := D.elementary
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (Additive V)
  conjugation : ∀ (l : L) (v : Additive V),
    ((action (quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) v).toMul : G) =
      (l : G) * (v.toMul : G) * (l : G)⁻¹
  projection : letI := D.elementary
    action.IntertwiningMap (specialLinearNatural (k := ZMod 2) 3)
  surjective : Function.Surjective projection
  kernel : letI := D.elementary
    projection.toLinearMap.ker = fixed action
  indecomposable : letI := D.elementary
    ∀ A B : Submodule (ZMod 2) (Additive V),
      (∀ g v, v ∈ A → action g v ∈ A) →
      (∀ g v, v ∈ B → action g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥

namespace SLThreeExtension
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
variable (E : SLThreeExtension D)

omit [Finite G] in
/-- The marking identifies the linear fixed space with the actual centralizer. -/
theorem mem_fixed_iff (v : Additive V) : letI := D.elementary
    v ∈ fixed E.action ↔ (v.toMul : G) ∈ centralizer (L : Set G) := by
  let _ := D.elementary
  constructor
  · intro hv l hl
    have he := E.conjugation ⟨l, hl⟩ v
    rw [hv] at he
    exact mul_inv_eq_iff_eq_mul.mp he.symm
  · intro hv g
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (E.quotientEquiv.symm g)
    have he : E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g := by
      rw [hl, MulEquiv.apply_symm_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [← he, E.conjugation]
    exact mul_inv_eq_iff_eq_mul.mpr (hv l l.property)

/-- The original fixed subgroup has at most two elements, by dual H¹. -/
theorem fixed_card_le_two (E : SLThreeExtension D) : Nat.card (fixedSubgroup L V) ≤ 2 := by
  let _ := D.elementary
  let e : fixedSubgroup L V ≃ E.projection.toLinearMap.ker := {
    toFun := fun v => ⟨Additive.ofMul ⟨v, v.property.1⟩, by
      rw [E.kernel]
      exact (E.mem_fixed_iff _).mpr v.property.2⟩
    invFun := fun v => ⟨v.val.toMul, v.val.toMul.property,
      (E.mem_fixed_iff _).mp (E.kernel ▸ v.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact SLThreeCentralExtension.card_kernel_le_two E.projection E.surjective
    E.kernel.le E.indecomposable

/-- In the counterexample the original fixed subgroup is a line. -/
theorem fixed_card_eq_two (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    Nat.card (fixedSubgroup L V) = 2 := by
  have hlo : 1 < Nat.card (fixedSubgroup L V) := by
    by_contra hlt
    have hle : Nat.card (fixedSubgroup L V) ≤ 1 := Nat.le_of_not_gt hlt
    have hsub : Subsingleton (fixedSubgroup L V) :=
      Finite.card_le_one_iff_subsingleton.mp hle
    apply hne
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have he : (⟨x, hx⟩ : fixedSubgroup L V) = 1 :=
      @Subsingleton.elim _ hsub _ _
    exact congrArg Subtype.val he
  have hhi := E.fixed_card_le_two
  omega

end SLThreeExtension

/-- The precise marked L₃ alternative needed from 12.2.2(3), universally
quantified over its source hypotheses. Its producer is the Section 12.2
reduction, and its final discharge belongs to the Section 12.4 assembly. -/
def SLThreeAlternative1222 (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 K T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 →
    fixedSubgroup L V ≠ ⊥ → Nonempty (SLThreeExtension D)

variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_orbit_eq (h : Hypothesis1223 K T L)
    (structural : Structural1222 K) : componentOrbit L (T : Subgroup G) = L := by
  apply le_antisymm _ (le_componentOrbit L _)
  exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl
    (structural G T L h).1

/-- Construct the centralizer/normalizer setup from the proved order of the
fixed subgroup. This applies to either small-module branch. -/
theorem exists_fixed_involution_setup_of_card_two
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hcard : Nat.card (fixedSubgroup L V) = 2) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      normalizer (L : Set G) = centralizer ({z} : Set G) ∧
      normalizer (L : Set G) = normalizer (V : Set G) ∧
      z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) ∧
      centralizer (omegaOneAmbient ((center (T : Subgroup G)).map
        (T : Subgroup G).subtype) : Set G) ≤ normalizer (L : Set G) := by
  let _ := D.elementary
  have hne : fixedSubgroup L V ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcard
    omega
  obtain ⟨z, hzne, _⟩ := (Nat.card_eq_two_iff' (1 : fixedSubgroup L V)).mp hcard
  have hz1 : (z : G) ≠ 1 := fun he => hzne (Subtype.ext he)
  have hzsq : (z : G) ^ 2 = 1 := by
    simpa using elemPow_eq_one_of_isElementaryAbelian
      (z : G) z.property.1
  have hzorder : orderOf (z : G) = 2 :=
    orderOf_eq_prime hzsq hz1
  have hzgen : fixedSubgroup L V = zpowers (z : G) := by
    apply (eq_of_le_of_card_ge (zpowers_le_of_mem z.property) ?_).symm
    rw [Nat.card_zpowers, hzorder, hcard]
  have hstruct := structural G T L h
  have hMnorm : normalizer (L : Set G) ≤ normalizer (V : Set G) :=
    (hstruct.2.2 V D).2.2.2.resolve_right hne
  have hMC : normalizer (L : Set G) ≤ normalizer (fixedSubgroup L V : Set G) :=
    (le_inf hMnorm (normalizer_le_normalizer_centralizer L)).trans
      inf_normalizer_le_normalizer_inf
  have hMCz : normalizer (L : Set G) ≤ centralizer ({(z : G)} : Set G) := by
    rwa [hzgen, normalizer_zpowers_eq_centralizer_of_order_two _ hzorder] at hMC
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier earlier
    h.simpleQTKE T h.maximal_faithful.1
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = normalizer (L : Set G) := by
    intro N hN hLN
    simpa only [source_orbit_eq h structural] using hu.normalizer_unique N hN hLN
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer hstruct.1
  letI : IsElementaryAbelian 2 (fixedSubgroup L V) :=
    IsElementaryAbelian.of_le inf_le_left
  have hfixP : IsPGroup 2 (fixedSubgroup L V) :=
    IsElementaryAbelian.isPGroup 2 (fixedSubgroup L V)
  have hfixne : fixedSubgroup L V ≠ ⊥ := hne
  have hCzM : centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G) := by
    rw [← normalizer_zpowers_eq_centralizer_of_order_two _ hzorder, ← hzgen]
    apply normalizer_le_of_unique_maximalTwoLocal huniq hfixP hfixne
    exact hLT.trans hMC
  have hVM : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal huniq
      (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
      (sup_le D.normalizes (hstruct.2.2 V D).1)
  have hzcenter : (z : G) ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype := by
    refine ⟨⟨z, D.le_sylow z.property.1⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro t
    apply Subtype.ext
    change (t : G) * (z : G) = (z : G) * (t : G)
    exact mem_centralizer_singleton_iff.mp
      (hMCz (hstruct.1 t.property))
  have hzomega : (z : G) ∈ omegaOneAmbient
      ((center (T : Subgroup G)).map (T : Subgroup G).subtype) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl (z : G) hzcenter
      (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property.1)
  refine ⟨z, hzorder, hzgen, le_antisymm hMCz hCzM, le_antisymm hMnorm hVM,
    hzomega, ?_⟩
  exact (centralizer_le (Set.singleton_subset_iff.mpr hzomega)).trans hCzM

/-- The L₃(2) counterexample setup, with its fixed line constructed using
I.1.6 rather than assumed. The marked 12.2.2 implication remains explicit. -/
theorem exists_slThree_fixed_involution_setup
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K)
    (marked : SLThreeAlternative1222 K)
    (earlier : Chapter1.Section02.UniquenessEarlierResults K)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    Nat.card (fixedSubgroup L V) = 2 ∧
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      normalizer (L : Set G) = centralizer ({z} : Set G) ∧
      normalizer (L : Set G) = normalizer (V : Set G) ∧
      z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) ∧
      centralizer (omegaOneAmbient ((center (T : Subgroup G)).map
        (T : Subgroup G).subtype) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  have hc := E.fixed_card_eq_two hne
  exact ⟨hc, exists_fixed_involution_setup_of_card_two h D structural earlier hc⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion
