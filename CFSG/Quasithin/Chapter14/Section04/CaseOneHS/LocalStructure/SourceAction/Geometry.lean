module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Action
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalCoordinates

/-!
# The conjugate center in the original nonextraspecial action

The earlier source geometry constructs the elementary parabolic quotient,
its exact action kernel, and the outside-hyperplane stabilizers. Centerlessness
then identifies the kernel on the conjugate center with the conjugated marked
point. The first isomorphism theorem gives an actual equivalence of this action
image with the original tilded center, and computes its order. The image is
nontrivial in the nonextraspecial branch.

These are the opening conclusions (*) of 14.3.32, before choosing any action
alternative. Neither natural coordinates nor a model-family label is a premise.
The remaining action classification belongs to qt-d-hs-action-source; the
centerlessness premise belongs to qt-d-hs-local-structure. The naturality and
structural/escape premises retain their earlier source owners qt-d-1434-source
and qt-d-1222-source.

Source: Aschbacher--Smith, 12.8.9--10 and 14.3.32, printed pp.852--854,1003.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source parabolic quotient, kernel, stabilizers and hyperplane index. -/
theorem source_parabolic_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (∃ hn : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal, letI := hn
      IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸
        (F.E g).subgroupOf (F.W ⊔ F.X g))) ∧
    F.xHatKernel g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) = F.E g ∧
    (∀ u : F.U, (u : G) ∉ F.W →
      (F.xHatStabilizer g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
        (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
          (conjugate F.ZU g : Set G) * (F.E g : Set G)) ∧
    F.W.relIndex F.U = 2 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨_, _, hVZ⟩ := source_closure d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨e, _, hgen, _, _, _, _, _, hfactor, hPH, hcore, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  have hn := F.binary_source_E_normal_in_core L chosen.normalizes g hgP hgen.symm hcomm
  let := hn
  have he := F.binary_source_quotient_elementary L chosen.normalizes g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal, letI := hn
      IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
        (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hn, he⟩
  rw [hsplit] at hpair
  have ha := F.binary_source_parabolic_action_clauses (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hcomm hsquare
    hspan hne hVZ g hgP hgH
  exact ⟨hpair, ha.2.1.1, ha.2.2, hindex⟩

/-- The exact kernel on the original right-conjugated center. -/
theorem source_conjugate_center_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).ker =
      (conjugate (F.Vi 1) g).subgroupOf (conjugate F.ZU g) := by
  let := chosen.elementary
  have ha := (source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hi := (source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).2.2
  rw [hI, bot_sup_eq] at hi
  have hVE := F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L chosen.normalizes hgP)
  ext z
  change F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1 ↔
    (z : G) ∈ conjugate (F.Vi 1) g
  have hk : F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1 ↔
      (z : G) ∈ F.E g := by
    rw [← ha, F.mem_xHatKernel]
    exact ⟨fun he => ⟨F.conjugate_ZU_le_X g z.property,
      (F.mem_uhatAction_ker_iff _).mp he⟩,
      fun he => (F.mem_uhatAction_ker_iff _).mpr he.2⟩
  rw [hk]
  constructor
  · intro he
    rw [← hi]
    exact ⟨z.property, (show F.E g ≤ F.U from inf_le_left.trans inf_le_left) he⟩
  · intro hz
    exact hVE (conjugate_le_of_normalizes (F.le_seed 1) g
      (F.P_le_seed_normalizer L chosen.normalizes hgP) hz)

/-- The image has half the order of the intrinsic center. -/
theorem source_conjugate_center_image_order (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    2 * Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range =
      Nat.card (center F.U) := by
  let := chosen.elementary
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  have hpoint : conjugate (F.Vi 1) g ≤ conjugate F.ZU g := map_mono (F.point_le_ZU (by decide))
  have hk : Nat.card f.ker = 2 := by
    rw [source_conjugate_center_kernel d earlier hq chosen structural alternatives F hne hI g hgP hgH,
      Nat.card_congr (subgroupOfEquivOfLe hpoint).toEquiv]
    change Nat.card ((F.Vi 1).map (MulAut.conj g⁻¹).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hh := f.ker.card_mul_index
  have hconj : Nat.card (conjugate F.ZU g) = Nat.card F.ZU :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcenter : Nat.card F.ZU = Nat.card (center F.U) :=
    card_map_of_injective F.U.subtype_injective
  rwa [index_ker, hk, hconj, hcenter] at hh

/-- The nonextraspecial source center has nontrivial action image. -/
theorem source_conjugate_center_image_nontrivial (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≠ ⊥ := by
  let := chosen.elementary
  intro hbot
  have hc := source_conjugate_center_image_order d earlier hq chosen structural alternatives
    F hne hI g hgP hgH
  rw [hbot, card_bot, mul_one] at hc
  have hcenter : Nat.card F.ZU = 2 :=
    (card_map_of_injective F.U.subtype_injective).trans hc.symm
  apply hZ
  apply (eq_of_le_of_card_ge (F.point_le_ZU (by decide)) ?_).symm
  rw [hcenter]
  simpa using (F.card 1 (by decide)).ge

/-- The actual image is isomorphic to the literal image of the center in H/V₁. -/
theorem source_conjugate_center_image_equiv (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nonempty ((F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≃*
        F.tilde F.ZU) := by
  let := chosen.elementary
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  let c : F.ZU ≃* conjugate F.ZU g := F.ZU.equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  let q := (F.tildeMap F.ZU hZH).comp c.symm.toMonoidHom
  have hqsurj : Function.Surjective q := (F.tildeMap_surjective F.ZU hZH).comp c.symm.surjective
  have hk : f.ker = q.ker := by
    rw [source_conjugate_center_kernel d earlier hq chosen structural alternatives F hne hI g hgP hgH]
    ext z
    change (z : G) ∈ conjugate (F.Vi 1) g ↔ q z = 1
    have ht : q z = 1 ↔ (c.symm z : G) ∈ F.Vi 1 := by
      change F.tildeMap F.ZU hZH (c.symm z) = 1 ↔ _
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff _
    rw [ht]
    have he : (z : G) = (MulAut.conj g⁻¹) (c.symm z : G) := by
      exact congrArg (fun x : conjugate F.ZU g => (x : G)) (c.apply_symm_apply z).symm
    rw [he]
    change (MulAut.conj g⁻¹) (c.symm z : G) ∈ (F.Vi 1).map (MulAut.conj g⁻¹).toMonoidHom ↔ _
    simp only [mem_map_equiv, MulEquiv.symm_apply_apply]
  exact ⟨(QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hqsurj))⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
