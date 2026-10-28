module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Orders
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.SolvableExclusion
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import Theory.GroupAction.TwoElementKernelAutomorphisms
public import Theory.GroupTheory.PResidual.NormalityLift

/-!
# The small-center action kernel and the solvable HS alternative

The equivariant map from U-tilde to U-hat has kernel Z(U)-tilde. When this
kernel has order at most two, its value-preserving automorphisms form a
two-group. The proved tilded action kernel then identifies the original
U-hat action kernel with O₂(H), without natural-action coordinates.

The original L₁ is the embedded 2-residual of L ∩ G₁ and is normalized by T.
Thus normality of its literal dotted image lifts across this normalizing
two-group kernel. The homogeneous-module contradiction excludes that
normality when the tilded center has order two. The final theorem applies
the argument to the actual S₃ × S₃ quotient and normal dotted L₁ of
14.3.23(2)(i), deriving the required actor bound from its order 36.

The six-dimensional order calculation also supplies its small-center
kernel premise. Its parabolic exclusion, the nonsolvable four-dimensional
alternatives, and the source classification producing those alternatives
remain with qt-d-hs-action-source. No classification or natural coordinates
are assumed in the kernel argument.

Source: Aschbacher--Smith, 14.3.32, printed pp.1003--1004, including the
final exclusion of 14.3.23(2)(i). The earlier uniqueness input is discharged
by the proved known-simple source theorem 1.2.7.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A tilded center of order at most two identifies the action kernel before choosing natural coordinates. -/
theorem source_small_center_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hZ : Nat.card (F.tilde F.ZU) ≤ 2) : F.uhatAction.ker = pCore 2 F.H := by
  let := chosen.elementary
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have ht := source_action_kernel d earlier hq chosen ⟨structural, unique, alternatives⟩ F
  let q := F.tildeToUhat (by decide : 1 ≤ 3)
  have hk : Nat.card q.ker ≤ 2 := by
    rw [show q.ker = (F.tilde F.ZU).subgroupOf (F.tilde F.U) from F.tildeToUhat_ker (by decide)]
    have hle : F.tilde F.ZU ≤ F.tilde F.U := map_mono (comap_mono (map_subtype_le (center F.U)))
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact hZ
  have hf := q.isPGroup_fixingAut_of_kernel_card_le_two hk
  let f : F.uhatAction.ker →* q.fixingAut :=
    ((F.localTildeAction F.H le_rfl).comp F.uhatAction.ker.subtype).codRestrict _ (by
      intro a u
      change q (F.localTildeAction F.H le_rfl (a : F.H) u) = q u
      rw [show q (F.localTildeAction F.H le_rfl (a : F.H) u) =
        F.uhatAction (a : F.H) (q u) from F.tildeToUhat_equivariant (by decide) a u]
      have ha : F.uhatAction (a : F.H) = 1 := a.property
      rw [ha]
      rfl)
  have hfker : f.ker ≤ (pCore 2 F.H).subgroupOf F.uhatAction.ker := by
    intro a ha
    change (a : F.H) ∈ pCore 2 F.H
    rw [← ht]
    exact congrArg Subtype.val ha
  have hp : IsPGroup 2 f.ker :=
    (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf F.uhatAction.ker)).to_le hfker
  have htop := (hf.to_subgroup ⊤).comap_of_ker_isPGroup f hp
  rw [comap_top] at htop
  have hker : IsPGroup 2 F.uhatAction.ker := htop.of_surjective
    (⊤ : Subgroup F.uhatAction.ker).subtype (fun a => ⟨⟨a,mem_top a⟩,rfl⟩)
  exact le_antisymm (le_sSup ⟨inferInstance, hker⟩)
    (F.pCore_le_uhatAction_ker_of_tilde_kernel (by decide) ht)

private theorem source_normal_Li_one_of_dot_normal (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hkernel : F.uhatAction.ker = pCore 2 F.H)
    (hn : (dotImage F F.uhatAction (F.Li L 1)).Normal) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes structural)
      ((F.invariant 1).trans (F.Gi 1).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.Gi 1) (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)))
  have hLH : F.Li L 1 ≤ F.H := fun x hx => (F.Li_le L 1 hx).2
  have hperf : IsPPerfect 2 (F.Li L 1) := by
    rw [hres]
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
  have hp : IsPPerfect 2 ((F.Li L 1).subgroupOf F.H) := hperf.of_surjective
    (subgroupOfEquivOfLe hLH).symm.toMonoidHom (subgroupOfEquivOfLe hLH).symm.surjective
  let q := QuotientGroup.mk' F.uhatAction.ker
  have hker : q.ker = pCore 2 F.H := (QuotientGroup.ker_mk' _).trans hkernel
  let : (((F.Li L 1).subgroupOf F.H).map q).Normal := hn
  apply normal_of_map_normal_of_pPerfect q _ hp (hker.symm ▸ pCore_isPGroup)
  intro x hx
  have hxQ : (x : G) ∈ F.H.pCoreIn 2 := mem_map_of_mem F.H.subtype (hker ▸ hx)
  have hxT : (x : G) ∈ (T : Subgroup G) := by
    obtain ⟨t, ht, he⟩ := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1)) hxQ
    exact he ▸ ht
  have hxn := hTn hxT
  rw [mem_normalizer_iff] at hxn ⊢
  intro y
  exact hxn (y : G)

/-- Lift the normality of the literal dotted L₁ and apply the source homogeneous-module contradiction. -/
theorem source_normal_dot_Li_one_exclusion_of_four_two (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (hr : primeRank 2 (Hdot F F.uhatAction) ≤ 2)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ¬ (dotImage F F.uhatAction (F.Li L 1)).Normal := by
  let := source_actor_elementary d earlier hq chosen structural alternatives F hne g hgP hgH
  have hb : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 4 :=
    (primeRank_le_iff_elementary_card_le (Hdot F F.uhatAction)).mp hr _ inferInstance
  have hz := (source_four_dimensional_orders d earlier hq chosen structural alternatives
    F hne hZ hI hc g hgP hgH hb).2.2.2
  have hk := source_small_center_kernel d earlier hq chosen structural alternatives F hz.le
  intro hn
  exact source_normal_Li_one_exclusion d earlier hq chosen structural alternatives F hne hz
    (source_normal_Li_one_of_dot_normal d earlier hq chosen structural F hk hn)

/-- The six-dimensional order calculation supplies the kernel equality needed by its parabolic exclusion. -/
theorem source_six_dimensional_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 64)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hX : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 8) :
    Nat.card (F.tilde F.ZU) = 2 ∧ F.uhatAction.ker = pCore 2 F.H := by
  have hz := (source_six_dimensional_orders d earlier hq chosen structural alternatives
    F hne hZ hI hc g hgP hgH hX).2.1
  obtain ⟨e⟩ := source_conjugate_center_image_equiv d earlier hq chosen structural alternatives
    F hne hI g hgP hgH
  have ho := source_conjugate_center_image_order d earlier hq chosen structural alternatives
    F hne hI g hgP hgH
  rw [Nat.card_congr e.toEquiv, hz] at ho
  have ht : Nat.card (F.tilde F.ZU) = 2 := by omega
  exact ⟨ht, source_small_center_kernel d earlier hq chosen structural alternatives F ht.le⟩


private theorem pair_symmetricThree_rank (D : Type*) [Group D] [Finite D]
    (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : primeRank 2 D ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le D).mpr
  intro A hA
  let := hA
  have hd : Nat.card A ∣ 36 := by
    have hc : Nat.card D = 36 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    exact hc ▸ A.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card A) 9 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 9).pow_left n
  exact Nat.le_of_dvd (by decide : 0 < 4) (hcop.dvd_mul_right.mp hd)

/-- Exclusion of the literal S₃ × S₃ row, retaining its normal dotted L₁. -/
theorem source_pair_symmetricThree_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (e : Hdot F F.uhatAction ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hn : (dotImage F F.uhatAction (F.Li L 1)).Normal) : False := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨β, _, b, _, hcuts, _, _⟩ := F.exists_marked_naturalFlag L chosen.normalizes h.full_L_action
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (show (T : Subgroup G) ≤ normalizer (V : Set G) from F.last ▸ F.invariant 3)
    (h.binarySeedAction_surjective F) β b hcuts
  exact source_normal_dot_Li_one_exclusion_of_four_two d earlier hq chosen structural alternatives
    F hne hZ hI hc (pair_symmetricThree_rank _ e) g hgP hgH hn

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
