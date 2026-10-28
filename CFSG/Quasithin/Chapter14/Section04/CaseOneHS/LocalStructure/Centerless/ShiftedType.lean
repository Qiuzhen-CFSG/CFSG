module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedMovement
public import Theory.LinearAlgebra.AlternatingDisplacementPair

/-!
# Order two and the type-a₂ shifted involution

The two displaced centralizers from ShiftedMovement generate U. Their
commutator bounds land in their respective orthogonal lines, which commute
inside V. The isometry equation therefore makes each shifted displacement
form alternating. Nondegeneracy and even rank identify every nonzero moved
space with the original two-dimensional V-hat. All these statements use the
actual action on U/Z(U) and the original commutator form.

Alternating displacement forms with image in this fixed plane descend to a
two-dimensional quotient and are determined by one binary value. The preceding
faithfulness theorem therefore bounds |Z(I₂)| by two. The final theorem constructs
the invariant symplectic form and applies the order and type-a₂ conclusions to
the original shifted involution and Ke/C_Ke(Ue) from 14.3.31.

The sole later explicit premise is the 14.3.25 seed exclusion, still owned by
qt-d-hs-centerless-source. Its faithful and solvable exclusions, the 14.3.29
Thompson argument, and both 14.3.31 contradictions remain with that same task.
The earlier marked action alternatives remain with qt-d-hs-action-source;
final LocalStructure assembly remains with qt-d-hs-local-structure. No part of
14.3.32 is used, and this module does not assert centerlessness.

Source: Aschbacher--Smith, 14.3.30--31, printed pp.1002--1003.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem hat_orthogonal_of_centralizes (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc) (A D : Subgroup G)
    (hAD : A ≤ centralizer (D : Set G)) :
    F.hatSubspace A ≤ B.form.orthogonal (F.hatSubspace D) := by
  rintro q ⟨u, hu, he⟩ r ⟨v, hv, hvq⟩
  change F.uhatProjection u = q.toMul at he
  change F.uhatProjection v = r.toMul at hvq
  rw [show q = Additive.ofMul (F.uhatProjection u) from congrArg Additive.ofMul he.symm,
    show r = Additive.ofMul (F.uhatProjection v) from congrArg Additive.ofMul hvq.symm,
    B.evaluation]
  have hcomm : ⁅(v : G), (u : G)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hAD hu v hv)
  have hz : (⟨⁅(v : G), (u : G)⁆, hc (commutator_mem_commutator v.property u.property)⟩ : F.Vi 1) = 1 :=
    Subtype.ext hcomm
  rw [hz, map_one]
  rfl

omit [Finite G] in
private theorem hat_sup (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (A D : Subgroup G) (hA : A ≤ F.U) (hD : D ≤ F.U) :
    F.hatSubspace (A ⊔ D) = F.hatSubspace A ⊔ F.hatSubspace D := by
  unfold hatSubspace
  rw [subgroupOf_sup hA hD, Subgroup.map_sup]
  rw [OrderIso.map_sup, OrderIso.map_sup]

omit [Finite G] in
private theorem hat_sup_top (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (A D : Subgroup G) (hgen : F.U = A ⊔ D) :
    F.hatSubspace A ⊔ F.hatSubspace D = ⊤ := by
  rw [← hat_sup F A D (hgen ▸ le_sup_left) (hgen ▸ le_sup_right), ← hgen]
  apply top_unique
  intro q _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) q.toMul
  exact ⟨u, u.property, hu⟩

omit [Finite G] in
private theorem displacement_line (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (A P C : Subgroup G) (hP : P ≤ F.U)
    (hbound : ⁅A,C⁆ ≤ F.ZU ⊔ P) (a : F.H) (ha : (a : G) ∈ C) :
    ∀ x ∈ F.hatSubspace A, F.uhatDisplacement a x ∈ F.hatSubspace P := by
  rintro x ⟨u, hu, he⟩
  change F.uhatProjection u = x.toMul at he
  rw [show x = Additive.ofMul (F.uhatProjection u) from congrArg Additive.ofMul he.symm,
    F.uhatDisplacement_projection, F.mem_hatSubspace_projection P hP]
  rw [commutator_comm] at hbound
  have hh := hbound (commutator_mem_commutator ha hu)
  change (a : G) * (u : G) * (a : G)⁻¹ / (u : G) ∈ P ⊔ F.ZU
  simpa only [sup_comm, commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hh

/-- The alternating displacement condition in type a₂, derived on the
original commutator form from the actual two centralizer bounds. -/
theorem source_shifted_alternating_displacement (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hc : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (a : F.H) (ha : (a : G) ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) :
    ∀ x, F.uhatBilinearForm (by decide) htwo hphi x (F.uhatDisplacement a x) = 0 := by
  let := chosen.elementary
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  obtain ⟨k, hkL, hkH, hkp, hgen, hb₁, hb₂, _⟩ := source_shifted_movement
    d earlier hq chosen structural alternatives F hne g l hgP hgH hlV hl hspace
  let Pg := conjugate (F.Vi 1) g
  let Pl := conjugate (F.Vi 1) l
  have hgV : Pg ≤ V := conjugate_le_of_normalizes (F.le_seed 1) g
    (F.P_le_seed_normalizer L chosen.normalizes hgP)
  have hlV' : Pl ≤ V := conjugate_le_of_normalizes (F.le_seed 1) l hlV
  have hgC : Pg ≤ centralizer (F.W : Set G) := by
    apply le_centralizer_iff.mp
    have hp : Pg ≤ F.Vi 2 := by
      rw [F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH]
      exact le_sup_right
    exact inf_le_right.trans (centralizer_le hp)
  have hlC : Pl ≤ centralizer (conjugate F.W k : Set G) := by
    change conjugate (F.Vi 1) l ≤ _
    rw [← hkp]
    have hm := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hgC
    exact hm.trans (map_centralizer_le_centralizer_image _ _)
  have hgl : Pl ≤ centralizer (Pg : Set G) := by
    intro z hz y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hgV hy⟩ : V) ⟨z, hlV' hz⟩)
  let t : Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat :=
    { (F.uhatAction a).toAdditive with map_smul' := ZMod.map_smul (F.uhatAction a).toAdditive }
  have ht : ∀ x y, B.form (t x) (t y) = B.form x y := by
    intro x y
    change F.uhatBilinearForm (by decide) htwo hphi
      (Additive.ofMul (F.uhatAction a x.toMul)) (Additive.ofMul (F.uhatAction a y.toMul)) = _
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) htwo hphi]
    rfl
  exact Theory.LinearAlgebra.alternating_displacement_of_two_subspaces B.form B.alternating
    (F.hatSubspace F.W) (F.hatSubspace (conjugate F.W k))
    (F.hatSubspace Pg) (F.hatSubspace Pl) (hat_sup_top F _ _ hgen)
    (hat_orthogonal_of_centralizes F B _ _ hgC)
    (hat_orthogonal_of_centralizes F B _ _ hlC)
    (hat_orthogonal_of_centralizes F B _ _ hgl) t ht
    (displacement_line F _ _ _ (hgV.trans (le_conjugateSpanBy V F.H)) hb₁ a ha)
    (displacement_line F _ _ _ (hlV'.trans (le_conjugateSpanBy V F.H)) hb₂ a ha)

/-- A nonidentity shifted actor has exactly the original seed as its moved
plane; the alternating displacement condition distinguishes type a₂. -/
theorem source_shifted_displacement_eq_seed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hc : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (a : F.H) (ha : (a : G) ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l))
    (hfaith : F.uhatAction a ≠ 1) :
    (F.uhatDisplacement a).range = F.hatSubspace V := by
  let := chosen.elementary
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  have hN : F.uhatDisplacement a ≠ 0 := by
    intro hzero
    apply hfaith
    ext u
    have h := LinearMap.congr_fun hzero (Additive.ofMul u)
    exact Additive.ofMul.injective (sub_eq_zero.mp h)
  apply Theory.LinearAlgebra.range_eq_plane_of_alternating_displacement
    B.form B.alternating B.nondegenerate (F.uhatDisplacement a) hN
    (source_shifted_alternating_displacement d earlier hq chosen structural alternatives
      F hne htwo hphi hc g l hgP hgH hlV hl hspace a ha)
  · exact CaseOneGeometry.seed_hat_dimension F
      (CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne).2.2
  · exact source_shifted_displacement_range d earlier hq chosen structural alternatives
      F hne g l hgP hgH hlV hl hspace a ha

/-- Source 14.3.30(1), with only the preceding 14.3.25 exclusion explicit. -/
theorem source_center_order_le_two (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥) :
    Nat.card (Chapter12.Section08.centerIn (F.I₂ L)) ≤ 2 := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hvz⟩ := CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let h := higherRankHypothesis d earlier hq chosen
  have hc := (F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F alternatives)).1
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  obtain ⟨g, l, hgL, hgP, hgH, hlL, hl, _, hspace, _, hgen⟩ :=
    source_shifted_generating_geometry d earlier hq chosen structural F
  let C := Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)
  have hCH : C ≤ F.H := by
    change Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ _
    rw [source_shifted_center_intersection d earlier hq chosen structural alternatives F hne g hgP hgH l hl]
    exact inf_le_left.trans ((F.conjugate_ZU_le_X g).trans
      (F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)))
  let actor : C →* F.H := inclusion hCH
  let N (a : C) := F.uhatDisplacement (actor a)
  have hfaith := source_shifted_action_faithful d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hlL hl hgen hspace
  have hinj : Function.Injective N := by
    intro a b hab
    have heq : F.uhatAction (actor a) = F.uhatAction (actor b) := by
      ext q
      have hh := LinearMap.congr_fun hab (Additive.ofMul q)
      have hh' : Additive.ofMul (F.uhatAction (actor a) q) - Additive.ofMul q =
          Additive.ofMul (F.uhatAction (actor b) q) - Additive.ofMul q := hh
      exact Additive.ofMul.injective (sub_left_inj.mp hh')
    have hker : (a : G) / (b : G) ∈ C ⊓ F.uhatAction.ker.map F.H.subtype := by
      refine ⟨C.div_mem a.property b.property, ⟨actor a / actor b, ?_, rfl⟩⟩
      change F.uhatAction (actor a / actor b) = 1
      rw [map_div, heq]
      simp only [div_eq_mul_inv, mul_inv_cancel]
    have hbot : (a : G) / (b : G) = 1 := by
      change (a : G) / (b : G) ∈ (⊥ : Subgroup G)
      exact hfaith ▸ hker
    exact Subtype.ext (div_eq_one.mp hbot)
  have hcard : Nat.card C ≤ 2 :=
    Theory.LinearAlgebra.card_le_two_of_alternating_plane_maps B.form B.nondegenerate
      (F.hatSubspace V) (CaseOneGeometry.seed_hat_dimension F hvz) N hinj
      (fun a x => B.alternating.eq_iff.mp
        (source_shifted_alternating_displacement d earlier hq chosen structural alternatives F hne
          htwo hphi hc g l hgP hgH (chosen.normalizes hlL) hl hspace (actor a) a.property x))
      (fun a => source_shifted_displacement_range d earlier hq chosen structural alternatives
        F hne g l hgP hgH (chosen.normalizes hlL) hl hspace (actor a) a.property)
  change Nat.card (Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) ≤ 2 at hcard
  rw [centerIn_conjugate, conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective] at hcard
  exact hcard

/-- The full order and type-a₂ conclusions needed by the actual 14.3.31
amalgam, with 14.3.25 retained explicitly and all form inputs discharged. -/
theorem source_shifted_amalgam_type (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    Nat.card (Chapter12.Section08.centerIn (F.I₂ L)) = 2 ∧
    ∃ g l e : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l ∧
      orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      let a := l⁻¹ * e * l
      let K := conjugateSpanBy (zpowers a) F.H
      ∃ haH : a ∈ F.H,
        orderOf a = 2 ∧ F.uhatAction ⟨a, haH⟩ ≠ 1 ∧
        (∃ helem : IsElementaryAbelian 2 F.Uhat, letI := helem
          ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat),
            B.IsAlt ∧ B.Nondegenerate ∧
            (∀ (h : F.H) (x y : F.Uhat),
              B (Additive.ofMul (F.uhatAction h x)) (Additive.ofMul (F.uhatAction h y)) =
                B (Additive.ofMul x) (Additive.ofMul y)) ∧
            (F.uhatDisplacement ⟨a, haH⟩).range = F.hatSubspace V ∧
            (∀ x, B x (F.uhatDisplacement ⟨a, haH⟩ x) = 0)) ∧
        K ≤ centralizer (F.ZU : Set G) ∧
        amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
        IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
        pCore 2 (AmalgamQuotient F L K) = ⊥ := by
  obtain ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI, heT, heU, heV,
    haH, ha, hfaith, _, hK, hKe, hr, hcore⟩ :=
    source_shifted_amalgam_faithful d earlier hq chosen structural alternatives F hne hseed hI
  have horder : Nat.card (Chapter12.Section08.centerIn (F.I₂ L)) = 2 := by
    apply Nat.le_antisymm (source_center_order_le_two d earlier hq chosen structural alternatives F hne hseed)
    have hh := card_le_of_le (zpowers_le.mpr heI)
    rwa [Nat.card_zpowers, he] at hh
  refine ⟨horder, g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI, heT, heU, heV,
    haH, ha, hfaith, ?_, hK, hKe, hr, hcore⟩
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne
  let helem := F.uhat_elementary_of_point (by decide) htwo hphi
  let := helem
  let h := higherRankHypothesis d earlier hq chosen
  have hc := (F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F alternatives)).1
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  have haI : l⁻¹ * e * l ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) := by
    rw [centerIn_conjugate]
    simpa only [conjugate, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      mem_map_of_mem (MulAut.conj l⁻¹).toMonoidHom heI
  refine ⟨helem, B.form, B.alternating, B.nondegenerate, ?_,
    source_shifted_displacement_eq_seed d earlier hq chosen structural alternatives F hne
      htwo hphi hc g l hgP hgH (chosen.normalizes hlL) hl hspace ⟨_, haH⟩ haI hfaith,
    source_shifted_alternating_displacement d earlier hq chosen structural alternatives F hne
      htwo hphi hc g l hgP hgH (chosen.normalizes hlL) hl hspace ⟨_, haH⟩ haI⟩
  intro h x y
  change F.uhatBilinearForm (by decide) htwo hphi
    (Additive.ofMul (F.uhatAction h x)) (Additive.ofMul (F.uhatAction h y)) = _
  rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) htwo hphi]
  rfl

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
