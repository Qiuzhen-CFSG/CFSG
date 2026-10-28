module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ShiftedAction
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Two displaced centralizers and the shifted-center displacement

The two displaced points determine distinct hyperplane centralizers in U.
Their centers, computed using the genuine commutator form, distinguish them;
their index two then proves that they generate U. Transporting 12.8.10(4)
by the point-fixing element gives a separate line bound on each centralizer.
Together these give [U,Z(I₂ˡ)] ≤ Z(U)V, and hence displacement inside V-hat
on the literal quotient U/Z(U).

The final theorem applies this calculation to the actual shifted involution
and its centralizer amalgam. Its explicit seed exclusion is 14.3.25, still
owned by qt-d-hs-centerless-source. The order/type-a₂ step and the faithful
and Goldschmidt exclusions remain with that same owner; this module does
not assert centerlessness. The earlier action alternatives retain their
independent owner qt-d-hs-action-source, and final LocalStructure assembly
retains qt-d-hs-local-structure. No conclusion of 14.3.32 is used.

Source: Aschbacher--Smith, 14.3.30--31, printed pp.1002--1003.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_commutator_bound (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) : ⁅F.U, F.U⁆ ≤ F.Vi 1 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  exact (F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F alternatives)).1

private theorem source_plane_center (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    Chapter12.Section08.centerIn F.W = F.Vi 2 ⊔ F.ZU := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne
  have hc := (source_commutator_bound d earlier hq chosen structural alternatives F)
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  exact F.plane_centralizer_center (F.localKernel_markedForm (by decide) htwo hphi hc)

/-- The first of the two displacement bounds in source 14.3.30. -/
theorem source_center_displacement (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ⁅F.W, conjugate F.ZU g⁆ ≤ F.ZU ⊔ conjugate (F.Vi 1) g := by
  let := chosen.elementary
  have h := F.center_commutator_le_plane (by decide) L chosen.normalizes
    (CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne).2.2
    (source_commutator_bound d earlier hq chosen structural alternatives F)
    (source_plane_center d earlier hq chosen structural alternatives F hne) g hgP hgH
  rw [F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH,
    ← sup_assoc, sup_eq_left.mpr (F.point_le_ZU (by decide))] at h
  exact h

/-- Distinct displaced points give two hyperplane centralizers generating U. -/
theorem source_two_hyperplane_generation (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g l k : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (hkH : k ∈ F.H)
    (hkp : conjugate (conjugate (F.Vi 1) g) k = conjugate (F.Vi 1) l) :
    F.U = F.W ⊔ conjugate F.W k := by
  let := chosen.elementary
  have hkU : conjugate F.U k = F.U :=
    (conjugate_eq_iff _ _).mpr (le_normalizer_conjugateSpanBy V F.H hkH)
  have hkZ : conjugate F.ZU k = F.ZU :=
    (conjugate_eq_iff _ _).mpr (F.H_normalizes_ZU hkH)
  have hkP : conjugate (F.Vi 1) k = F.Vi 1 := (conjugate_eq_iff _ _).mpr hkH
  have hcenter := source_plane_center d earlier hq chosen structural alternatives F hne
  have hplane := F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH
  have hzc : Chapter12.Section08.centerIn (conjugate F.W k) =
      F.ZU ⊔ conjugate (F.Vi 1) l := by
    rw [centerIn_conjugate, hcenter, hplane]
    have hmap (A B : Subgroup G) : conjugate (A ⊔ B) k =
        conjugate A k ⊔ conjugate B k := Subgroup.map_sup _ _ _
    rw [hmap, hmap, hkZ, hkP, hkp, sup_comm, ← sup_assoc,
      sup_eq_left.mpr (F.point_le_ZU (by decide))]
  have hcw : Chapter12.Section08.centerIn F.W =
      F.ZU ⊔ conjugate (F.Vi 1) g := by
    rw [hcenter, hplane, sup_comm, ← sup_assoc, sup_eq_left.mpr (F.point_le_ZU (by decide))]
  have hneq : conjugate F.W k ≠ F.W := by
    intro he
    have hEq : F.ZU ⊔ conjugate (F.Vi 1) l =
        F.ZU ⊔ conjugate (F.Vi 1) g := by rw [← hzc, he, hcw]
    have hm := source_two_point_intersection d earlier hq chosen structural alternatives
      F hne g l hgP hgH hlV hspace
    rw [hEq, inf_idem] at hm
    have hPZ : F.Vi 2 ≤ F.ZU := by
      rw [hplane]
      exact sup_le (F.point_le_ZU (by decide)) (le_sup_right.trans hm.le)
    have hPP : F.Vi 2 ≤ F.Vi 1 :=
      (le_inf (F.le_seed 2) hPZ).trans
        (CaseOneGeometry.source_closure d earlier hq chosen structural alternatives F hne).2.2.le
    have hc := card_le_of_le hPP
    rw [F.card 2 (by decide), F.card 1 (by decide)] at hc
    norm_num at hc
  have hnot : ¬ conjugate F.W k ≤ F.W := by
    intro hh
    exact hneq (eq_of_le_of_card_ge hh (by
      rw [conjugate, card_map_of_injective (MulAut.conj k⁻¹).injective]))
  have hWU : conjugate F.W k ≤ F.U := hkU ▸
    (map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) (show F.W ≤ F.U from inf_le_left))
  have hidx := (source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH).2.2.2
  have hm := relIndex_mul_relIndex F.W (F.W ⊔ conjugate F.W k) F.U le_sup_left
    (sup_le inf_le_left hWU)
  rw [hidx] at hm
  have hn : F.W.relIndex (F.W ⊔ conjugate F.W k) ≠ 1 := fun he =>
    hnot (le_sup_right.trans (relIndex_eq_one.mp he))
  have hlast : (F.W ⊔ conjugate F.W k).relIndex F.U = 1 := by
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hn hh.2).elim
  exact le_antisymm (relIndex_eq_one.mp hlast) (sup_le inf_le_left hWU)

/-- The shifted center moves U only inside the original seed modulo Z(U).
This is the literal first paragraph of 14.3.30, before faithfulness. -/
theorem source_shifted_movement (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l) :
    ∃ k ∈ L, k ∈ F.H ∧
      conjugate (conjugate (F.Vi 1) g) k = conjugate (F.Vi 1) l ∧
      F.U = F.W ⊔ conjugate F.W k ∧
      ⁅F.W, Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)⁆ ≤
        F.ZU ⊔ conjugate (F.Vi 1) g ∧
      ⁅conjugate F.W k, Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)⁆ ≤
        F.ZU ⊔ conjugate (F.Vi 1) l ∧
      ⁅F.U, Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)⁆ ≤ F.ZU ⊔ V := by
  let := chosen.elementary
  have hlH : l ∉ F.H := by
    intro hh
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hspace, (conjugate_eq_iff _ _).mpr hh,
      sup_eq_left.mpr (F.monotone (by decide)), F.card 2 (by decide)] at hc
    norm_num at hc
  obtain ⟨k, hkL, hkH, hkp, hkz⟩ := source_point_fixer d earlier hq chosen F g l
    (F.P_le_seed_normalizer L chosen.normalizes hgP) hlV hgH hlH
  have hgen := source_two_hyperplane_generation d earlier hq chosen structural alternatives
    F hne g l k hgP hgH hlV hspace hkH hkp
  have hbound := source_center_displacement d earlier hq chosen structural alternatives F hne g hgP hgH
  have hbound' := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hbound
  rw [map_commutator, Subgroup.map_sup] at hbound'
  change ⁅conjugate F.W k, conjugate (conjugate F.ZU g) k⁆ ≤
    conjugate F.ZU k ⊔ conjugate (conjugate (F.Vi 1) g) k at hbound'
  rw [hkz, hkp, (conjugate_eq_iff _ _).mpr (F.H_normalizes_ZU hkH)] at hbound'
  have hi := source_shifted_center_intersection d earlier hq chosen structural alternatives
    F hne g hgP hgH l hl
  have hgZ : Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ conjugate F.ZU g :=
    hi ▸ inf_le_left
  have hlZ : Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ conjugate F.ZU l :=
    hi ▸ inf_le_right
  have hb₁ := (commutator_mono le_rfl hgZ).trans hbound
  have hb₂ := (commutator_mono le_rfl hlZ).trans hbound'
  refine ⟨k, hkL, hkH, hkp, hgen, hb₁, hb₂, ?_⟩
  have hn : F.U ≤ normalizer ((F.ZU ⊔ V : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hZU : F.ZU ⊔ V ≤ F.U := sup_le (map_subtype_le _) (le_conjugateSpanBy V F.H)
    exact ((commutator_mono le_rfl hZU).trans
      (source_commutator_bound d earlier hq chosen structural alternatives F)).trans
      ((F.point_le_ZU (by decide)).trans le_sup_left)
  have hkg : conjugate F.W k ≤ F.U := hgen ▸ le_sup_right
  have hc := commutator_sup_le_of_relative_normal F.U F.W (conjugate F.W k)
    (Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) (F.ZU ⊔ V)
    hn inf_le_left hkg
    (hb₁.trans (sup_le_sup_left (conjugate_le_of_normalizes (F.le_seed 1) g
      (F.P_le_seed_normalizer L chosen.normalizes hgP)) F.ZU))
    (hb₂.trans (sup_le_sup_left (conjugate_le_of_normalizes (F.le_seed 1) l hlV) F.ZU))
  rwa [← hgen] at hc

/-- Pass the ambient commutator bound through the literal quotient U/Z(U). -/
theorem source_shifted_displacement_range (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (a : F.H) (ha : (a : G) ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) :
    (F.uhatDisplacement a).range ≤ F.hatSubspace V := by
  obtain ⟨_, _, _, _, _, _, _, hbound⟩ := source_shifted_movement
    d earlier hq chosen structural alternatives F hne g l hgP hgH hlV hl hspace
  rintro v ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
  rw [show w = Additive.ofMul (F.uhatProjection u) from
    (congrArg Additive.ofMul hu).symm, F.uhatDisplacement_projection,
    F.mem_hatSubspace_projection V (le_conjugateSpanBy V F.H)]
  rw [commutator_comm] at hbound
  have hh := hbound (commutator_mem_commutator ha u.property)
  change (a : G) * (u : G) * (a : G)⁻¹ / (u : G) ∈ V ⊔ F.ZU
  simpa only [sup_comm, commutatorElement_def, div_eq_mul_inv] using hh

/-- Apply the displacement calculation to the actual shifted involution and
centralizer amalgam from 14.3.31, retaining its faithful, nontrivial action. -/
theorem source_shifted_amalgam_movement (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
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
        Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ⊓
          F.uhatAction.ker.map F.H.subtype = ⊥ ∧
        ⁅F.U, Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)⁆ ≤ F.ZU ⊔ V ∧
        K ≤ centralizer (F.ZU : Set G) ∧
        amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
        IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
        pCore 2 (AmalgamQuotient F L K) = ⊥ := by
  obtain ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI, heT, heU, heV,
    haH, ha, hfaith, hker, hK, hKe, hr, hcore⟩ :=
    source_shifted_amalgam_faithful d earlier hq chosen structural alternatives F hne hseed hI
  obtain ⟨_, _, _, _, _, _, _, hmove⟩ := source_shifted_movement
    d earlier hq chosen structural alternatives F hne g l hgP hgH (chosen.normalizes hlL) hl hspace
  exact ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI, heT, heU, heV,
    haH, ha, hfaith, hker, hmove, hK, hKe, hr, hcore⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
