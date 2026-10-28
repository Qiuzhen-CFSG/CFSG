module

public import CFSG.Quasithin.Chapter2.Source
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionSupplement
public import CFSG.Quasithin.Chapter10.SourceThompsonControl
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.Bender
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.Mathieu.M11.Properties.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The original Thompson movement on the L₃(2) omega module

The marked natural quotient supplies an involution `z` whose centralizer is
the normalizer of `L`.  If the original Thompson subgroup centralized the
chosen module, the full fixed-module argument would force the vanishing of
the nonzero fixed subgroup.  The only missing input to that argument is the
outside-maximal witness.  We obtain it from the actual Theorem 2.1.1
classification in the unique-overgroup branch: Bender and odd `PSL₂` models
have solvable relevant normalizers, while `PSL₃(3)` and `M₁₁` have orders
not divisible by the `7` forced by the marked `PSL₃(2)` quotient.

This keeps the exact original hypotheses and concludes movement first on the
chosen module, then on `Ω₁ Z(C_T(V))` using the proved inclusion of `V` in that
omega center.  No fixed supplement, commutator estimate, fusion conclusion,
or downstream classification is used.

Source: Aschbacher–Smith, 12.2.9(2), 12.4.3(2), 12.4.5(2), and 3.1.8(3),
combined manuscript (1 March 2004), printed pp.797–798, 813, and 576.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

private theorem nonsolvable_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ¬ Group.IsSolvable L := by
  intro hs
  let := hs
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) :=
    IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  exact Group.IsPerfect.not_isSolvable (L ⧸ pCore 2 L) inferInstance

omit [Finite G] in
private theorem seven_dvd_card (D : ChosenModule T L V) (E : SLThreeExtension D) :
    7 ∣ Nat.card G := by
  have hc : Nat.card (L ⧸ pCore 2 L) = 168 :=
    (Nat.card_congr E.quotientEquiv.toEquiv).trans Matrix.PSL3Two.card_SL
  have hd := (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _)).trans L.card_subgroup_dvd_card
  rw [hc] at hd
  exact (show 7 ∣ 168 from by decide).trans hd

private theorem not_theorem211_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (E : SLThreeExtension D)
    (z : G) (hz : orderOf z = 2)
    (hLC : L ≤ centralizer ({z} : Set G)) :
    ¬ ClassificationModels.IsTheorem211Model G := by
  intro hm
  cases hm with
  | bender hb =>
    let := D.elementary
    let := Chapter2.AlternatingTerminal.bender_two_subgroup_normalizer_solvable
      hb V (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
    exact nonsolvable_component h
      (Group.isSolvable_of_isSolvable_injective
        (f := inclusion D.normalizes) (inclusion_injective _))
  | linear_prime p hp hlarge hm =>
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
    let : Field F := hF
    let : Finite F := hfin
    have hez : GorensteinWalter.IsInvolution (e z) := by
      have ho : orderOf (e z) = 2 := (e.orderOf_eq z).trans hz
      exact ⟨by intro he; simp [he] at ho, by simpa only [ho] using pow_orderOf_eq_one (e z)⟩
    let := Theory.PSL2.involution_centralizer_isSolvable
      (show GorensteinWalter.IsOddPrimePower (Nat.card F) from
        ⟨p, 1, hp.1, hp.1.odd_of_ne_two (by omega), by decide, by simpa using hc⟩)
      (e z) hez
    let f : L →* centralizer ({e z} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := {
      toFun := fun l => ⟨e l, by
        apply mem_centralizer_singleton_iff.mpr
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hLC l.property)]⟩
      map_one' := Subtype.ext e.map_one
      map_mul' := fun a b => Subtype.ext (e.map_mul a b) }
    exact nonsolvable_component h
      (Group.isSolvable_of_isSolvable_injective (f := f)
        (fun a b he => Subtype.ext (e.injective (congrArg Subtype.val he))))
  | linear_three hm =>
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
    let : Field F := hF
    let : Finite F := hfin
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc
    let e' := e.trans (Atlas.fieldEquivPSL 3 (FiniteField.ringEquivOfCardEq hcard))
    have hGcard : Nat.card G = 5616 :=
      (Nat.card_congr e'.toEquiv).trans Matrix.PSL3Three.card_PSL
    have hd := seven_dvd_card D E
    rw [hGcard] at hd
    norm_num at hd
  | mathieu_eleven hm =>
    obtain ⟨e⟩ := hm
    have hGcard : Nat.card G = 7920 :=
      (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m11_order
    have hd := seven_dvd_card D E
    rw [hGcard] at hd
    norm_num at hd

theorem thompson_hasMaximalOutside
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (E : SLThreeExtension D)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hne : fixedSubgroup L V ≠ ⊥) :
    Chapter3.HasMaximalOutside T (normalizer (L : Set G)) := by
  classical
  obtain ⟨z, hz, _, hNC, _, _, _⟩ :=
    SLThreeCommutatorSource.fixed_involution_setup_of_card_two h D structural
      (E.fixed_card_eq_two hne)
  have hnot := not_theorem211_model h D E z hz (L.le_normalizer.trans_eq hNC)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  by_contra hout
  apply hnot
  apply Chapter2.theorem_2_1_1 h.simpleQTKE T _ hm (structural G T L h).1
  intro N hN hTN
  apply hN.eq_of_le hm.1
  by_contra hNM
  exact hout (Chapter3.hasMaximalOutside_of_two_distinct hm hN
    (structural G T L h).1 hTN (fun he => hNM he.le))

theorem thompson_moves_chosen_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  obtain ⟨E⟩ := marked G T L V h D hmodel hne
  have hout := thompson_hasMaximalOutside h D E structural hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hMV := ((structural G T L h).2.2 V D).2.2.2.resolve_right hne
  let F := D.fundamentalSetup h.toHypothesis1221
  have hm : F.moduleSubgroup = V := by
    rw [D.fundamentalSetup_module]
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTV)
      (le_componentOrbit _ _)
  have hf : F.fullModule = V := by
    rw [D.fundamentalSetup_fullModule]
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hMV)
      (le_componentOrbit _ _)
  intro hJ
  have hout' : Chapter3.HasMaximalOutside T F.maximalLocal := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal, D.localOrbit_eq] using hout
  have he := Chapter10.source_fullModule_fixed_eq_bot_of_centralizes
    F hout' (hm.symm ▸ hJ)
  rw [hf, D.localOrbit_eq] at he
  exact hne he

theorem thompson_moves_omega_center_of_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) : Set G) :=
  fun hJ => thompson_moves_chosen_of_source h D structural marked hmodel hne
    (hJ.trans (centralizer_le (chosen_le_omega_center D)))

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
