module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.FourSpace

/-!
# The natural HS action and component at G,T

Under the earlier centerlessness conclusion, the marked action
alternatives yield actual semilinear SL2(4) coordinates. The center is
cyclic of order four, and the original component gives H=KT,
U=[O2(K),K] and indecomposability on U/V1. Applying the established
central-product construction supplies every LocalStructure field.
Source: Aschbacher--Smith 14.3.32, pp.1003--1004.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/NaturalOrder.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open SL2FourNatural
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private def naturalOrder_concreteCoordinates_at : SL2FourNatural.V ≃ₗ[ZMod 2]
    (Fin 2 → OrthogonalFourMinus.FiniteModel.Field 1) where
  toFun v i := fieldEquiv (v i)
  invFun v i := fieldEquiv.symm (v i)
  left_inv v := by funext i; exact fieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact fieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add fieldEquiv _ _
  map_smul' c v := by funext i; exact ZMod.map_smul fieldEquiv c (v i)
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI
theorem source_four_residual_concrete_coordinates_at
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) :
    ∃ (e : solvableResidual F.TerminalHdot ≃* SL)
      (c : Additive F.Uhat ≃ₗ[ZMod 2] SL2FourNatural.V),
      ∀ a w, c (F.terminalRepresentation a.val w)=action (e a) (c w) := by
  obtain ⟨e,⟨E⟩⟩ := source_four_residual_natural_at d earlier hq chosen structural alternatives
    F hne hZ hI hd
  let e' := e.trans standardGroupEquiv.symm
  let c := E.toLinearEquiv.trans naturalOrder_concreteCoordinates_at.symm
  refine ⟨e',c,?_⟩
  intro a w
  have hi := IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap a w
  change E (F.terminalRepresentation a.val w) = specialLinearNatural 2 (e a) (E w) at hi
  apply naturalOrder_concreteCoordinates_at.injective
  change naturalOrder_concreteCoordinates_at (naturalOrder_concreteCoordinates_at.symm (E (F.terminalRepresentation a.val w))) =
    naturalOrder_concreteCoordinates_at (action (e' a) (c w))
  rw [naturalOrder_concreteCoordinates_at.apply_symm_apply]
  change _ = standardVectorEquiv (action (e' a) (c w))
  rw [standard_equivariant]
  change _ = specialLinearNatural 2 (standardGroupEquiv (standardGroupEquiv.symm (e a)))
    (naturalOrder_concreteCoordinates_at (naturalOrder_concreteCoordinates_at.symm (E w)))
  rw [standardGroupEquiv.apply_symm_apply,naturalOrder_concreteCoordinates_at.apply_symm_apply]
  exact hi
theorem source_four_card_oneTwenty_at (hd : finrank (ZMod 2) (Additive F.Uhat)=4) :
    Nat.card F.TerminalHdot=120 := by
  have hc : Nat.card F.Uhat=16 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    simpa only [Nat.card_zmod,hd,show (2 : ℕ)^4=16 by decide] using hh
  rcases source_four_card_sixty_or_oneTwenty_at d earlier hq chosen structural alternatives
    F hne hZ hI hc with h60 | h120
  · exfalso
    obtain ⟨eA⟩ := source_four_residual_alternatingFive_at d earlier hq chosen structural alternatives
      F hne hZ hI hc
    have hR : solvableResidual F.TerminalHdot = ⊤ := by
      apply eq_of_le_of_card_ge le_top
      rw [card_top,h60,Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    let R := solvableResidual F.TerminalHdot
    let eR : R ≃* F.TerminalHdot := MulEquiv.ofBijective R.subtype
      ⟨Subtype.val_injective, fun a => ⟨⟨a,by change a ∈ solvableResidual F.TerminalHdot; rw [hR]; exact mem_top a⟩,rfl⟩⟩
    have heR (a : F.TerminalHdot) : (eR.symm a).val=a := eR.apply_symm_apply a
    obtain ⟨e,c,he⟩ := source_four_residual_concrete_coordinates_at d earlier hq chosen structural alternatives
      F hne hZ hI hd
    let e' := eR.symm.trans e
    have he' (a : F.TerminalHdot) (w : Additive F.Uhat) :
        c (F.terminalRepresentation a w)=action (e' a) (c w) := by
      simpa only [e',MulEquiv.trans_apply,heR] using he (eR.symm a) w
    let := chosen.elementary
    obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
    obtain ⟨heU,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
      d earlier hq chosen structural alternatives hne g hgP hgH
    let := heX
    have hb := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
      F g hne hZ hgP hgH
    have hX : 4≤Nat.card (F.terminalDot (F.X g)) := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Additive (F.terminalDot (F.X g)))
      change Nat.card (F.terminalDot (F.X g)) = _ at hh
      rw [hh,Nat.card_zmod]
      exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))
    have hW : finrank (ZMod 2) (hatSpace F (F.E g))=2 := by
      rw [source_intersection_eq_seed_of_card_sixteen_at d earlier hq chosen structural alternatives
        F hne hI hc g hgP hgH]
      exact seed_hat_dimension F (source_closure_at d earlier hq chosen structural alternatives F hne).2.2
    exact ChapterG.Section11.FourNatural.not_special_linear hyp hW hX e' c he'
  · exact h120
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/Center.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {V : Subgroup G}
private theorem center_noncentral_involution_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] (h : V ⊓ F.ZU = F.Vi 1) :
    ∃ v : F.U, v ^ 2 = 1 ∧ QuotientGroup.mk' (center F.U) v ≠ 1 := by
  have hn : ¬ V ≤ F.ZU := by
    intro hv
    have he : V = F.Vi 1 := (inf_eq_left.mpr hv).symm.trans h
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [he] at hc
    have hc1 : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    omega
  obtain ⟨v, hv, hz⟩ := SetLike.not_le_iff_exists.mp hn
  let v' : F.U := ⟨v, le_conjugateSpanBy V F.H hv⟩
  refine ⟨v', ?_, ?_⟩
  · apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  · intro he
    have hc : v' ∈ center F.U := (QuotientGroup.eq_one_iff (N := center F.U) v').mp he
    exact hz (mem_map_of_mem _ hc)
private theorem center_center_square_nontrivial_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] (hn : ¬ IsMulCommutative F.U)
    (h : V ⊓ F.ZU = F.Vi 1) (hc : NaturalCoordinates F) :
    ∃ z : center F.U, z ^ 2 ≠ 1 := by
  classical
  by_contra hz
  push Not at hz
  obtain ⟨v, hv, hvq⟩ := center_noncentral_involution_at F h
  have hs (x : F.U) : x ^ 2 = 1 := by
    by_cases hx : QuotientGroup.mk' (center F.U) x = 1
    · have hxz : x ∈ center F.U := (QuotientGroup.eq_one_iff (N := center F.U) x).mp hx
      exact congrArg Subtype.val (hz ⟨x, hxz⟩)
    · obtain ⟨a, ha⟩ := NaturalCoordinates.transitive_nonidentity F hc _ _ hvq hx
      rw [F.uhatAction_apply_mk] at ha
      have hzmem : F.uAction a v / x ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp ha
      let z : center F.U := ⟨F.uAction a v / x, hzmem⟩
      have he : (z : F.U) * x = F.uAction a v := div_mul_cancel _ _
      have hcomm : Commute (z : F.U) x := (mem_center_iff.mp z.property x).symm
      have hp : ((z : F.U) * x) ^ 2 = 1 := by rw [he, ← map_pow, hv, map_one]
      rw [hcomm.mul_pow, show (z : F.U) ^ 2 = 1 from congrArg Subtype.val (hz z), one_mul] at hp
      exact hp
  apply hn
  have hi (x : F.U) : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
  refine ⟨⟨fun a b => ?_⟩⟩
  calc
    a * b = (a * b)⁻¹ := (hi _).symm
    _ = b * a := by rw [mul_inv_rev, hi, hi]
private theorem center_center_cyclic_at (F : InvariantFlag T V 3) [Finite G]
    [IsElementaryAbelian 2 V] (hn : ¬ IsMulCommutative F.U)
    (h : V ⊓ F.ZU = F.Vi 1) (hc : NaturalCoordinates F)
    (hcard : Nat.card (center F.U) = 4) : IsCyclic (center F.U) := by
  obtain ⟨z, hz⟩ := center_center_square_nontrivial_at F hn h hc
  apply isCyclic_of_orderOf_eq_card z
  have hd : orderOf z ∣ 4 := hcard ▸ orderOf_dvd_natCard z
  have hn2 : ¬ orderOf z ∣ 2 := by simpa only [orderOf_dvd_iff_pow_eq_one] using hz
  have he : orderOf z = 4 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases orderOf z <;> norm_num at *
  exact he.trans hcard.symm
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_intersection_eq_seed_of_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : F.E g = V := by
  exact source_intersection_eq_seed_of_card_sixteen_at d earlier hq chosen structural alternatives
    F hne hI (hc.card_uhat F) g hgP hgH
private theorem center_center_card_le_four_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : Nat.card (center F.U) ≤ 4 := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  obtain ⟨⟨hn, he⟩, hhat, _, hindex⟩ := source_parabolic_action_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  let := hn
  let := he
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  let := Xdot_uhatAction_elementary F g hgG
  have hXH := F.X_le_H g hgG
  have hk : (dotMap F F.uhatAction (F.X g) hXH).ker = (F.E g).subgroupOf (F.X g) := by
    rw [dotMap_ker]
    change (F.xHatAction g hgG).ker = _
    rw [← hhat]
    exact (comap_map_eq_self_of_injective (F.X g).subtype_injective _).symm
  have hcopy := hc
  obtain ⟨eqv, _, _⟩ := hcopy
  let eqh := (QuotientGroup.quotientMulEquivOfEq (hc.kernel F)).trans
    (eqv.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv)
  let f := eqh.toMonoidHom.comp (dotImage F F.uhatAction (F.X g)).subtype
  have hf : Function.Injective f := eqh.injective.comp Subtype.val_injective
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  have himg : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 4 := by
    have hh := (primeRank_le_iff_elementary_card_le (Equiv.Perm (Fin 5))).mp
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two f.range inferInstance
    rwa [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hh
  have hEc : Nat.card (F.E g) = 8 := by
    rw [source_intersection_eq_seed_of_natural_at d earlier hq chosen structural alternatives F hne hI hc g hgP hgH]
    simpa [F.last] using F.card 3 (by decide)
  have hXc := (dotMap F F.uhatAction (F.X g) hXH).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (dotMap_surjective F F.uhatAction (F.X g) hXH),
    card_top, hk, Nat.card_congr (subgroupOfEquivOfLe (show F.E g ≤ F.X g from inf_le_right)).toEquiv,
    hEc] at hXc
  have hWc := (F.W.subgroupOf F.U).index_mul_card
  rw [show (F.W.subgroupOf F.U).index = F.W.relIndex F.U from rfl,
    hindex, Nat.card_congr (subgroupOfEquivOfLe (show F.W ≤ F.U from inf_le_left)).toEquiv] at hWc
  have hXW : Nat.card (F.X g) = Nat.card F.W :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hUc := (center F.U).card_eq_card_quotient_mul_card_subgroup
  rw [hc.card_uhat F] at hUc
  omega
theorem source_center_of_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    IsCyclic (center F.U) ∧ Nat.card (center F.U) = 4 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨β, _, b, _, hcuts, _, _⟩ := F.exists_marked_naturalFlag L chosen.normalizes h.full_L_action
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (show (T : Subgroup G) ≤ normalizer (V : Set G) from F.last ▸ F.invariant 3)
    (h.binarySeedAction_surjective F) β b hcuts
  have hb := center_center_card_le_four_at d earlier hq chosen structural alternatives F hne hI hc g hgP hgH
  obtain ⟨htwo, _, hVZ⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  obtain ⟨z, hz⟩ := center_center_square_nontrivial_at F hne hVZ hc
  have hnc : ¬ Nat.card (center F.U) ∣ 2 := fun hd => hz
    (orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard z).trans hd))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (htwo.to_subgroup (center F.U))
  have hcard : Nat.card (center F.U) = 4 := by
    have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hb)
    interval_cases n
    · exact (hnc (by rw [hn]; norm_num)).elim
    · exact (hnc (by rw [hn]; norm_num)).elim
    · exact hn
  exact ⟨center_center_cyclic_at F hne hVZ hc hcard, hcard⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/CoreMovement.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem coreMovement_parabolic_core_bound_at [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) (htwo : IsPGroup 2 F.U)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hindex : F.W.relIndex F.U = 2)
    (g : G) (hg : g ∈ F.Gi 2) (hinter : F.X g ⊓ F.H.pCoreIn 2 ≤ F.U) :
    ⁅F.H.pCoreIn 2, F.X g⁆ ≤ F.U := by
  let Q := F.H.pCoreIn 2
  let C := centralizer (F.Vi 2 : Set G)
  let D := commutatorPreimage F.H (F.X g) F.U
  have hHU := le_normalizer_conjugateSpanBy V F.H
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes htwo F.U_le_H hHU
  have hQH : Q ≤ F.H := pCoreIn_le 2 F.H
  have hHQ : F.H ≤ normalizer (Q : Set G) := F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hh hq
    exact hx
  have hUG : F.U ≤ F.Gi 2 := F.U_le_G₂_of_commutator hcomm
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  let : IsElementaryAbelian 2 (F.Vi 2) :=
    IsElementaryAbelian.of_injective (inclusion (F.le_seed 2)) (inclusion_injective _)
  have hfact := F.H2_eq_plane_centralizer_sup_U (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex)
  have hUD : F.U ≤ D := le_commutatorPreimage F.U_le_H
    (le_normalizer_iff_commutator_le_left.mp (F.X_normalizes_U g hg))
  have hCD : Q ⊓ C ≤ D := by
    apply le_commutatorPreimage (inf_le_left.trans hQH)
    apply le_trans (le_inf
      (le_normalizer_iff_commutator_le_right.mp
        (inf_le_right.trans (F.plane_centralizer_normalizes_actors g hg).1))
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp ((F.X_le_H g hg).trans hHQ))))
      hinter
  have hQD : Q ≤ D := by
    intro q hq
    have hqgen : q ∈ C ⊔ F.U := hfact ▸ ⟨hQH hq, F.invariant 2 (hQT hq)⟩
    have hprod : ((C ⊔ F.U : Subgroup G) : Set G) = (C : Set G) * (F.U : Set G) :=
      coe_mul_of_right_le_normalizer_left C F.U
        (hUG.trans (normalizer_le_normalizer_centralizer _))
    obtain ⟨c, hc, w, hw, he⟩ := hprod ▸ (show q ∈ ((C ⊔ F.U : Subgroup G) : Set G) from hqgen)
    have hcQ : c ∈ Q := by
      have hcw : c * w ∈ Q := by rwa [show c * w = q from he]
      exact (Q.mul_mem_cancel_right (hUQ hw)).mp hcw
    rw [← he]
    exact D.mul_mem (hCD ⟨hcQ, hc⟩) (hUD hw)
  exact (commutator_mono hQD le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hHU)
private theorem coreMovement_residual_bound_of_symmetricFive_at {J : Type*} [Group J] [Finite J]
    (e : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5))
    (U X : Subgroup J) [U.Normal] (hX : ¬ X ≤ pCore 2 J)
    (hbound : ⁅pCore 2 J, X⁆ ≤ U) : ⁅pCore 2 J, solvableResidual J⁆ ≤ U := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 J := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let N := normalClosure (X : Set J)
  let : (N.map f).Normal := Normal.map inferInstance f hf
  have hn : N.map f ≠ ⊥ := by
    intro hn
    have hle := (map_eq_bot_iff N).mp hn
    exact hX ((show X ≤ N from le_normalClosure).trans (hle.trans_eq hk))
  have ha : alternatingGroup (Fin 5) ≤ N.map f :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hn)
  have hm : (solvableResidual J).map f ≤ N.map f := by
    rw [map_solvableResidual_eq f hf,
      Theory.SpecificGroups.SymmetricFive.WreathComponents.symmetric_residual]
    exact ha
  have hp : IsPPerfect 2 (solvableResidual J) := by
    intro A hA hq
    let := hA
    let := hq.isNilpotent
    exact top_unique (by simpa using solvableResidual_le_of_solvable_quotient A)
  have hKN : solvableResidual J ≤ N :=
    isPPerfect_le_of_map_le_of_kernel_normalizes f _ _ hp
      (hk ▸ pCore_isPGroup) le_normalizer_of_normal hm
  exact (commutator_mono le_rfl hKN).trans
    (commutator_normalClosure_le_of_normal _ _ _ hbound)
theorem source_component_core_bound_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    ⁅(sourceComponent F).pCoreIn 2, sourceComponent F⁆ ≤ F.U := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, _, hVZ⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
  obtain ⟨β, _, b, _, hcuts, _, _⟩ := F.exists_marked_naturalFlag L chosen.normalizes h.full_L_action
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (show (T : Subgroup G) ≤ normalizer (V : Set G) from F.last ▸ F.invariant 3)
    (h.binarySeedAction_surjective F) β b hcuts
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hXH := F.X_le_H g hgG
  have hker := (F.binary_source_action_kernel_intersections (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hcomm hsquare
    (source_seed_geometry_at d earlier hq chosen F).2.1 hne hVZ g hgP hgH).1
  rw [hc.kernel F] at hker
  have hbound : ⁅F.H.pCoreIn 2, F.X g⁆ ≤ F.U :=
    coreMovement_parabolic_core_bound_at F htwo hcomm
      (source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.2.2
      g hgG (hker.le.trans (inf_le_left.trans inf_le_left))
  have hnot : ¬ (F.X g).subgroupOf F.H ≤ pCore 2 F.H := by
    intro hh
    apply source_conjugate_center_image_nontrivial_at d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH
    apply le_bot_iff.mp
    rintro _ ⟨z, rfl⟩
    change F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1
    apply (show _ ∈ F.uhatAction.ker from ?_)
    rw [hc.kernel F]
    exact hh (F.conjugate_ZU_le_X g z.property)
  let : (F.U.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V F.H)
  have hb : ⁅pCore 2 F.H, (F.X g).subgroupOf F.H⁆ ≤ F.U.subgroupOf F.H := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hXH]
    exact hbound
  obtain ⟨e, _, _⟩ := hc
  have hr := map_mono (f := F.H.subtype) (coreMovement_residual_bound_of_symmetricFive_at
    (e.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv)
    (F.U.subgroupOf F.H) ((F.X g).subgroupOf F.H) hnot hb)
  rw [map_commutator, map_subgroupOf_eq_of_le F.U_le_H] at hr
  exact (commutator_mono
    (pCoreIn_mono_of_normalizes (sourceComponent_le F)
      ((normal_subgroupOf_iff_le_normalizer (sourceComponent_le F)).mp (sourceComponent_normal F)))
    le_rfl).trans hr
theorem source_component_of_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
      TildeIndecomposable F K := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  have hcard := (source_center_of_natural_at d earlier hq chosen structural alternatives F hne hI hc).2
  refine ⟨sourceComponent F, sourceComponent_le F, hc.sourceComponent_isCComponent F,
    hc.sourceComponent_supplement F, ?_, hc.tildeIndecomposable F htwo hphi hne hcard⟩
  apply le_antisymm
  · rw [← hc.commutator_eq_self F htwo hphi hne hcard]
    exact commutator_mono (hc.le_component_core F htwo hphi hne hcard) le_rfl
  · exact source_component_core_bound_at d earlier hq chosen structural alternatives F hne hZ hI hc
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/DottedNatural.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_naturalCoordinates_of_dotted_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : DottedNaturalCoordinates F) : NaturalCoordinates F := by
  obtain ⟨e, c, he⟩ := hc
  have hcard : Nat.card F.Uhat = 16 := by
    rw [Nat.card_congr c.toEquiv]
    change Nat.card Representation.SL2FourNatural.V = 16
    rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_vector]
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨β, _, b, _, hcuts, _, _⟩ := F.exists_marked_naturalFlag L chosen.normalizes h.full_L_action
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (show (T : Subgroup G) ≤ normalizer (V : Set G) from F.last ▸ F.invariant 3)
    (h.binarySeedAction_surjective F) β b hcuts
  let := source_actor_elementary_at d earlier hq chosen structural alternatives F hne g hgP hgH
  have hr : primeRank 2 (Hdot F F.uhatAction) ≤ 2 := by
    rw [primeRank_equiv 2 (e.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv)]
    exact Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  have hX : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 4 :=
    (primeRank_le_iff_elementary_card_le (Hdot F F.uhatAction)).mp hr _ inferInstance
  have ht := (source_four_dimensional_orders_at d earlier hq chosen structural alternatives F hne hZ hI
    hcard g hgP hgH hX).2.2.2
  have hk := source_small_center_kernel_at d earlier hq chosen structural alternatives F ht.le
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans e, c, ?_⟩
  intro a x
  exact he a x
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction.lean. -/
section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem actionStructure_of_natural_component_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (component : ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
      TildeIndecomposable F K) : ActionStructure F := by
  obtain ⟨hcyclic, hcard⟩ := source_center_of_natural_at d earlier hq chosen structural
    alternatives F hne hI hc
  exact ⟨hc, hcyclic, hcard, component⟩
theorem actionStructure_of_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    ActionStructure F :=
  actionStructure_of_natural_component_at d earlier hq chosen structural alternatives F hne hI hc
    (source_component_of_natural_at d earlier hq chosen structural alternatives F hne hZ hI hc)
theorem actionStructure_of_dotted_natural_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : DottedNaturalCoordinates F) : ActionStructure F :=
  actionStructure_of_natural_at d earlier hq chosen structural alternatives F hne hZ hI
    (source_naturalCoordinates_of_dotted_at d earlier hq chosen structural alternatives F hne hZ hI hc)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/FourCoordinates.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI
theorem source_four_dotted_natural_at
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) : DottedNaturalCoordinates F := by
  obtain ⟨e,c,he⟩ := source_four_residual_concrete_coordinates_at d earlier hq chosen structural alternatives
    F hne hZ hI hd
  obtain ⟨E,C,hE⟩ := SL2FourNatural.SemilinearNormalizer.coordinates_of_order_oneTwenty
    F.terminalRepresentation F.terminalRepresentation_injective
    (source_four_card_oneTwenty_at d earlier hq chosen structural alternatives F hne hZ hI hd)
    (solvableResidual F.TerminalHdot) e c he
  refine ⟨E,C.toAddEquiv.toMultiplicativeRight,?_⟩
  intro a w
  exact hE (QuotientGroup.mk' F.terminalHatAction.ker a) (Additive.ofMul w)
theorem source_four_actionStructure_at
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) : ActionStructure F :=
  actionStructure_of_dotted_natural_at d earlier hq chosen structural alternatives F hne hZ hI
    (source_four_dotted_natural_at d earlier hq chosen structural alternatives F hne hZ hI hd)
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_action_or_whole_recognition_of_centerless_at
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ActionStructure F ∨
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      IsIrreducible F.terminalRepresentation ∧
      6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
      ¬ Group.IsSolvable F.TerminalHdot ∧
      ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
        ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
        ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
          F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
          (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
        ChapterG.Section11.WholeComponentCandidates.Alternatives F.terminalRepresentation J
          (componentOrbit J ⊤) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hi,hs,hcases⟩ :=
    source_nonsolvable_four_or_whole_recognition_of_centerless_at d earlier hq chosen structural
      alternatives F hne hZ hI g hgP hgH
  let := heU
  let := heX
  rcases hcases with ⟨hfour,_,_⟩ | hwhole
  · exact .inl (source_four_actionStructure_at d earlier hq chosen structural alternatives
      F hne hZ hI hfour.1)
  · exact .inr ⟨heU,heX,B,v,hyp,hline,hw,hn,hwhole⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/WholeComponents.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI
theorem source_no_whole_alternating_eight_at
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (J : Subgroup F.TerminalHdot)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) J J
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    (e₀ : J ≃* alternatingGroup (Fin 8)) : False := by
  let := h9.normal_H
  obtain ⟨e,c,hc⟩ :=
    ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
      h9 (LargeWhole.selfDual hyp)
      (e₀.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  have hJc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation hyp.faithful J e c hc
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 8))
  let : IsSimpleGroup J := e.isSimpleGroup
  have hJa : ¬ IsMulCommutative J := fun hh =>
    h9.component.isCComponent.not_isSolvable (by let := hh; infer_instance)
  have hJC := source_simple_normal_le_center_centralizer_at d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH J hJa hJc
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hr : 2 ≤ primeRank 3 (C.subgroupOf J) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp J.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c hc v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let f : C.subgroupOf J →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hJC a.val.property⟩,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C.subgroupOf D => z.val.val) he))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hu := source_center_centralizing_point_image_three_rank_le_one_at d earlier hq chosen
    structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  omega
theorem source_no_whole_component_at
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hw : LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hd : 6 ≤ finrank (ZMod 2) (Additive F.Uhat))
    (J : Subgroup F.TerminalHdot)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) : False := by
  have hlarge := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  by_cases he : componentOrbit J ⊤ = J
  · rw [he] at h9
    obtain ⟨_,hc⟩ := LargeWhole.single_small_carrier hyp h9 hw hS hd hlarge
    cases hc with
    | seven e =>
      exact LargeWhole.not_seven_of_smaller_ne_bot hyp h9 hd
        (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
        (source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives
          F hne hZ g hgP hgH) e.some
    | eight e =>
      exact source_no_whole_alternating_eight_at d earlier hq chosen structural alternatives
        F hne hZ hI g hgP hgH B v hyp hline J h9 e.some
    | binary_g2 e =>
      exact source_no_caseSix_at d earlier hq chosen structural alternatives F hne hZ hI
        (LargeWhole.caseSix_of_binary_g2 hyp h9 hd hlarge e.some)
  · exact LargeWhole.not_component_pair hyp hw hlarge h9 he
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_actionStructure_of_centerless_at : ActionStructure F := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  rcases source_action_or_whole_recognition_of_centerless_at d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH with ha | ⟨heU,heX,B,v,hyp,hline,hw,hS,_,hd,_,J,_,_,_,h9,_⟩
  · exact ha
  · let := heU
    let := heX
    exact (source_no_whole_component_at d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH B v hyp hline hw hS hd J h9).elim
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_localStructure_of_centerless_at : LocalStructure L F :=
  localStructure_of_centerless_action_at d earlier hq chosen structural alternatives F hne hI
    (source_actionStructure_of_centerless_at d earlier hq chosen structural alternatives F hne hZ hI)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end
