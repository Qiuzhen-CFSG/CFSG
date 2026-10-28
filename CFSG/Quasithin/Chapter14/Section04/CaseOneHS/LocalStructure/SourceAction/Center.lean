module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Geometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Orders
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Quotients

/-!
# The center in the natural HS action branch

The actual SL₂(4) matrices are transitive on the nonzero quotient vectors.
The original elementary seed contains a noncentral involution. If the center
had exponent two, transitivity would put an involution in every noncentral
coset, making all of U have exponent two and hence commute.

Centerlessness and the symplectic form show that the literal intersection
E is the original seed V. The original parabolic quotient makes its X-image
an elementary subgroup of S₅, hence of order at most four. Counting its
kernel E, the hyperplane W, and U/Z(U) bounds the center by four. The preceding
nontrivial square then forces a cyclic center of order four.

The natural coordinates remain an explicit premise. This module proves the
center argument in 14.3.32 after its natural-action alternative has been
established; it does not prove the alternative exclusions or select a component.
Those obligations remain with qt-d-hs-action-source. The centerlessness premise
is discharged by the parent qt-d-hs-local-structure. The earlier naturality
input belongs to qt-d-1434-source, and the structural/escape inputs to
qt-d-1222-source.

Source: Aschbacher--Smith, 14.3.32, printed pp.1003--1004. The cyclicity
argument uses the same natural-module obstruction as the printed quadratic-form
argument, expressed directly through element squares and conjugation.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- Transitivity for the original H-action on the nonidentity quotient elements. -/
theorem NaturalCoordinates.transitive_nonidentity (F : InvariantFlag T V 3) (hc : NaturalCoordinates F)
    (x y : F.Uhat) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ h : F.H, F.uhatAction h x = y := by
  obtain ⟨e, c, he⟩ := hc
  have hcx : (c x).toAdd ≠ 0 := by
    intro hz
    apply hx
    apply c.injective
    simpa using congrArg Multiplicative.ofAdd hz
  have hcy : (c y).toAdd ≠ 0 := by
    intro hz
    apply hy
    apply c.injective
    simpa using congrArg Multiplicative.ofAdd hz
  obtain ⟨a, ha⟩ := Representation.SL2FourNatural.transitive_nonzero
    (c x).toAdd (c y).toAdd hcx hcy
  let a' : Representation.SL2FourNatural.SemilinearNormalizer.specialField :=
    ⟨Representation.SL2FourNatural.action a, (show Representation.SL2FourNatural.action.range ≤
      Representation.SL2FourNatural.SemilinearNormalizer.specialField from le_sup_left) ⟨a, rfl⟩⟩
  obtain ⟨q, hq⟩ := e.surjective a'
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) q
  refine ⟨h, c.injective ?_⟩
  have hh := he h x
  rw [hq] at hh
  exact congrArg Multiplicative.ofAdd (hh.trans ha)

private theorem noncentral_involution (F : InvariantFlag T V 3)
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

private theorem center_square_nontrivial (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] (hn : ¬ IsMulCommutative F.U)
    (h : V ⊓ F.ZU = F.Vi 1) (hc : NaturalCoordinates F) :
    ∃ z : center F.U, z ^ 2 ≠ 1 := by
  classical
  by_contra hz
  push Not at hz
  obtain ⟨v, hv, hvq⟩ := noncentral_involution F h
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

private theorem center_cyclic (F : InvariantFlag T V 3) [Finite G]
    [IsElementaryAbelian 2 V] (hn : ¬ IsMulCommutative F.U)
    (h : V ⊓ F.ZU = F.Vi 1) (hc : NaturalCoordinates F)
    (hcard : Nat.card (center F.U) = 4) : IsCyclic (center F.U) := by
  obtain ⟨z, hz⟩ := center_square_nontrivial F hn h hc
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

/-- The source isotropic intersection equals the literal elementary seed. -/
theorem source_intersection_eq_seed_of_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : F.E g = V := by
  exact source_intersection_eq_seed_of_card_sixteen d earlier hq chosen structural alternatives
    F hne hI (hc.card_uhat F) g hgP hgH

private theorem center_card_le_four (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : Nat.card (center F.U) ≤ 4 := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  obtain ⟨⟨hn, he⟩, hhat, _, hindex⟩ := source_parabolic_action d earlier hq chosen
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
    rw [source_intersection_eq_seed_of_natural d earlier hq chosen structural alternatives F hne hI hc g hgP hgH]
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

/-- Construct both intrinsic center conclusions from natural coordinates and
the original source geometry, with no center order or cyclicity hypothesis. -/
theorem source_center_of_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    IsCyclic (center F.U) ∧ Nat.card (center F.U) = 4 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨β, _, b, _, hcuts, _, _⟩ := F.exists_marked_naturalFlag L chosen.normalizes h.full_L_action
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (show (T : Subgroup G) ≤ normalizer (V : Set G) from F.last ▸ F.invariant 3)
    (h.binarySeedAction_surjective F) β b hcuts
  have hb := center_card_le_four d earlier hq chosen structural alternatives F hne hI hc g hgP hgH
  obtain ⟨htwo, _, hVZ⟩ := source_closure d earlier hq chosen structural alternatives F hne
  obtain ⟨z, hz⟩ := center_square_nontrivial F hne hVZ hc
  have hnc : ¬ Nat.card (center F.U) ∣ 2 := fun hd => hz
    (orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard z).trans hd))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (htwo.to_subgroup (center F.U))
  have hcard : Nat.card (center F.U) = 4 := by
    have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hb)
    interval_cases n
    · exact (hnc (by rw [hn]; norm_num)).elim
    · exact (hnc (by rw [hn]; norm_num)).elim
    · exact hn
  exact ⟨center_cyclic F hne hVZ hc hcard, hcard⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
