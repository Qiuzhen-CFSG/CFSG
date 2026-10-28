module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.AxisCases
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Sp4.Symplectic
public import Theory.SpecificGroups.SymplecticFour.ReciprocalSmallActors

/-!
# The single natural summand in the reciprocal Sp₄ case

For a faithful marked symplectic module, the actual group commutator embeds
in the linear displacement space. Symplectic orthogonality bounds its order
by the index of the original centralizer. The literal common-axis index is q,
whereas the forward natural coordinates give commutator order q^m. Hence m=1.

The conditional realization interface is retained, and its actual source
application discharges that premise with the symplectic homomorphism of
`Reciprocal.Sp4.Symplectic`, preserving the original conjugator and quotient.
Earlier natural-coordinate and fixed-space inputs are discharged by the final
owner qt-d-1222-shadow-common-action.
Source: Aschbacher--Smith 11.3.7(4), printed p.773 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal

private theorem symplectic_commutator_card_le_centralizer_index
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (U B : Subgroup G) (hn : B ≤ normalizer (U : Set G))
    (π : U →* Multiplicative (Vector F)) (hp : Function.Surjective π)
    (hi : Function.Injective π) (α : B →* Sp F)
    (hact : ∀ (b : B) (u : U),
      π (U.normalizerMonoidHom (inclusion hn b) u) =
        Multiplicative.ofAdd (α b • (π u).toAdd)) :
    Nat.card (⁅B,U⁆ : Subgroup G) ≤ (centralizer (B : Set G)).relIndex U := by
  let K := displacementSpace α.range
  let E₀ : Subgroup U := K.toAddSubgroup.toSubgroup.comap π
  let E : Subgroup G := E₀.map U.subtype
  have hCE : ⁅B,U⁆ ≤ E := by
    apply commutator_le.mpr
    intro b hb u hu
    let b' : B := ⟨b,hb⟩
    let u' : U := ⟨u,hu⟩
    let z : U := U.normalizerMonoidHom (inclusion hn b') u' * u'⁻¹
    refine ⟨z,?_,rfl⟩
    change (π z).toAdd ∈ K
    change (π (U.normalizerMonoidHom (inclusion hn b') u' * u'⁻¹)).toAdd ∈ K
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,hact]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp α.range.subtype) ⟨α b',⟨b',rfl⟩⟩ (π u').toAdd
  let j : E₀ → K := fun u => ⟨(π u.val).toAdd,u.property⟩
  have hj : Function.Injective j := by
    intro u v h
    apply Subtype.ext
    apply hi
    exact Multiplicative.toAdd.injective (congrArg Subtype.val h)
  calc
    Nat.card (⁅B,U⁆ : Subgroup G) ≤ Nat.card E := card_le_of_le hCE
    _ = Nat.card E₀ := card_map_of_injective U.subtype_injective
    _ ≤ Nat.card K := Nat.card_le_card_of_injective j hj
    _ = Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace α.range) := by
      rw [fixed_quotient_card,Module.natCard_eq_pow_finrank (K := F)]
    _ ≤ (centralizer (B : Set G)).relIndex U :=
      fixed_quotient_card_le_centralizer_index U B hn π hp α hact

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- A genuine symplectic realization forces one forward natural summand. -/
theorem source_sp4_multiplicity_of_realization
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hm : 0 < m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (α : omegaClosure T H →* Sp S.field.Carrier)
    (hα : ∀ w (v : Vector S.field.Carrier), α w • v = reciprocalAction (.sp4 a) g hN w v) : m = 1 := by
  let c := Coordinates.sp4 a
  let A := V.map (MulAut.conj g).toMonoidHom
  let e : V ≃* A := V.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  let π : A →* Multiplicative (Vector S.field.Carrier) := c.projection.comp e.symm.toMonoidHom
  have hi : Function.Injective c.projection := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro v hv
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfixed]
    exact ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩
  have hact (w : omegaClosure T H) (v : A) :
      π (A.normalizerMonoidHom (inclusion hN w) v) =
        Multiplicative.ofAdd (α w • (π v).toAdd) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd,hα]
    change (c.projection (e.symm (A.normalizerMonoidHom (inclusion hN w) v))).toAdd =
      reciprocalAction c g hN w (c.projection (e.symm v)).toAdd
    rw [reciprocalAction_projection]
    congr 2
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (w : G) * (v : G) * (w : G)⁻¹ = _
    rw [coe_equivMapOfInjective_apply]
    have hz : ((reciprocalNormalizerHom g hN w : normalizer (V : Set G)) : G) =
        g⁻¹ * (w : G) * g := by
      change g⁻¹ * (w : G) * (g⁻¹)⁻¹ = _
      rw [inv_inv]
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
      normalizerMonoidHom_apply_apply_coe,hz]
    have hv : g * (e.symm v : G) * g⁻¹ = (v : G) :=
      congrArg Subtype.val (e.apply_symm_apply v)
    calc
      _ = (w : G) * (g * (e.symm v : G) * g⁻¹) * (w : G)⁻¹ := by rw [hv]
      _ = _ := by group
  have hb := symplectic_commutator_card_le_centralizer_index A (omegaClosure T H) hN π
    (c.projection_surjective.comp e.symm.surjective) (hi.comp e.symm.injective) α hact
  rw [commutator_comm,n.commutator_eq_fixed,n.card_fixed] at hb
  change Nat.card S.field.Carrier ^ m ≤
    ((centralizer (omegaClosure T H : Set G)).comap A.subtype).index at hb
  rw [n.centralizer_index hm] at hb
  have hle : m ≤ 1 := (Nat.pow_le_pow_iff_right (Finite.one_lt_card (α := S.field.Carrier))).mp
    (by simpa only [pow_one] using hb)
  omega

/-- The original reciprocal Sp₄ case has exactly one natural summand,
with the symplectic-realization premise discharged. -/
theorem source_sp4_multiplicity
    (a : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 a))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hm : 0 < m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    m = 1 := by
  obtain ⟨α,hα⟩ := sp4_reciprocal_symplectic_realization a f g n hN
  exact source_sp4_multiplicity_of_realization a hfixed g n hm hN α hα

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
