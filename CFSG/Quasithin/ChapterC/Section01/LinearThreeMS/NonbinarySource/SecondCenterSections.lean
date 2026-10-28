module
public import Theory.GroupTheory.PGroup.SecondCenterFrattiniPairing
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.DoubledCenter

/-!
# Marked upper commutator sections of the original MS core

A natural or doubled-natural model of the whole center gives an elementary
center on the original core Q. Pair Z₂(Q)/Z(Q) faithfully with Q/Φ(Q), using
the actual commutator and coordinates on that whole center. Simultaneous
conjugation transports the pairing by the same supplied SL₃ marking. Both
natural summands and all original quotient maps are retained.

For a nonabelian Q the upper section is nonzero. Its numerator centralizes
Φ(Q), its quotient by Z(Q) is elementary, and its exponent divides four.
Thus it lies in the literal D=C_Q(Φ(Q)) occurring in the source alternatives.
The natural and doubled whole-omega reconstructions discharge the center
premise at every n>1. NonblockSecondCenter applies this to the original
field-four configuration without a center-model or classification callback.

This constructs an actual upper section, not the entire Q/Z(Q). Proving
that Q has class two in the third row, identifying the doubled-dual upper
module, excluding the nonabelian doubled-center branch and treating the
arbitrary-degree fixed factor remain necessary for full C.1.34.
Source: Aschbacher–Smith C.1.34, printed pp.136–137, and original 4.3.8–10,
pp.616–617. The pairing uses the elementary commutator identities and
Frattini functoriality proved in Theory.GroupTheory.PGroup.SecondCenterFrattiniPairing.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K Q : Subgroup G}
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
local notation "Z₂" => Subgroup.upperCentralSeries Q 2

/-- The second center of the actual core, embedded in the original group. -/
@[expose] def secondCenterIn (Q : Subgroup G) : Subgroup G := (Subgroup.upperCentralSeries Q 2).map Q.subtype

/-- Marked commutator coordinates on the actual second central quotient.
The second input is the entire original Frattini quotient. -/
def HasCommutatorCoordinates {F W X : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Group X] (K Q : Subgroup G) (a : K →* X) (ρ : Representation F X W) : Prop :=
  ∃ c : center Q ≃* Multiplicative W,
    ∃ b : ((Subgroup.upperCentralSeries Q 2) ⧸
        (center Q).subgroupOf (Subgroup.upperCentralSeries Q 2)) →*
        ((Q ⧸ frattini Q) →* Multiplicative W),
      Function.Injective b ∧
      (∀ (k : K) (z z' : center Q), ((z':Q):G)=(k:G)*((z:Q):G)*(k:G)⁻¹ →
        (c z').toAdd=ρ (a k) (c z).toAdd) ∧
      (∀ (x : Subgroup.upperCentralSeries Q 2) (y : Q),
        (c.symm (b (QuotientGroup.mk' _ x) (QuotientGroup.mk' (frattini Q) y)) : Q) =
          ⁅(x:Q),y⁆) ∧
      (∀ (k : K) (x x' : Subgroup.upperCentralSeries Q 2) (y y' : Q),
        (x'.val:G)=(k:G)*(x.val:G)*(k:G)⁻¹ → (y':G)=(k:G)*(y:G)*(k:G)⁻¹ →
        (b (QuotientGroup.mk' _ x') (QuotientGroup.mk' (frattini Q) y')).toAdd =
          ρ (a k) (b (QuotientGroup.mk' _ x) (QuotientGroup.mk' (frattini Q) y)).toAdd)

private def centerEmbedding : center Q ≃* Z :=
  (center Q).equivMapOfInjective Q.subtype Q.subtype_injective

/-- Any model of the whole elementary center gives faithful, equivariant
coordinates for the second central section at exactly that same marking. -/
theorem exists_marked_pairing {F W X : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Group X] [IsElementaryAbelian 2 (Multiplicative W)]
    (a : K →* X) (ρ : Representation F X W)
    (hm : HasSectionModel K Z ⊥ a ρ) :
    IsElementaryAbelian 2 (center Q) ∧ HasCommutatorCoordinates K Q a ρ := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKZ,_,hi,b0,hb0⟩ := hm
  let := hi
  let d : Z ≃* Multiplicative W := QuotientGroup.quotientBot.symm.trans b0
  let c : center Q ≃* Multiplicative W := centerEmbedding.trans d
  let : IsElementaryAbelian 2 (center Q) := IsElementaryAbelian.of_injective c.toMonoidHom c.injective
  let b := (SecondCenterFrattini.pairing (P := Q)).compr₂ c.toMonoidHom
  have hbinj : Function.Injective b := by
    intro x y he
    apply SecondCenterFrattini.pairing_injective
    apply MonoidHom.ext
    intro v
    apply c.injective
    exact DFunLike.congr_fun he v
  have hval (x : Z₂) (y : Q) :
      (c.symm (b (QuotientGroup.mk' _ x) (QuotientGroup.mk' (frattini Q) y)) : Q)=⁅(x:Q),y⁆ := by
    change (c.symm (c (SecondCenterFrattini.pairing _ _)) : Q)=_
    rw [c.symm_apply_apply,SecondCenterFrattini.pairing_apply]
  have hc (k : K) (z z' : center Q)
      (hz : ((z':Q):G)=(k:G)*((z:Q):G)*(k:G)⁻¹) :
      (c z').toAdd=ρ (a k) (c z).toAdd :=
    hb0 k (centerEmbedding z) (centerEmbedding z') hz
  refine ⟨inferInstance,c,b,hbinj,hc,hval,?_⟩
  intro k x x' y y' hxx hyy
  let z : center Q := c.symm (b (QuotientGroup.mk' _ x) (QuotientGroup.mk' (frattini Q) y))
  let z' : center Q := c.symm (b (QuotientGroup.mk' _ x') (QuotientGroup.mk' (frattini Q) y'))
  have hz : (centerEmbedding z':G)=(k:G)*(centerEmbedding z:G)*(k:G)⁻¹ := by
    change ((z':Q):G)=(k:G)*((z:Q):G)*(k:G)⁻¹
    dsimp only [z,z']
    rw [hval,hval]
    change ⁅(x'.val:G),(y':G)⁆=(k:G)*⁅(x.val:G),(y:G)⁆*(k:G)⁻¹
    rw [hxx,hyy]
    exact (map_commutatorElement (MulAut.conj (k:G)) (x.val:G) (y:G)).symm
  have he := hb0 k (centerEmbedding z) (centerEmbedding z') hz
  change (c z').toAdd=ρ (a k) (c z).toAdd at he
  simpa only [z,z',c.apply_symm_apply] using he

/-- The upper section is nonzero for a nonabelian core; it lies in the literal
Frattini centralizer, and has elementary quotient and exponent at most four. -/
theorem upper_structure (hQ : IsPGroup 2 Q) (hna : ¬IsMulCommutative Q)
    [IsElementaryAbelian 2 (center Q)] :
    Z < secondCenterIn Q ∧
      secondCenterIn Q ≤ Q ⊓ centralizer (frattiniIn Q : Set G) ∧
      IsElementaryAbelian 2 (Z₂ ⧸ (center Q).subgroupOf Z₂) ∧
      (∀ x ∈ secondCenterIn Q, x^4=1) := by
  refine ⟨?_,?_,SecondCenterFrattini.second_quotient_elementary,?_⟩
  · exact (map_lt_map_iff_of_injective (f := Q.subtype) Q.subtype_injective).mpr
      (SecondCenterFrattini.center_lt_second hQ hna)
  · refine le_inf (map_subtype_le _) ?_
    rintro _ ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩
    exact congrArg Q.subtype (SecondCenterFrattini.second_le_frattini_centralizer hx y hy)
  · rintro _ ⟨x,hx,rfl⟩
    exact congrArg Q.subtype (SecondCenterFrattini.second_fourth_power ⟨x,hx⟩)

variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {R : Subgroup G} {n : ℕ}
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1<n)
include h hn
local instance natural_elementary : IsElementaryAbelian 2 (Multiplicative (Fin 3 → F)) := {
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change x.toAdd+x.toAdd=0
    exact funext (fun i => CharTwo.add_self_eq_zero (x.toAdd i))) }
local instance doubled_elementary :
    IsElementaryAbelian 2 (Multiplicative ((Fin 3 → F) × (Fin 3 → F))) := {
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change x.toAdd+x.toAdd=0
    exact Prod.ext (funext (fun i => CharTwo.add_self_eq_zero (x.toAdd.1 i)))
      (funext (fun i => CharTwo.add_self_eq_zero (x.toAdd.2 i)))) }

/-- Each recognized whole central omega supplies the actual upper pairing,
without a class-two or upper-section-model assumption. -/
theorem ms_natural_upper_pairing (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R))
      ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    IsElementaryAbelian 2 (center (msQ K R)) ∧
      HasCommutatorCoordinates K (msQ K R) (linearThreeActor e) (specialLinearNatural 3) := by
  exact exists_marked_pairing _ _ (CenterFourExclusion.center_natural h hn e hm)

/-- The doubled-center branch retains both target summands and the same full
quotient marking in its faithful upper pairing. -/
theorem ms_doubled_upper_pairing (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R))
      ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    IsElementaryAbelian 2 (center (msQ K R)) ∧
      HasCommutatorCoordinates K (msQ K R) (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  exact exists_marked_pairing _ _ (DoubledCenter.center_doubled h hn e hm)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections
