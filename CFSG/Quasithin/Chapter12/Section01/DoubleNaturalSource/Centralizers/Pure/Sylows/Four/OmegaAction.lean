module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.CaseFour
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import Theory.GroupTheory.PResidual.CentralizerCorrection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input

/-!
# The omega-center action in the dimension-four pure-point argument

In source case (4), the commutators of the Sylow omega-center with the
point residual can be corrected inside the natural central layer. Odd
Sylow index averaging constructs those corrections. The natural fixed
line has at most two elements, and uniqueness of correction gives an
actual homomorphism whose kernel is the residual centralizer. Thus that
centralizer has index at most two. MS3 rules out index one.

The source application supplies every local input from the original
chosen module and a contrary ambient Sylow enlargement. Its only earlier
classification premise is the exact binary C.1.34 implication, owned by
`qt-rank-two-ms93`. The remaining Sylow contradiction and full pure-point
assembly stay with `qt-d-double-natural-pure-fusion`, under the final parent
`qt-d-double-natural-centralizers`.
Source: Aschbacher--Smith, 12.1.4, printed p.790, and C.1.34(4), p.137.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "msCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
local notation "msOmega" => Subgroup.omegaCenterIn
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem natural_section_fixed_card {L U : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hm : HasSectionModel L U ⊥ (linearThreeActor e)
      (specialLinearNatural (k := ZMod 2) 3)) (P : Sylow 2 L) :
    IsElementaryAbelian 2 U ∧
      Nat.card (U ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G) : Subgroup G) ≤ 2 := by
  simp only [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,φ,hφ⟩ := hm
  let := hn
  let f : U ≃* Multiplicative (Fin 3 → ZMod 2) := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (show (⊥ : Subgroup U) = (⊥ : Subgroup G).subgroupOf U by rw [bot_subgroupOf])).trans φ)
  have hf : ∀ (l : L) (u u' : U), (u' : G) = l * (u : G) * (l : G)⁻¹ →
      (f u').toAdd = specialLinearNatural 3 (linearThreeActor e l) (f u).toAdd := hφ
  let : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro v
      apply Multiplicative.toAdd.injective
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      ext i
      exact CharTwo.add_self_eq_zero _)⟩
  have hel : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    f.toMonoidHom f.injective
  refine ⟨hel,?_⟩
  let a := linearThreeActor e
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let PS := P.mapSurjective (f := a) ha
  let C := U ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G)
  let g : C → fixedSpace BinaryLinearThree.W (PS : Subgroup BinaryLinearThree.Group) :=
    fun u => ⟨(f ⟨u,u.property.1⟩).toAdd,by
      intro p
      have hp : (p : BinaryLinearThree.Group) ∈ (P : Subgroup L).map a := p.property
      obtain ⟨l,hl,heq⟩ := hp
      change BinaryLinearThree.W (p : BinaryLinearThree.Group) _ = _
      rw [←heq]
      exact (hf l ⟨u,u.property.1⟩ ⟨u,u.property.1⟩ (by
        rw [u.property.2 l (mem_map_of_mem L.subtype hl),mul_inv_cancel_right])).symm⟩
  have hg : Function.Injective g := by
    intro u v h
    have he := f.injective (Multiplicative.toAdd.injective (congrArg Subtype.val h))
    exact Subtype.ext (congrArg (fun x : U => (x : G)) he)
  exact (Nat.card_le_card_of_injective g hg).trans
    (BinaryLinearThree.card_sylow_natural_fixed_le_two PS)


private theorem corrections_index_bound (A U F Z : Subgroup G)
    (hUA : U ≤ A) (hFU : F ≤ U)
    (hfree : U ⊓ centralizer (A : Set G) = ⊥)
    (hsplit : ∀ z ∈ Z, ∃ q ∈ F, q⁻¹ * z ∈ centralizer (A : Set G)) :
    (centralizer (A : Set G)).relIndex Z ≤ Nat.card F := by
  classical
  let q (z : Z) : F := ⟨(hsplit z z.property).choose,(hsplit z z.property).choose_spec.1⟩
  have hq (z : Z) : (q z : G)⁻¹ * z ∈ centralizer (A : Set G) :=
    (hsplit z z.property).choose_spec.2
  have huniq (z : Z) (v : F) (hv : (v : G)⁻¹ * z ∈ centralizer (A : Set G)) :
      q z = v := by
    have hc : (q z : G)⁻¹ * v ∈ centralizer (A : Set G) := by
      have hh := (centralizer (A : Set G)).mul_mem (hq z)
        ((centralizer (A : Set G)).inv_mem hv)
      convert hh using 1; group
    have he : (q z : G)⁻¹ * v = 1 := by
      apply show (q z : G)⁻¹ * v ∈ (⊥ : Subgroup G) → (q z : G)⁻¹ * v = 1 from id
      rw [←hfree]
      exact ⟨U.mul_mem (U.inv_mem (hFU (q z).property)) (hFU v.property),hc⟩
    exact Subtype.ext (inv_mul_eq_one.mp he)
  let f : Z →* F := {
    toFun := q
    map_one' := huniq 1 1 (by simp)
    map_mul' := by
      intro x y
      apply huniq
      have hx := hq x
      have hy := hq y
      have hc := hx (q y) (hUA (hFU (q y).property))
      have hh := (centralizer (A : Set G)).mul_mem hx hy
      convert hh using 1
      change ((q x : G) * q y)⁻¹ * ((x : G) * y) =
        ((q x : G)⁻¹ * x) * ((q y : G)⁻¹ * y)
      have hc' := (Commute.inv_left hc).eq
      calc
        _ = (q y : G)⁻¹ * (((q x : G)⁻¹ * x) * y) := by group
        _ = ((q x : G)⁻¹ * x) * ((q y : G)⁻¹ * y) := by rw [←mul_assoc,hc',mul_assoc] }
  have hk : f.ker = (centralizer (A : Set G)).subgroupOf Z := by
    ext z
    change q z = 1 ↔ (z : G) ∈ centralizer (A : Set G)
    constructor
    · intro hz
      simpa only [hz,OneMemClass.coe_one,inv_one,one_mul] using hq z
    · intro hz
      exact huniq z 1 (by simpa using hz)
  rw [relIndex,←hk,index_ker]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- The actual case-(4) omega center moves by at most one binary dimension. -/
theorem pureFourMS_omega_index_le_two
    {κ : GroupClass.{u}} {X R : Subgroup G}
    (hms : SmallMSPair κ X R)
    (hR : Chapter1.IsSylowIn 2 R (X ⊔ R))
    (e : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hl : PureFourMSLayeredAlternative X R e) :
    (centralizer (X : Set G)).relIndex (msOmega R) ≤ 2 := by
  let J := X ⊔ R
  let N := J.pCoreIn 2
  let Q := msQ X R
  let U := ⁅msCenter Q,X⁆
  have hm : HasSectionModel X U ⊥ (linearThreeActor e)
      (specialLinearNatural (k := ZMod 2) 3) := hl.2.2.2.2.2.1
  let A := X.subgroupOf J
  let a : A ≃* X := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect A := hms.component.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  have hpX : IsPPerfect 2 X := by
    intro B hn ht
    let := hn
    let := ht.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ B)
  obtain ⟨R0,hR0⟩ := hR
  have hRJ : R ≤ J := hR0 ▸ map_subtype_le (R0 : Subgroup J)
  have hNR : N ≤ R := (pCoreIn_le_sylow J R0).trans_eq hR0
  obtain ⟨P0,hP0⟩ := R0.exists_subgroupOf_eq_of_subnormal A hms.component.subnormal
  let P : Sylow 2 X := P0.mapSurjective (f := a.toMonoidHom) a.surjective
  have hPR : (P : Subgroup X).map X.subtype ≤ R := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨b,hb,rfl⟩ := hx
    have hbR : (b : J) ∈ R0 := by rw [hP0] at hb; exact hb
    exact hR0 ▸ mem_map_of_mem J.subtype hbR
  obtain ⟨he,hcard⟩ := natural_section_fixed_card e hm P
  let := he
  have hXN : X ≤ normalizer (N : Set G) :=
    (show X ≤ J from le_sup_left).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hQN : Q ≤ N := le_normalizer_iff_commutator_le_left.mp hXN
  have hXQ : X ≤ normalizer (Q : Set G) := normalizer_commutator_ge_right N X
  have hXZ : X ≤ normalizer (msCenter Q : Set G) :=
    hXQ.trans (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hUZ : U ≤ msCenter Q := le_normalizer_iff_commutator_le_left.mp hXZ
  have hUX : U ≤ X := by
    have hQX : Q ≤ X := by
      have hnorm := (hms.binaryInput e).component_normal
      have hn : J ≤ normalizer (X : Set G) := by
        apply (normal_subgroupOf_iff_le_normalizer (show X ≤ J from le_sup_left)).mp
        exact hnorm
      exact le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 J).trans hn)
    exact hUZ.trans ((map_subtype_le _).trans hQX)
  have hfree : U ⊓ centralizer (X : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxC : x ∈ Q ⊓ centralizer (X : Set G) :=
      ⟨(hUZ.trans (map_subtype_le _)) hx.1,hx.2⟩
    exact (show (Q ⊓ centralizer (X : Set G)) ⊓ U = ⊥ from hl.2.2.2.2.1) ▸ ⟨hxC,hx.1⟩
  apply (corrections_index_bound X U
    (U ⊓ centralizer ((P : Subgroup X).map X.subtype : Set G))
    (msOmega R) hUX inf_le_left hfree ?_).trans hcard
  intro z hz
  obtain ⟨hzR,hzC,_⟩ := (mem_omegaCenterIn_iff R z).mp hz
  have hzN : z ∈ N := by
    have hc : (⟨z,hRJ hzR⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro k hk
      exact Subtype.ext (hzC k (hNR (mem_map_of_mem J.subtype hk)))
    exact mem_map_of_mem J.subtype ((hms.binaryInput e).core_selfCentralizing hc)
  exact fixed_correction_of_center_commutator X N U hpX
    (isPGroup_pCoreIn 2 J) hXN hm.2.1
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) le_rfl P z
    hzN (centralizer_le (hQN.trans hNR) hzC) (centralizer_le hPR hzC)


open Chapter12.Section01.DoubleNaturalSource
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The source rank and exact action index at the original marked point,
conditional only on the complete binary C.1.34 implication. -/
theorem doubleNatural_four_pure_omega_index_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4)
    (classification : BinaryLinearThreeMSClassification KnownSimple.IsKnownSimple.{u}) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      4 < Nat.card (msOmega (B.pointSylow w)) ∧
        (centralizer (B.pointResidual w : Set G)).relIndex (msOmega (B.pointSylow w)) = 2 := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  obtain ⟨hms,_,hs⟩ := D.doubleNatural_four_pure_smallMSPair_of_many h hmany B S w hw hp hfix hf
  obtain ⟨e,hl,hcard⟩ := D.doubleNatural_four_pure_layered_ms_of_many h hmany B classification S w hw hp hfix hf
  have hi := pureFourMS_omega_index_le_two hms hs e hl
  refine ⟨hcard,?_⟩
  have hpos : (centralizer (B.pointResidual w : Set G)).relIndex
      (msOmega (B.pointSylow w)) ≠ 0 := index_ne_zero_of_finite
  have hne : (centralizer (B.pointResidual w : Set G)).relIndex
      (msOmega (B.pointSylow w)) ≠ 1 := by
    intro he
    have hc := relIndex_eq_one.mp he
    apply omegaCenter_not_central hms.characteristic (by omega) ?_
    intro z hz
    obtain ⟨hzR,hzC,_⟩ := (mem_omegaCenterIn_iff (B.pointSylow w) z).mp hz
    have hj : z ∈ B.pointResidual w ⊔ B.pointSylow w := mem_sup_right hzR
    refine ⟨⟨z,hj⟩,mem_center_iff.mpr ?_,rfl⟩
    intro a
    apply Subtype.ext
    have hcentral : B.pointResidual w ⊔ B.pointSylow w ≤ centralizer ({z} : Set G) := by
      refine sup_le ?_ ?_
      · intro x hx
        exact mem_centralizer_singleton_iff.mpr (hc hz x hx)
      · intro r hr
        exact mem_centralizer_singleton_iff.mpr (hzC r hr)
    exact mem_centralizer_singleton_iff.mp (hcentral a.property)
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
