module
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupAction.InnerCentralizerCardinality
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.CubicOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OrdinaryLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InvolutionCentralizerOdd
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.SpecificGroups.Held.OrdinaryLocal
public import Theory.SpecificGroups.Held.ComponentFacts

/-!
# Cubic obstructions for Sylow-fixing sporadic automorphisms

The native J₂, HS, Held and Rudvalis involution centralizers have orders
indivisible by nine in the classes fixed by a full Sylow two-subgroup.
The actual outer two-groups preserve this divisibility obstruction in the
full automorphism centralizers. J₂ uses both native involution classes;
HS uses its exhaustive proper Sylow-overgroup calculation; Held uses
conjugacy of the unique Sylow-center involution to the marked max5 element.
Rudvalis inherits simplicity when applying its proved automorphism realization.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, Theorem C
inspection; GLS3 Table 5.3g,i,m,p,r. The imported native calculations retain
their ATLAS attribution. No group-family tag replaces a model equivalence.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer

private theorem not_nine_dvd_aut_centralizer_of_inner
    {B : Type*} [Group B] [Finite B] (hz : center B = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer B)) (x : B)
    (hc : ¬ 9 ∣ Nat.card (centralizer ({x} : Set B))) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut B))) := by
  intro h
  have hd := h.trans (MulAut.centralizer_conj_card_dvd hz x)
  obtain ⟨k,hk⟩ := ho.exists_card_eq
  have hcop : Nat.Coprime 9 (Nat.card (MulAut.Outer B)) := by
    rw [hk]
    exact (by decide : Nat.Coprime 9 2).pow_right k
  exact hc (hcop.dvd_of_dvd_mul_right hd)

namespace Rudvalis
/-- Inherited simplicity suffices for the full involution automorphism centralizer bound. -/
theorem not_nine_dvd_involution_aut_centralizer [IsSimpleGroup Model]
    (a : MulAut Model) (ha : orderOf a = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut Model))) := by
  obtain ⟨x,rfl⟩ := component_conj_surjective a
  have hx : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot LowCentralizers.model_center_eq_bot x).symm.trans ha
  exact not_nine_dvd_aut_centralizer_of_inner LowCentralizers.model_center_eq_bot
    outer_isPGroup_two x (InvolutionCentralizers.centralizer_not_nine x hx)
end Rudvalis

namespace Sporadic.LeechRelated.J2
open InnerInvolutionCores ExceptionalParabolics GeneratorPair
/-- Both actual J2 involution centralizers have order indivisible by nine. -/
theorem not_nine_dvd_involution_centralizer (x : Carrier) (hx : orderOf x = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({x} : Set Carrier)) := by
  rcases involution_fusion x hx with h|h
  · rw [← card_centralizer_eq_of_isConj _ _ h, Nat.card_congr a_centralizer_equiv.toEquiv,
      Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [E4,C2,Nat.card_fun,Nat.factorial]
  · rw [← card_centralizer_eq_of_isConj _ _ h]
    change ¬ 9 ∣ Nat.card Seed.l₁
    rw [FirstParabolic.card_l₁]
    decide

/-- Sylow-fixing selects innerness in J2, retaining its actual outer two-group. -/
theorem not_nine_dvd_sylow_fixer_centralizer
    (P : Sylow 2 Carrier) (a : MulAut Carrier) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut Carrier))) := by
  obtain ⟨x,rfl⟩ := automorphism_inner_of_fixes_sylow P a hP
  have hx : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot OrdinaryLocal.center_eq_bot x).symm.trans ha
  exact not_nine_dvd_aut_centralizer_of_inner OrdinaryLocal.center_eq_bot
    outer_isTwoGroup x (not_nine_dvd_involution_centralizer x hx)
end Sporadic.LeechRelated.J2

namespace Sporadic.LeechRelated.HS
/-- The proper full-Sylow centralizer and outer order two exclude nine in HS. -/
theorem not_nine_dvd_sylow_fixer_centralizer
    (P : Sylow 2 Carrier) (a : MulAut Carrier) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut Carrier))) := by
  obtain ⟨x,hx,ho,he⟩ := MulAut.inner_involution_fixing_sylow_center
    BlockNormalizer.center_carrier_eq_bot P a ha
    (OrdinaryLocal.automorphism_inner_of_fixes_sylow P a hP) hP
  have hc : TwoCentral (x : Carrier) := ⟨P,x.property,hx⟩
  have hmax := OrdinaryLocal.twoCentral_centralizer_isCoatom x ho hc
  have hPC : (P : Subgroup Carrier) ≤ centralizer ({(x : Carrier)} : Set Carrier) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hx (⟨y,hy⟩ : P)))
  have hnot := SylowOvergroups.proper_overgroup_not_nine_dvd P _ hPC hmax.1
  rw [he]
  exact not_nine_dvd_aut_centralizer_of_inner BlockNormalizer.center_carrier_eq_bot
    (IsPGroup.of_card_dvd_pow (n := 1) (by simpa only [pow_one] using outer_card_dvd_two)) x hnot
end Sporadic.LeechRelated.HS

namespace Held
open TwoLocalCandidates
/-- The literal centralizer of a Sylow-central Held involution has order 21504. -/
theorem twoCentral_centralizer_card (t : He) (ht : orderOf t = 2)
    (hc : TwoCentral t) : Nat.card (centralizer ({t} : Set He)) = 21504 := by
  let z : He := max5First ^ 4
  obtain ⟨R,hR⟩ := RankOneLocalPair.exists_sylow_le_max5
  have hzC : z ∈ centralizer (R : Set He) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (CentralInvolutionBounds.max5_le_centralizer (hR hx))
  have hzR : z ∈ R := by
    have hh := centralizer_le_normalizer (R : Set He) hzC
    rwa [LocalPairs.SylowGeometry.Calculations.inner_self_normalizing R] at hh
  have hz : TwoCentral z := ⟨R,hzR,mem_center_iff.mpr (fun x => Subtype.ext (hzC x x.property))⟩
  have hconj := hc.isConj_of_center_card_two hz
    (by intro he; rw [he,orderOf_one] at ht; omega)
    (by intro he; have ho := CentralInvolutionBounds.orderOf_centralInvolution
        change orderOf z = 2 at ho
        rw [he,orderOf_one] at ho
        omega)
    LocalPairs.SylowGeometry.Calculations.inner_center_card
  rw [card_centralizer_eq_of_isConj _ _ hconj]
  change Nat.card (centralizer ({max5First ^ 4} : Set He)) = 21504
  rw [InvolutionFixedData.TwoB.centralizer_eq_max5,InvolutionFixedData.TwoB.max5_card]

/-- The marked Held involution also has full automorphism centralizer indivisible by nine. -/
theorem not_nine_dvd_sylow_fixer_centralizer
    (P : Sylow 2 He) (a : MulAut He) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut He))) := by
  obtain ⟨t,ht⟩ := LocalPairs.SylowPointwise.isInner_of_fixes_sylow
    Realization.normalizer_surjective P a hP
  obtain ⟨x,hx,ho,he⟩ := MulAut.inner_involution_fixing_sylow_center
    LocalPairs.center_eq_bot P a ha ⟨t,ht.symm⟩ hP
  have hc : TwoCentral (x : He) := ⟨P,x.property,hx⟩
  rw [he]
  exact not_nine_dvd_aut_centralizer_of_inner LocalPairs.center_eq_bot outer_isPGroup_two x
    (by rw [twoCentral_centralizer_card x ho hc]; decide)
end Held
