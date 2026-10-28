module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Transport
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Normalizer
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry

/-!
# The two largest local pairs in the A₆ shadow

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 2.5.12(3) and 2.5.23, printed pp.557–558 and 567–568.

The earlier correspondence is kept as an explicit source input.  Everything
after that input is derived from the actual local-pair definition, the
compatible action, and the checked Sylow geometry of `Aut(A₆)`.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

namespace EarlierSetup

variable (d : EarlierSetup κ G)

/- The source map in Lemma 2.5.12(3). -/
@[expose] noncomputable def normalizerPair (E : Subgroup G) : Subgroup G × Subgroup G :=
  (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G))

theorem normalizerPair_eq (E : Subgroup G) :
    d.normalizerPair E =
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) := rfl

def fourSubgroups : Set (Subgroup G) :=
  {E | E ≤ d.S ⊓ d.K ∧ IsKleinFour E}

def restrictedLargestPairs : Set (Subgroup G × Subgroup G) :=
  {P | P ∈ largestLocalPairs d.M d.H ∧ P.1 ≤ d.S}

/-- The exact earlier-source bijection 2.5.12(3), supplied by the section
assembly.  The present file proves all consequences of this input. -/
abbrev EarlierPairCorrespondence : Prop :=
  Set.BijOn d.normalizerPair d.fourSubgroups d.restrictedLargestPairs

theorem h_le_s_of_largest_pair {U L : Subgroup G}
    (hUL : (U, L) ∈ largestLocalPairs d.M d.H) : U ≤ d.S := by
  have hUbeta : U ∈ beta d.M := hUL.1.1.1
  have hULe : U ≤ L := hUL.1.1.2.2.2.1
  have hLH : L ≤ d.H := hUL.1.2
  have hUH : U ≤ d.H := hULe.trans hLH
  have hUM : U ≤ d.M := hUbeta.2.1
  let _ : (d.K.subgroupOf d.H).Normal := d.normalK
  intro u hu
  let uh : d.H := ⟨u, hUH hu⟩
  have hdecomp : ∃ k : d.K, ∃ s : d.S, (k : G) * s = u := by
    have htop : d.K.subgroupOf d.H ⊔ d.S.subgroupOf d.H = ⊤ := by
      rw [← subgroupOf_sup d.k_le_h d.s_le_h, d.generated, subgroupOf_self]
    have hu' : uh ∈ (d.K.subgroupOf d.H) ⊔ (d.S.subgroupOf d.H) :=
      htop ▸ mem_top uh
    obtain ⟨k, hk, s, hs, hks⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := d.K.subgroupOf d.H)
        (t := d.S.subgroupOf d.H) (x := uh)).mp hu'
    exact ⟨⟨k, hk⟩, ⟨s, hs⟩, by exact congrArg Subtype.val hks⟩
  obtain ⟨k, s, hks⟩ := hdecomp
  have hsM : (s : G) ∈ d.M := (d.s_le_t.trans d.t_le_m) s.property
  have hkM : (k : G) ∈ d.M := by
    have h := d.M.mul_mem (hUM hu) (d.M.inv_mem hsM)
    rw [← hks] at h
    simpa [mul_assoc] using h
  have hkKM : (k : G) ∈ d.K ⊓ d.M := ⟨k.property, hkM⟩
  have hkSK : (k : G) ∈ d.S ⊓ d.K := by
    rw [← d.intersection_m]
    exact hkKM
  rw [← hks]
  exact d.S.mul_mem hkSK.1 s.property

theorem sylow_of_largest_pair {U L : Subgroup G}
    (hUL : (U, L) ∈ largestLocalPairs d.M d.H) :
    ∃ P : Sylow 2 L,
      (P : Subgroup L).map L.subtype = U := by
  rcases hUL with ⟨⟨hlocal, hLH⟩, hmax⟩
  rcases hlocal with ⟨hUβ, hLE, hcore, hULe, hnot⟩
  obtain ⟨P, hUP, hPβ⟩ := beta_exists_sylow hUβ hULe
  let U' : Subgroup G := (P : Subgroup L).map L.subtype
  have hU'L : U' ≤ L := by
    exact (map_le_range _ _).trans_eq L.range_subtype
  have hpair : (U', L) ∈ localPairs (Chapter1.He G) d.M :=
    ⟨hPβ, hLE, hcore, hU'L, hnot⟩
  have hcard : Nat.card U' ≤ Nat.card U := hmax U' ⟨L, hpair⟩
  have heq : U' = U := (eq_of_le_of_card_ge hUP hcard).symm
  exact ⟨P, heq⟩

theorem normalizer_sylow_of_largest_pair {U L : Subgroup G}
    (hUL : (U, L) ∈ largestLocalPairs d.M d.H) :
    ∃ P : Sylow 2 L,
      (P : Subgroup L).map L.subtype = U :=
  d.sylow_of_largest_pair hUL

@[expose] noncomputable def skActionP : (d.S ⊓ d.K : Subgroup G) →* d.imageSylow :=
  d.skAction.codRestrict (d.imageSylow : Subgroup AutA6)
    (fun k => by
      rw [d.imageSylow_eq_range]
      exact ⟨⟨k, k.property.1⟩, rfl⟩)

theorem skAction_injective : Function.Injective d.skAction := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  change d.sylowAction ⟨a, a.property.1⟩ = 1 at ha
  have hker : (⟨a, a.property.1⟩ : d.S) ∈ d.sylowAction.ker := ha
  rw [d.sylowAction_kernel] at hker
  change (a : G) ∈ d.SC at hker
  exact Subtype.ext (disjoint_def.mp d.disjoint_k_sc a.property.2 hker)

theorem skActionP_injective : Function.Injective d.skActionP := by
  intro a b hab
  have hab' : d.skAction a = d.skAction b := by
    exact congrArg Subtype.val hab
  exact d.skAction_injective hab'

theorem skActionP_range : d.skActionP.range =
    sylowInner d.imageSylow := by
  ext a
  constructor
  · rintro ⟨k, rfl⟩
    change d.skAction k ∈ AlternatingSix.ShadowLocal.inner
    have hk : d.skAction k ∈ d.skAction.range := ⟨k, rfl⟩
    rw [d.skAction_range] at hk
    exact hk.2
  · intro ha
    have ha' : (a : AutA6) ∈
        (d.imageSylow : Subgroup AutA6) ⊓ inner := ⟨a.property, ha⟩
    rw [← d.skAction_range] at ha'
    obtain ⟨k, hk⟩ := ha'
    exact ⟨k, by
      apply Subtype.ext
      change d.skAction k = (a : AutA6)
      exact hk⟩

private theorem kleinZero_range (d : EarlierSetup κ G) :
    SylowGeometry.kleinZero d.imageSylow ≤ d.skActionP.range := by
  rw [d.skActionP_range]
  exact SylowGeometry.kleinZero_le_inner d.imageSylow

private theorem kleinOne_range (d : EarlierSetup κ G) :
    SylowGeometry.kleinOne d.imageSylow ≤ d.skActionP.range := by
  rw [d.skActionP_range]
  exact SylowGeometry.kleinOne_le_inner d.imageSylow

noncomputable def kleinZeroD : Subgroup (d.S ⊓ d.K : Subgroup G) :=
  (SylowGeometry.kleinZero d.imageSylow).comap d.skActionP

noncomputable def kleinOneD : Subgroup (d.S ⊓ d.K : Subgroup G) :=
  (SylowGeometry.kleinOne d.imageSylow).comap d.skActionP

noncomputable def kleinZeroAmbient : Subgroup G :=
  d.kleinZeroD.map (d.S ⊓ d.K : Subgroup G).subtype

noncomputable def kleinOneAmbient : Subgroup G :=
  d.kleinOneD.map (d.S ⊓ d.K : Subgroup G).subtype

noncomputable abbrev E1 : Subgroup G := d.kleinZeroAmbient

noncomputable abbrev E2 : Subgroup G := d.kleinOneAmbient

private theorem map_kleinZeroD :
    d.kleinZeroD.map d.skActionP = SylowGeometry.kleinZero d.imageSylow := by
  exact map_comap_eq_self (d.kleinZero_range)

private theorem map_kleinOneD :
    d.kleinOneD.map d.skActionP = SylowGeometry.kleinOne d.imageSylow := by
  exact map_comap_eq_self (d.kleinOne_range)

private theorem kleinZeroD_isKleinFour : IsKleinFour d.kleinZeroD := by
  let e := (d.kleinZeroD.equivMapOfInjective d.skActionP d.skActionP_injective).trans
    (MulEquiv.subgroupCongr d.map_kleinZeroD)
  exact {
    card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two }

private theorem kleinOneD_isKleinFour : IsKleinFour d.kleinOneD := by
  let e := (d.kleinOneD.equivMapOfInjective d.skActionP d.skActionP_injective).trans
    (MulEquiv.subgroupCongr d.map_kleinOneD)
  exact {
    card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two }

theorem kleinZeroAmbient_le : d.kleinZeroAmbient ≤ d.S ⊓ d.K := by
  change d.kleinZeroD.map (d.S ⊓ d.K : Subgroup G).subtype ≤ d.S ⊓ d.K
  exact map_subtype_le _

theorem kleinOneAmbient_le : d.kleinOneAmbient ≤ d.S ⊓ d.K := by
  change d.kleinOneD.map (d.S ⊓ d.K : Subgroup G).subtype ≤ d.S ⊓ d.K
  exact map_subtype_le _

theorem kleinZeroAmbient_isKleinFour : IsKleinFour d.kleinZeroAmbient := by
  let e := d.kleinZeroD.equivMapOfInjective (d.S ⊓ d.K).subtype
    (d.S ⊓ d.K).subtype_injective
  have hfour := d.kleinZeroD_isKleinFour
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans hfour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans hfour.exponent_two }

theorem kleinOneAmbient_isKleinFour : IsKleinFour d.kleinOneAmbient := by
  let e := d.kleinOneD.equivMapOfInjective (d.S ⊓ d.K).subtype
    (d.S ⊓ d.K).subtype_injective
  have hfour := d.kleinOneD_isKleinFour
  exact {
    card_four := (Nat.card_congr e.toEquiv).symm.trans hfour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans hfour.exponent_two }

theorem kleinZeroAmbient_ne_kleinOneAmbient :
    d.kleinZeroAmbient ≠ d.kleinOneAmbient := by
  intro h
  have hD : d.kleinZeroD = d.kleinOneD := by
    apply (Subgroup.map_injective (d.S ⊓ d.K).subtype_injective)
    simpa [kleinZeroAmbient, kleinOneAmbient] using h
  have hP := congrArg (Subgroup.map d.skActionP) hD
  rw [d.map_kleinZeroD, d.map_kleinOneD] at hP
  exact SylowGeometry.kleinZero_ne_kleinOne d.imageSylow hP

theorem normalizerPair_largest
    (hcor : d.EarlierPairCorrespondence)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (hfour : IsKleinFour E) :
    d.normalizerPair E ∈ largestLocalPairs d.M d.H := by
  have h := hcor.mapsTo (show E ∈ d.fourSubgroups from ⟨hE, hfour⟩)
  exact h.1

theorem four_subgroup_eq_marked (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K)
    (hfour : IsKleinFour E) :
    E = d.kleinZeroAmbient ∨ E = d.kleinOneAmbient := by
  let ED : Subgroup (d.S ⊓ d.K : Subgroup G) := E.subgroupOf (d.S ⊓ d.K)
  let eE := subgroupOfEquivOfLe hE
  let _ : IsKleinFour ED := {
    card_four := (Nat.card_congr eE.toEquiv).trans hfour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans hfour.exponent_two }
  let EP : Subgroup d.imageSylow := ED.map d.skActionP
  let _ : IsKleinFour EP := {
    card_four := (Nat.card_congr
      (ED.equivMapOfInjective d.skActionP d.skActionP_injective).toEquiv).symm.trans
      IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv
      (ED.equivMapOfInjective d.skActionP d.skActionP_injective)).symm.trans
      IsKleinFour.exponent_two }
  have hEPinner : EP ≤ sylowInner d.imageSylow := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := ha
    have hr : d.skActionP k ∈ d.skActionP.range := ⟨k, rfl⟩
    rw [d.skActionP_range] at hr
    exact hr
  rcases SylowGeometry.kleinFour_subgroups_inner d.imageSylow EP hEPinner with h0 | h1
  · left
    have hED : ED = d.kleinZeroD := by
      calc
        ED = (EP.comap d.skActionP) :=
          (comap_map_eq_self_of_injective d.skActionP_injective ED).symm
        _ = (SylowGeometry.kleinZero d.imageSylow).comap d.skActionP := by rw [h0]
        _ = d.kleinZeroD := rfl
    calc
      E = ED.map (d.S ⊓ d.K : Subgroup G).subtype :=
        (map_subgroupOf_eq_of_le hE).symm
      _ = d.kleinZeroAmbient := by simp [hED, kleinZeroAmbient]
  · right
    have hED : ED = d.kleinOneD := by
      calc
        ED = (EP.comap d.skActionP) :=
          (comap_map_eq_self_of_injective d.skActionP_injective ED).symm
        _ = (SylowGeometry.kleinOne d.imageSylow).comap d.skActionP := by rw [h1]
        _ = d.kleinOneD := rfl
    calc
      E = ED.map (d.S ⊓ d.K : Subgroup G).subtype :=
        (map_subgroupOf_eq_of_le hE).symm
      _ = d.kleinOneAmbient := by simp [hED, kleinOneAmbient]

theorem largest_pair_classification
    (hcor : d.EarlierPairCorrespondence) (P : Subgroup G × Subgroup G) :
    P ∈ largestLocalPairs d.M d.H ↔
      P = d.normalizerPair d.kleinZeroAmbient ∨
      P = d.normalizerPair d.kleinOneAmbient := by
  constructor
  · intro hP
    have hPS : P.1 ≤ d.S := d.h_le_s_of_largest_pair hP
    obtain ⟨E, hE, hEP⟩ := hcor.surjOn ⟨hP, hPS⟩
    rcases hE with ⟨hEbound, hfour⟩
    rcases d.four_subgroup_eq_marked E hEbound hfour with h0 | h1
    · left
      exact hEP.symm.trans (congrArg d.normalizerPair h0)
    · right
      exact hEP.symm.trans (congrArg d.normalizerPair h1)
  · rintro (rfl | rfl)
    · exact (d.normalizerPair_largest hcor d.kleinZeroAmbient
        d.kleinZeroAmbient_le d.kleinZeroAmbient_isKleinFour)
    · exact (d.normalizerPair_largest hcor d.kleinOneAmbient
        d.kleinOneAmbient_le d.kleinOneAmbient_isKleinFour)

theorem largestPairs
    (hcor : d.EarlierPairCorrespondence)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (hfour : IsKleinFour E) :
    d.normalizerPair E ∈ localPairs (Chapter1.He G) d.M ∧
      ∀ W ∈ localBases (Chapter1.He G) d.M,
        Nat.card W ≤ Nat.card (d.normalizerPair E).1 := by
  have h := d.normalizerPair_largest hcor E hE hfour
  exact ⟨h.1.1, h.2⟩

theorem normalizerSylow
    (hcor : d.EarlierPairCorrespondence)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (hfour : IsKleinFour E) :
    ∃ P : Sylow 2 (d.H ⊓ normalizer (E : Set G) : Subgroup G),
      (P : Subgroup (d.H ⊓ normalizer (E : Set G) : Subgroup G)).map
        (d.H ⊓ normalizer (E : Set G)).subtype =
        d.S ⊓ normalizer (E : Set G) := by
  obtain ⟨P, hP⟩ := d.sylow_of_largest_pair
    (d.normalizerPair_largest hcor E hE hfour)
  exact ⟨P, by simpa [normalizerPair] using hP⟩

theorem fourSubgroups_eq_two
    :
    d.fourSubgroups = {d.kleinZeroAmbient, d.kleinOneAmbient} := by
  ext E
  constructor
  · intro hE
    rcases d.four_subgroup_eq_marked E hE.1 hE.2 with h0 | h1
    · exact Set.mem_insert_iff.mpr (Or.inl h0)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h1))
  · intro hE
    rcases Set.mem_insert_iff.mp hE with h0 | h1
    · rw [h0]
      exact ⟨d.kleinZeroAmbient_le, d.kleinZeroAmbient_isKleinFour⟩
    · rw [Set.mem_singleton_iff.mp h1]
      exact ⟨d.kleinOneAmbient_le, d.kleinOneAmbient_isKleinFour⟩

theorem largestLocalPairs_eq_two
    (hcor : d.EarlierPairCorrespondence) :
    largestLocalPairs d.M d.H =
      {P | P = d.normalizerPair d.kleinZeroAmbient ∨
        P = d.normalizerPair d.kleinOneAmbient} := by
  ext P
  exact d.largest_pair_classification hcor P

end EarlierSetup
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
