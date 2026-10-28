module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.InvariantSubgroups
public import Theory.GroupAction.FiveInvariantSupplement
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteLattice
public import Theory.SpecificGroups.ReeTwo.ParabolicResidualCoreObstruction

/-!
# Correct core alternatives in the Ree and Tits branches

In the actual full-Ree parabolic every normal subgroup between E and QH
is E, F, QH, or W = Ω₁(QH). Irreducibility identifies the quotient image;
uniqueness of invariant index-two supplements identifies the additional
case with the computed W. The source centralizer chain (*) supplies E ≤ Q
through the second center and excludes Q = E.

The full core is also not contained in the local two-residual: the imported
binary-character obstruction requires residual images in later quotients.

The additional W cannot be the two-core of an ambient group with
self-centralizing two-core. Its derived subgroup E is characteristic and
self-centralizing in W, so the ambient centralizer of E lies in the core.
This would put F in W, contradicting W ∩ F = E < F.

For the actual Tits core, its derived subgroup lies in its second center
by the literal embedding into the full-Ree core. Thus (*) and the computed
irreducible quotient give the two alternatives F and QH directly.
All quotients here use the intrinsic center of the specified core; a source
application must transport the marked Z and the chain (*) to this quotient.

These results repair the core stage of Aschbacher--Smith, Lemma 14.2.21,
printed pp.988--989. The ambient faithful action and final residual
contradiction remain separate steps. The concrete identities are proved in
ReeTwo.ParabolicConcrete from the verified root-and-Weyl model comparisons.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal

open Subgroup ReeTwo.ParabolicConcrete

private theorem ree_core_interval (Q : Subgroup Tits.ExceptionalParabolics.FullRee.first) [Q.Normal]
    (hQQ : Q ≤ reeQ) (hEQ : reeE ≤ Q) :
    Q = reeE ∨ Q = reeF ∨ Q = reeQ ∨
      ((Q.subgroupOf reeQ) ⊓ (reeF.subgroupOf reeQ) = reeE.subgroupOf reeQ ∧
        (Q.subgroupOf reeQ) ⊔ (reeF.subgroupOf reeQ) = ⊤ ∧
        (Q.subgroupOf reeQ).index = 2) := by
  let D : Subgroup reeQ := commutator reeQ
  let F : Subgroup reeQ := centralizer (D : Set reeQ)
  have hD : D = reeE.subgroupOf reeQ := by
    apply Subgroup.map_injective reeQ.subtype_injective
    rw [map_subtype_commutator, map_subgroupOf_eq_of_le (commutator_le_left _ _)]
  have hF : F = reeF.subgroupOf reeQ := reeV_denominator
  have hEF : D ≤ F := by
    rw [hD, hF]
    exact subgroupOf_mono _ (by rw [← reeW_inf_F]; exact inf_le_right)
  have hindex : D.relIndex F = 2 := by
    rw [hD, hF, relIndex_subgroupOf reeF_le_Q]
    have hc := (reeE.subgroupOf reeF).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show reeE ≤ reeF by rw [← reeW_inf_F]; exact inf_le_right)).toEquiv,
      reeE_card, reeF_card] at hc
    change reeE.relIndex reeF * 32 = 64 at hc
    omega
  have hact := Theory.GroupAction.normal_subgroup_quotient_invariant reeQ Q F
  have hc := Theory.GroupAction.invariant_subgroup_cases_of_index_two_layer
    D F (Q.subgroupOf reeQ) reeQuotientAction hact
    (hD ▸ subgroupOf_mono _ hEQ) hEF hindex ree_five_dvd_action reeV_card
  rcases hc with h | h | h | h
  · left
    have hm := congrArg (Subgroup.map reeQ.subtype) h
    simpa only [map_subgroupOf_eq_of_le hQQ, hD,
      map_subgroupOf_eq_of_le (commutator_le_left _ _)] using hm
  · right; left
    have hm := congrArg (Subgroup.map reeQ.subtype) h
    simpa only [map_subgroupOf_eq_of_le hQQ, hF,
      map_subgroupOf_eq_of_le reeF_le_Q] using hm
  · right; right; left
    have hm := congrArg (Subgroup.map reeQ.subtype) h
    simpa only [map_subgroupOf_eq_of_le hQQ, ← MonoidHom.range_eq_map, range_subtype] using hm
  · exact Or.inr (Or.inr (Or.inr (by simpa only [hD, hF] using h)))

/-- The four actual invariant candidates, retaining the intrinsic omega subgroup. -/
public theorem ree_invariant_core_cases (Q : Subgroup Tits.ExceptionalParabolics.FullRee.first) [Q.Normal]
    (hQQ : Q ≤ reeQ) (hEQ : reeE ≤ Q) :
    Q = reeE ∨ Q = reeF ∨ Q = reeQ ∨ Q = reeW := by
  rcases ree_core_interval Q hQQ hEQ with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · right; right; right
    let F : Subgroup reeQ := centralizer (commutator reeQ : Set reeQ)
    let := reeW_characteristic
    have hWQ := reeW_lt_Q.le
    have hWindex : (reeW.subgroupOf reeQ).index = 2 := by
      have hc := (reeW.subgroupOf reeQ).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hWQ).toEquiv,
        reeW_card, reeQ_card] at hc
      exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 512) hc
    have hinter : Q.subgroupOf reeQ ⊓ F = reeW.subgroupOf reeQ ⊓ F := by
      rw [show F = reeF.subgroupOf reeQ from reeV_denominator, h.1]
      exact (congrArg (fun S => S.subgroupOf reeQ) reeW_inf_F).symm
    have hsup : reeW.subgroupOf reeQ ⊔ F = ⊤ := by
      rw [show F = reeF.subgroupOf reeQ from reeV_denominator,
        ← subgroupOf_sup hWQ reeF_le_Q, reeW_sup_F, subgroupOf_self]
    have hI := Theory.GroupAction.normal_subgroup_quotient_invariant reeQ (Q ⊓ reeW) F
    have he := Theory.GroupAction.invariant_index_two_supplement_unique
      F (Q.subgroupOf reeQ) (reeW.subgroupOf reeQ) reeQuotientAction
      hI hinter hsup h.2.2 hWindex ree_five_dvd_action reeV_card
    have hm := congrArg (Subgroup.map reeQ.subtype) he
    simpa only [map_subgroupOf_eq_of_le hQQ, map_subgroupOf_eq_of_le hWQ] using hm

/-- The centralizer chain (*) supplies the lower bound and excludes the derived tail. -/
public theorem ree_core_cases_of_quotient_centralizer (Q : Subgroup Tits.ExceptionalParabolics.FullRee.first) [Q.Normal]
    (hQQ : Q ≤ reeQ)
    (hZQ : center reeQ ≤ Q.subgroupOf reeQ)
    (hself : centralizer ((Q.subgroupOf reeQ).map
        (QuotientGroup.mk' (center reeQ)) : Set (reeQ ⧸ center reeQ)) ≤
      (Q.subgroupOf reeQ).map (QuotientGroup.mk' (center reeQ))) :
    Q = reeF ∨ Q = reeQ ∨ Q = reeW := by
  have h2 := second_center_le_of_quotient_centralizer_le (Q.subgroupOf reeQ) hZQ hself
  have hEQ : reeE ≤ Q := by
    have hm := Subgroup.map_mono (f := reeQ.subtype) h2
    rwa [ree_second_center, map_subgroupOf_eq_of_le hQQ] at hm
  rcases ree_invariant_core_cases Q hQQ hEQ with h | h | h | h
  · subst Q
    have hFQ : reeF ≤ reeE := by
      have hh := le_of_centralizer_quotient_le (center reeQ) (reeE.subgroupOf reeQ)
        (reeF.subgroupOf reeQ) hZQ (by
          intro x hx y hy
          exact Subtype.ext (hx (y : _) hy)) hself
      have hm := Subgroup.map_mono (f := reeQ.subtype) hh
      rwa [map_subgroupOf_eq_of_le reeF_le_Q, map_subgroupOf_eq_of_le hQQ] at hm
    have hc := card_le_of_le hFQ
    rw [reeF_card, reeE_card] at hc
    omega
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem upper_center_comap_le {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (n : ℕ) :
    (Subgroup.upperCentralSeries B n).comap f ≤ Subgroup.upperCentralSeries A n := by
  induction n with
  | zero =>
    intro a ha
    apply (show a = 1 → a ∈ Subgroup.upperCentralSeries A 0 from id)
    apply hf
    simpa using ha
  | succ n ih =>
    intro a ha
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro b
    apply ih
    change f _ ∈ Subgroup.upperCentralSeries B n
    rw [map_commutatorElement]
    exact Subgroup.mem_upperCentralSeries_succ_iff.mp ha (f b)

/-- The literal Tits-to-Ree core embedding places the Tits derived subgroup in its second center. -/
public theorem tits_derived_le_second_center : commutator titsQ ≤
    Subgroup.upperCentralSeries titsQ 2 := by
  let i := Tits.ExceptionalParabolics.FirstQuotient.embedding
  let f : titsQ →* reeQ := (i.comp titsQ.subtype).codRestrict reeQ (by
    intro x
    apply reeW_lt_Q.le
    rw [← tits_core_image_eq_W]
    exact mem_map_of_mem _ x.property)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact Tits.ExceptionalParabolics.FirstQuotient.embedding_injective
      (congrArg Subtype.val h)
  have hD : (commutator titsQ).map f = reeE.subgroupOf reeQ := by
    apply Subgroup.map_injective reeQ.subtype_injective
    rw [Subgroup.map_map, map_subgroupOf_eq_of_le (commutator_le_left _ _)]
    change (commutator titsQ).map (i.comp titsQ.subtype) = reeE
    rw [← Subgroup.map_map, map_subtype_commutator]
    exact tits_derived_image
  have hE : reeE.subgroupOf reeQ = Subgroup.upperCentralSeries reeQ 2 := by
    apply Subgroup.map_injective reeQ.subtype_injective
    rw [map_subgroupOf_eq_of_le (commutator_le_left _ _), ree_second_center]
  intro x hx
  apply upper_center_comap_le f hf 2
  change f x ∈ Subgroup.upperCentralSeries reeQ 2
  rw [← hE, ← hD]
  exact mem_map_of_mem _ hx

/-- In the actual Tits core the chain (*) gives precisely the centralizer or the whole core. -/
public theorem tits_core_cases_of_quotient_centralizer (Q : Subgroup Tits.ExceptionalParabolics.first) [Q.Normal]
    (hQQ : Q ≤ titsQ)
    (hZQ : center titsQ ≤ Q.subgroupOf titsQ)
    (hself : centralizer ((Q.subgroupOf titsQ).map
        (QuotientGroup.mk' (center titsQ)) : Set (titsQ ⧸ center titsQ)) ≤
      (Q.subgroupOf titsQ).map (QuotientGroup.mk' (center titsQ))) :
    Q = titsF ∨ Q = titsQ := by
  have hEQ := tits_derived_le_second_center.trans
    (second_center_le_of_quotient_centralizer_le (Q.subgroupOf titsQ) hZQ hself)
  have hE : commutator titsQ = titsE.subgroupOf titsQ := by
    apply Subgroup.map_injective titsQ.subtype_injective
    rw [map_subtype_commutator, map_subgroupOf_eq_of_le (commutator_le_left _ _)]
  let F : Subgroup titsQ := centralizer (commutator titsQ : Set titsQ)
  have hF : F = titsE.subgroupOf titsQ := titsV_denominator.trans (congrArg
    (fun S => S.subgroupOf titsQ) titsF_eq_E)
  have hFQ : F ≤ Q.subgroupOf titsQ := by rwa [hF, ← hE]
  rcases invariant_subgroup_alternatives F (Q.subgroupOf titsQ) titsQuotientAction
    (Theory.GroupAction.normal_subgroup_quotient_invariant titsQ Q F)
    hFQ tits_five_dvd_action titsV_card with h | h
  · left
    have hm := congrArg (Subgroup.map titsQ.subtype) h
    simpa only [map_subgroupOf_eq_of_le hQQ,
      show F = titsF.subgroupOf titsQ from titsV_denominator,
      map_subgroupOf_eq_of_le titsF_le_Q] using hm
  · right
    have hm := congrArg (Subgroup.map titsQ.subtype) h
    simpa only [map_subgroupOf_eq_of_le hQQ, ← MonoidHom.range_eq_map, range_subtype] using hm

private theorem commutator_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (commutator A).map e.toMonoidHom = commutator B := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

private theorem self_centralizing_derived_transfer {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : centralizer (commutator A : Set A) ≤ commutator A) :
    centralizer (commutator B : Set B) ≤ commutator B := by
  intro b hb
  rw [← commutator_map_equiv e]
  refine ⟨e.symm b, h ?_, e.apply_symm_apply b⟩
  intro a ha
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    hb (e a) (commutator_map_equiv e ▸ mem_map_of_mem _ ha)

/-- The extra invariant subgroup cannot be a self-centralizing ambient two-core.
The characteristic and centralizer premises are supplied by the concrete model. -/
public theorem ree_omega_ne_ambient_core {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    (hcentral : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hW : reeW.map i = pCore 2 M) : False := by
  let e : reeW ≃* pCore 2 M :=
    (reeW.equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hW)
  have hderived : commutator reeW = reeE.subgroupOf reeW := by
    apply Subgroup.map_injective reeW.subtype_injective
    rw [map_subtype_commutator, reeW_commutator,
      map_subgroupOf_eq_of_le reeE_lt_W.le]
  have hself : centralizer (commutator (pCore 2 M) : Set (pCore 2 M)) ≤
      commutator (pCore 2 M) := by
    apply self_centralizing_derived_transfer e
    rw [hderived, reeW_centralizer_E]
  have hc := centralizer_le_pCore_of_characteristic_selfCentralizing 2 hcentral
    (commutator (pCore 2 M)) hself
  have hd : (commutator (pCore 2 M)).map (pCore 2 M).subtype = reeE.map i := by
    rw [map_subtype_commutator, ← hW, ← Subgroup.map_commutator, reeW_commutator]
  rw [hd] at hc
  have hF : reeF.map i ≤ pCore 2 M :=
    (map_centralizer_le_centralizer_image (reeE : Set _) i).trans hc
  rw [← hW] at hF
  have hFW : reeF ≤ reeW := (Subgroup.map_le_map_iff_of_injective hi).mp hF
  have he : reeF = reeE := by
    rw [← reeW_inf_F, inf_eq_right.mpr hFW]
  have hcard := reeF_card
  rw [he, reeE_card] at hcard
  omega


/-- Apply the corrected lattice and omega exclusion to the literal preimage of O₂(Mc).
The two central-quotient hypotheses are the restriction of the source chain (*). -/
public theorem ree_ambient_core_cases {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    (hcentral : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hQ : pCore 2 M ≤ reeQ.map i)
    (hZQ : center reeQ ≤ ((pCore 2 M).comap i).subgroupOf reeQ)
    (hself : centralizer ((((pCore 2 M).comap i).subgroupOf reeQ).map
        (QuotientGroup.mk' (center reeQ)) : Set (reeQ ⧸ center reeQ)) ≤
      (((pCore 2 M).comap i).subgroupOf reeQ).map (QuotientGroup.mk' (center reeQ))) :
    pCore 2 M = reeF.map i ∨ pCore 2 M = reeQ.map i := by
  have hpre : (pCore 2 M).comap i ≤ reeQ := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hQ hx
    exact hi he ▸ hy
  have hmap : ((pCore 2 M).comap i).map i = pCore 2 M := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr (hQ.trans (reeQ.map_le_range i))
  rcases ree_core_cases_of_quotient_centralizer _ hpre hZQ hself with h | h | h
  · exact Or.inl (hmap.symm.trans (congrArg (Subgroup.map i) h))
  · exact Or.inr (hmap.symm.trans (congrArg (Subgroup.map i) h))
  · exact (ree_omega_ne_ambient_core i hi hcentral
      ((congrArg (Subgroup.map i) h).symm.trans hmap)).elim

/-- The same preimage application for an embedded actual Tits parabolic. -/
public theorem tits_ambient_core_cases {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.first →* M) (hi : Function.Injective i)
    (hQ : pCore 2 M ≤ titsQ.map i)
    (hZQ : center titsQ ≤ ((pCore 2 M).comap i).subgroupOf titsQ)
    (hself : centralizer ((((pCore 2 M).comap i).subgroupOf titsQ).map
        (QuotientGroup.mk' (center titsQ)) : Set (titsQ ⧸ center titsQ)) ≤
      (((pCore 2 M).comap i).subgroupOf titsQ).map (QuotientGroup.mk' (center titsQ))) :
    pCore 2 M = titsF.map i ∨ pCore 2 M = titsQ.map i := by
  have hpre : (pCore 2 M).comap i ≤ titsQ := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hQ hx
    exact hi he ▸ hy
  have hmap : ((pCore 2 M).comap i).map i = pCore 2 M := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr (hQ.trans (titsQ.map_le_range i))
  rcases tits_core_cases_of_quotient_centralizer _ hpre hZQ hself with h | h
  · exact Or.inl (hmap.symm.trans (congrArg (Subgroup.map i) h))
  · exact Or.inr (hmap.symm.trans (congrArg (Subgroup.map i) h))

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal
