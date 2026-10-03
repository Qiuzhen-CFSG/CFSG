module
public import Stellmacher.SectionTwo.RelativeBaumannActionInputs
public import Stellmacher.SectionTwo.BaumannFactorActionData
public import Stellmacher.SectionTwo.QuotientModuleTransport
public import Stellmacher.SectionOne.OneARelativeM
public import Theory.GroupTheory.WeakClosureQuotient
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Stellmacher.DirectProductMap
public import Stellmacher.SectionOne.WeaklyClosedOffenderBaumannProduct
public import Theory.GroupTheory.NormalClosureSupplement
public import Stellmacher.BaumannNormalizer
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Baumann factor decomposition through a normal supplement

Keep the original Section Two module V=⟨Ω₁(Z(S))^G⟩. Let N be a normal
supplement to S, and let Q be a Sylow subgroup of N whose ambient image is
normalized by S and contains V. The image of the normal closure of the
Baumann subgroup of Q is a product of SL₂(2) factors, with the same family
of four-element commutator modules in the original V and its fixed complement.
The action decomposition retains the raw factors inside the normal quotient
image, with injective indexing, relative normality, the original restricted
action and the matching intrinsic and ambient module families. It also
records solvability, faithfulness and the trivial two-core of that normal
quotient image. BaumannFactorActionData stores these facts; its projection
recovers BaumannFactorModuleData using the same factors and modules.
The result also retains the containment of every Sylow-three fixed space
in the fixed space of the actual Baumann normal closure. Both earlier
decomposition theorems remain projections with their original statements.

Restrict the original quotient action to the normal image of N. Its action
is faithful and its two-core is trivial. Maximal elementary subgroups of Q
give offenders on this unchanged V, and the Baumann subgroup fixes their
Thompson fixed space. Weak closure descends from Q. The action-level product
recognition theorem identifies the entire Baumann normal closure and its
module family. The normal-supplement closure identity and injective subtype
maps transport these factors to the original quotient and ambient module.
No equality with a newly defined vSubgroup Q is asserted or required.

For the companion, each raw factor's derived C3 lies in the three-core of
the normal image of N. Its ambient image lies in the quotient's three-core,
so it is contained in every Sylow-three subgroup. A vector fixed by such
a Sylow subgroup is therefore fixed by each derived C3, hence by the full
factor, and finally by the join of all factors.

All action constructions use the exact original quotient action. The module
product predicate is transported with its existing pairwise independence
meaning; no unrestricted joint independence or product-cardinality formula
is inferred from it.

Source: Stellmacher, Journal of Algebra 190 (1997), the (2.2) action argument
on p20 and its normal-supplement application in (4.6), p26.
-/

namespace Stellmacher.SectionTwo
universe u

private theorem fixedPoints_map_subtype
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (N : Subgroup G) (A : Subgroup N) :
    FixedPoints.subgroup (A.map N.subtype) V = FixedPoints.subgroup A V := by
  ext v
  rw [FixedPoints.mem_subgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hv a
    exact hv ⟨((a : N) : G), Subgroup.mem_map_of_mem N.subtype a.property⟩
  · intro hv a
    obtain ⟨x, hx, hxa⟩ := a.property
    have h := hv ⟨x, hx⟩
    change (x : G) • v = v at h
    change (a : G) • v = v
    rw [← hxa]
    exact h

private theorem oneA_of_map_subtype
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (N : Subgroup G) (S A : Subgroup N)
    (h : SectionOne.oneA (V := V) (S.map N.subtype) (A.map N.subtype)) :
    SectionOne.oneA (V := V) S A := by
  have hAS : A ≤ S := (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp h.1
  have hAe : IsElementaryAbelian 2 A := by
    let _ : IsElementaryAbelian 2 (A.map N.subtype) := h.2.1
    have hh := IsElementaryAbelian.subgroupOf (p := 2) (Subgroup.map_subtype_le A)
    rwa [subgroupOf_map_subtype_eq] at hh
  refine ⟨hAS, hAe, ?_⟩
  have hm := h.2.2
  unfold SectionOne.m at hm ⊢
  rwa [fixedPoints_map_subtype, Subgroup.card_map_of_injective N.subtype_injective] at hm

private theorem commutatorAction_map_subtype
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (E : Subgroup G) (D : Subgroup E) :
    commutatorAction (D.map E.subtype) V = commutatorAction D V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨d,v,rfl⟩
    obtain ⟨d₀,hd₀,heq⟩ := d.property
    refine ⟨⟨d₀,hd₀⟩,v,?_⟩
    change v⁻¹ * (d : G) • v = v⁻¹ * (d₀ : G) • v
    change (d₀ : G) = (d : G) at heq
    rw [heq]
  · rintro ⟨d,v,rfl⟩
    exact ⟨⟨((d : E) : G), Subgroup.mem_map_of_mem E.subtype d.property⟩,v,rfl⟩


private theorem map_subgroupMap_subtype
    {G H : Type*} [Group G] [Group H] (q : G →* H)
    (N : Subgroup G) (A : Subgroup N) :
    (A.map (q.subgroupMap N)).map (N.map q).subtype = (A.map N.subtype).map q := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

set_option maxHeartbeats 900000 in
/-- Retain the raw natural-action factor family and its exact maps on the
original module, together with every Sylow-three fixed-space containment. -/
public theorem normal_supplement_baumann_action_decomposition
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (N : Subgroup G) [N.Normal] (Q : Sylow 2 N)
    (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q : Subgroup N).map N.subtype : Subgroup G) : Set G))
    (hVQ : vSubgroup S ≤ (Q : Subgroup N).map N.subtype) :
    let B := (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set G)
    let _ := quotientConjugationAction S q hq hker
    BaumannFactorActionData (vSubgroup S) (Subgroup.normalClosure (B : Set G)) q (N.map q) ∧
      ∀ U : Sylow 3 barG,
        FixedPoints.subgroup U (vSubgroup S) ≤
          FixedPoints.subgroup ((Subgroup.normalClosure (B : Set G)).map q) (vSubgroup S) := by
  classical
  let V := vSubgroup S
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let _ := quotientConjugationAction S q hq hker
  let _ : Group.IsSolvable G := h.solvable
  let _ : Group.IsSolvable barG := Group.isSolvable_of_surjective hq
  let barN := N.map q
  let _ : barN.Normal := Subgroup.Normal.map inferInstance q hq
  let f : N →* barN := q.subgroupMap N
  have hf : Function.Surjective f := q.subgroupMap_surjective N
  let T : Sylow 2 barN := Q.mapSurjective hf
  let QA := (Q : Subgroup N).map N.subtype
  let B := QA ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ QA) : Set G)
  let b := B.subgroupOf N
  let J := (elementaryAbelianMaxJ (Q : Subgroup N)).map f
  let Bbar := b.map f
  let I := {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups QA}
  let A : I → Subgroup barN := fun a => (a.val.subgroupOf N).map f
  have hQAN : QA ≤ N := Subgroup.map_subtype_le _
  have hBN : B ≤ N := inf_le_left.trans hQAN
  have hQmap : (T : Subgroup barN).map barN.subtype = QA.map q := by
    change ((Q : Subgroup N).map f).map barN.subtype = _
    exact map_subgroupMap_subtype q N (Q : Subgroup N)
  have hBmap : Bbar.map barN.subtype = B.map q := by
    rw [show Bbar = b.map (q.subgroupMap N) from rfl,
      map_subgroupMap_subtype q N b, Subgroup.map_subgroupOf_eq_of_le hBN]
  have hJmap : J.map barN.subtype = (elementaryAbelianMaxJ QA).map q := by
    rw [show J = (elementaryAbelianMaxJ (Q : Subgroup N)).map (q.subgroupMap N) from rfl,
      map_subgroupMap_subtype, ← elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective]
  have hAmap (a : I) : (A a).map barN.subtype = a.val.map q := by
    change ((a.val.subgroupOf N).map (q.subgroupMap N)).map barN.subtype = _
    rw [map_subgroupMap_subtype,
      Subgroup.map_subgroupOf_eq_of_le (a.property.1.trans hQAN)]
  obtain ⟨hOff, hFix⟩ := relative_baumann_action_inputs h S q hq hker QA B hVQ inf_le_right
  have hA : ∀ a, SectionOne.oneA (V := V) (T : Subgroup barN) (A a) := by
    intro a
    apply oneA_of_map_subtype barN (T : Subgroup barN) (A a)
    rw [hQmap, hAmap]
    exact hOff a.val a.property
  have hJgen : J = ⨆ a, A a := by
    apply Subgroup.map_injective barN.subtype_injective
    rw [hJmap, Subgroup.map_iSup]
    have hj : elementaryAbelianMaxJ QA = ⨆ a : I, a.val := by
      apply le_antisymm
      · exact sSup_le fun K hK => le_iSup (fun a : I => a.val) ⟨K, hK⟩
      · exact iSup_le fun a => le_sSup a.property
    rw [hj, Subgroup.map_iSup]
    exact iSup_congr fun a => (hAmap a).symm
  have hweak : ∀ g : barN, J.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup barN) →
      J.map (MulAut.conj g).toMonoidHom = J := by
    intro g hg
    exact weakly_closed_map_of_surjective Q (elementaryAbelianMaxJ (Q : Subgroup N))
      (sSup_le fun a ha => ha.1)
      (fun x hx => elementaryAbelianMaxJ_map_eq_of_le (Q : Subgroup N) (MulAut.conj x) hx)
      f hf g hg
  have hJQB : elementaryAbelianMaxJ QA ≤ B := by
    refine le_inf (sSup_le fun a ha => ha.1) ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 j hj |>.symm
  have hJB : J ≤ Bbar := by
    apply (Subgroup.map_le_map_iff_of_injective barN.subtype_injective).mp
    rw [hJmap, hBmap]
    exact Subgroup.map_mono hJQB
  have hBS : Bbar ≤ (T : Subgroup barN) := by
    apply (Subgroup.map_le_map_iff_of_injective barN.subtype_injective).mp
    rw [hBmap, hQmap]
    exact Subgroup.map_mono inf_le_left
  have hBfix : Bbar ≤ fixingSubgroup barN (FixedPoints.subgroup J V : Set V) := by
    intro x hx
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hv' : v ∈ FixedPoints.subgroup ((elementaryAbelianMaxJ QA).map q) V := by
      rw [← hJmap, fixedPoints_map_subtype]
      exact hv
    have hx' : (x : barG) ∈ B.map q := by
      rw [← hBmap]
      exact Subgroup.mem_map_of_mem barN.subtype hx
    exact (mem_fixingSubgroup_iff (M := barG)).mp (hFix hx') v hv'
  have hfaith : fixingSubgroup barN (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hx' : (x : barG) ∈ fixingSubgroup barG (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff] at hx ⊢
      exact hx
    rw [quotientConjugationAction_faithful S q hq hker] at hx'
    exact hx'
  have hcore : pCore 2 barN = ⊥ := by
    have hn : ((pCore 2 barN).map barN.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hle : (pCore 2 barN).map barN.subtype ≤ pCore 2 barG :=
      le_sSup ⟨hn, (pCore_isPGroup (p := 2) (G := barN)).map barN.subtype⟩
    rw [lemma_two_one h S q hq hker] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ barN.subtype_injective).mp (bot_unique hle)
  obtain ⟨_, n, D, hDgen, hDprod, hDin, hD, hDn, hmodule⟩ :=
    SectionOne.weakly_closed_offender_baumann_product
      (inferInstance : Group.IsSolvable barN) hfaith hcore T A hA J Bbar hJgen hweak hJB hBS hBfix
  let L := Subgroup.normalClosure (B : Set G)
  let Lbar := Subgroup.normalClosure (Bbar : Set barN)
  change Lbar = ⨆ i, D i at hDgen
  have hSNB : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) :=
    hSN.trans (normalizer_le_normalizer_baumann QA)
  have hL : L = (Subgroup.normalClosure (b : Set N)).map N.subtype :=
    Subgroup.normalClosure_eq_map_of_normal_supplement N (S : Subgroup G) B hgen hBN hSNB
  have hLbar : Lbar = (Subgroup.normalClosure (b : Set N)).map f := by
    rw [Subgroup.map_normalClosure _ f hf]
    rfl
  have hLmap : Lbar.map barN.subtype = L.map q := by
    rw [hLbar]
    change ((Subgroup.normalClosure (b : Set N)).map (q.subgroupMap N)).map barN.subtype = _
    rw [map_subgroupMap_subtype, ← hL]
  let E (i : Fin n) := (D i).map barN.subtype
  have hfixmap : (FixedPoints.subgroup Lbar V).map V.subtype =
      V ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← fixedPoints_map_subtype barN Lbar, hLmap]
    exact quotientConjugationAction_fixedPoints_image_map S q hq hker L
  have hthree : ∀ U : Sylow 3 barG,
      FixedPoints.subgroup U V ≤ FixedPoints.subgroup (L.map q) V := by
    have hcoreNormal : ((pCore 3 barN).map barN.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hcoreMap : (pCore 3 barN).map barN.subtype ≤ pCore 3 barG :=
      le_sSup ⟨hcoreNormal, (pCore_isPGroup (p := 3) (G := barN)).map barN.subtype⟩
    intro U v hv
    rw [← hLmap, fixedPoints_map_subtype]
    have hLfix : Lbar ≤ fixingSubgroup barN ({v} : Set V) := by
      rw [hDgen]
      refine iSup_le fun i => ?_
      intro d hd
      rw [mem_fixingSubgroup_iff]
      intro w hw
      have hwv : w = v := Set.mem_singleton_iff.mp hw
      subst w
      apply SectionOne.oneSevenFactor_fixes_derived_fixedPoints (D i) (hD i) d hd v
      rw [FixedPoints.mem_subgroup]
      intro k
      have hk : ((k : barN) : barG) ∈ (U : Subgroup barG) :=
        (pCore_isPGroup (p := 3) (G := barG)).le_sylow_of_normal U
          (hcoreMap (Subgroup.mem_map_of_mem barN.subtype
            (SectionOne.oneSevenFactor_derived_le_threeCore (D i) (hD i) k.property)))
      exact (FixedPoints.mem_subgroup (M := U) (a := v)).mp hv ⟨_, hk⟩
    rw [FixedPoints.mem_subgroup]
    intro l
    exact (mem_fixingSubgroup_iff (M := barN)).mp (hLfix l.property) v (Set.mem_singleton v)
  have hL0 : (L.map q).subgroupOf barN = Lbar := by
    rw [← hLmap, subgroupOf_map_subtype_eq]
  refine ⟨⟨inferInstance, hfaith, hcore, ?_⟩, hthree⟩
  rw [hL0]
  refine ⟨n, D, hLmap, hDprod, hDin, hD, hDn, hmodule, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · simpa only [E, commutatorAction_map_subtype] using
        quotientConjugationAction_commutator_map S q hq hker (E i)
    · rw [Subgroup.card_map_of_injective V.subtype_injective]
      exact (hD i).2.2.1
  · have hm := hmodule.map_injective V.subtype V.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
    convert hm using 1
    funext i
    cases i with
    | none => exact hfixmap.symm
    | some i => rfl

/-- The normal-supplement factor decomposition, together with control of every
Sylow-three fixed space for the same original quotient action. -/
public theorem normal_supplement_baumann_decomposition_with_three_fixed
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (N : Subgroup G) [N.Normal] (Q : Sylow 2 N)
    (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q : Subgroup N).map N.subtype : Subgroup G) : Set G))
    (hVQ : vSubgroup S ≤ (Q : Subgroup N).map N.subtype) :
    let B := (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set G)
    let _ := quotientConjugationAction S q hq hker
    BaumannFactorModuleData (vSubgroup S) (Subgroup.normalClosure (B : Set G)) q ∧
      ∀ U : Sylow 3 barG,
        FixedPoints.subgroup U (vSubgroup S) ≤
          FixedPoints.subgroup ((Subgroup.normalClosure (B : Set G)).map q) (vSubgroup S) := by
  let _ := quotientConjugationAction S q hq hker
  have hr := normal_supplement_baumann_action_decomposition h S q hq hker N Q hgen hSN hVQ
  exact ⟨hr.1.toModuleData, hr.2⟩


/-- The normal-supplement Baumann closure decomposes on the unchanged original V. -/
public theorem normal_supplement_baumann_decomposition
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (N : Subgroup G) [N.Normal] (Q : Sylow 2 N)
    (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q : Subgroup N).map N.subtype : Subgroup G) : Set G))
    (hVQ : vSubgroup S ≤ (Q : Subgroup N).map N.subtype) :
    let B := (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set G)
    BaumannFactorModuleData (vSubgroup S) (Subgroup.normalClosure (B : Set G)) q := by
  exact (normal_supplement_baumann_decomposition_with_three_fixed
    h S q hq hker N Q hgen hSN hVQ).1

end Stellmacher.SectionTwo
