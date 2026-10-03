module
public import Stellmacher.SectionTwo.LemmaTwoTwo
public import Stellmacher.SectionOne.OneSevenProductSaturation
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionThree.NormalClosureResidualJoin
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# The native Baumann image is the global offender group locally

For the actual Section Two quotient action on V=⟨Ω₁(Z(S))^G⟩, assume the
original group belongs to the Section Three P-set relative to S and the
native elementary Thompson image is nontrivial. Then the native Baumann
image equals the global action-defined J(V,q(S)). The P-set hypothesis
is essential to the residual-generation argument; no unconditional
identification between native and action-defined actors is asserted.

The images of the maximal elementary subgroups are actual offenders.
Their selected factor product E₀ intersects the quotient Sylow in the
native Thompson image J, and (2.2) makes E₀ normal. Thus J is normal in
the quotient Sylow. Its Sylow lift cannot lie in the original two-core,
whose image lies in the quotient's trivial two-core. The normal-closure
form of (3.4) therefore puts the full quotient two-residual inside E₀.
The three-core lies in that residual, so factor saturation makes E₀ the
global one-seven product. Taking the Sylow intersection identifies J with
the global offender group, and (2.2) identifies J with the Baumann image.

This is the local comparison required in Stellmacher (9.3), Journal of
Algebra 190 (1997), p.50, when a central element of the native Baumann
group is used with the canonical barred (6.4) action. Source:
`refs/files/stellmacher-n-group.pdf`. The supplied quotient homomorphism
and its named conjugation action are retained throughout.
-/
namespace Stellmacher.SectionTwo
universe u

public theorem native_baumann_image_eq_global_oneJ_of_pSet
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hP : (⊤ : Subgroup G) ∈ SectionThree.PSet ⊤ (S : Subgroup G))
    {X : Type u} [Group X] [Finite X]
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hJne : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≠ ⊥) :
    letI := quotientConjugationAction S q hq hker
    B.map q = SectionOne.oneJ (V := vSubgroup S) ((S : Subgroup G).map q) := by
  classical
  let V := vSubgroup S
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let _ := quotientConjugationAction S q hq hker
  let _ : Group.IsSolvable G := h.solvable
  let T := S.mapSurjective hq
  let J := (elementaryAbelianMaxJ (S : Subgroup G)).map q
  let E0 := ⁅SectionOne.oddCore X,J⁆ ⊔ J
  have hOne := quotientConjugationAction_hypotheses h S q hq hker hJne
  let I := {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)}
  let A : I → Subgroup X := fun a => a.val.map q
  have hA : ∀ a, SectionOne.oneA (V := V) (T : Subgroup X) (A a) :=
    fun a => maxElementary_map_mem_oneA h S q hq hker a.val a.property
  have hJgen : J = ⨆ a, A a := by
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply sSup_le
      intro a ha
      exact Subgroup.map_le_iff_le_comap.mp (le_iSup A (⟨a,ha⟩ : I))
    · exact iSup_le fun a => Subgroup.map_mono (le_sSup a.property)
  obtain ⟨hJinf,_,_,n,D,hprod,_,hD,_,_⟩ :=
    SectionOne.offender_generated_selected_product hOne T A hA J hJgen
  have h22 := lemma_two_two h S q hq hker (T : Subgroup X) J (B.map q)
    rfl B hB rfl rfl hJne
  let _ : E0.Normal := h22.part_a
  have hJS : J ≤ (T : Subgroup X) := hJinf ▸ inf_le_left
  have hJn : (J.subgroupOf (T : Subgroup X)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs j hj
    rw [hJinf] at hj ⊢
    exact ⟨T.mul_mem (T.mul_mem hs hj.1) (T.inv_mem hs),
      (inferInstance : E0.Normal).conj_mem j hj.2 s⟩
  let P : Subgroup G := ⊤
  let f : P →* X := q.comp P.subtype
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,rfl⟩ := hq x
    exact ⟨⟨g,Subgroup.mem_top g⟩,rfl⟩
  have hSm : ((S : Subgroup G).subgroupOf P).map f = (T : Subgroup X) := by
    rw [show f = q.comp P.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le (show (S : Subgroup G) ≤ P from le_top)]
    rfl
  have hcore : (twoCoreAmbient P).map q ≤ pCore 2 X := by
    change ((pCore 2 P).map P.subtype).map q ≤ _
    rw [Subgroup.map_map]
    let _ : ((pCore 2 P).map f).Normal := Subgroup.Normal.map inferInstance f hf
    exact le_sSup ⟨inferInstance,(pCore_isPGroup (p := 2) (G := P)).map f⟩
  have hnot : ¬ (S : Subgroup G) ⊓ (J.comap f).map P.subtype ≤ twoCoreAmbient P := by
    intro hc
    apply hJne
    apply bot_unique
    intro j hj
    obtain ⟨s,hs,hsj⟩ := Subgroup.mem_map.mp (hJS hj)
    have hsJ : (⟨s,Subgroup.mem_top s⟩ : P) ∈ J.comap f := by
      change q s ∈ J
      rwa [hsj]
    have hsC := hc ⟨hs,Subgroup.mem_map.mpr ⟨⟨s,Subgroup.mem_top s⟩,hsJ,rfl⟩⟩
    have hjC := hcore (Subgroup.mem_map.mpr ⟨s,hsC,hsj⟩)
    rwa [hOne.twoCore_eq_bot] at hjC
  have h3 : SectionThree.Hypotheses G (S : Subgroup G) :=
    ⟨h.even_order,S.ne_bot_of_dvd_card (even_iff_two_dvd.mp h.even_order),S.isPGroup'⟩
  have hclosure := SectionThree.normalClosure_eq_residual_sup_of_normal_sylow_image
    (S : Subgroup G) h3 P hP inferInstance f hf J
    (hSm.symm ▸ hJS) (hSm.symm ▸ hJn) hnot
  have hRmap : ((twoResidualAmbient P).subgroupOf P).map f =
      twoResidualAmbient (⊤ : Subgroup X) := by
    rw [show f = q.comp P.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le (show twoResidualAmbient P ≤ P from le_top)]
    exact map_twoResidualAmbient_of_subgroup_image P q ⊤ (by
      rw [show P = ⊤ from rfl, ← MonoidHom.range_eq_map, q.range_eq_top_of_surjective hq])
  rw [hRmap] at hclosure
  let R := BenderSuzuki.External.hktPResidual 2 X
  let _ : R.Normal := BenderSuzuki.External.hktPResidual_normal
  have hRE : R ≤ E0 := by
    have hc : Subgroup.normalClosure (J : Set X) ≤ E0 :=
      Subgroup.normalClosure_le_normal (show J ≤ E0 from le_sup_right)
    rw [hclosure,SectionThree.twoResidualAmbient_top_eq_hktPResidual] at hc
    exact le_sup_left.trans hc
  have hthreeR : pCore 3 X ≤ R := by
    let r := QuotientGroup.mk' R
    have h3map := (pCore_isPGroup (p := 3) (G := X)).map r
    have h2map := (BenderSuzuki.External.hktPResidual_quotient_isPGroup
      (q := 2) (Q := X)).to_subgroup ((pCore 3 X).map r)
    have hh : (pCore 3 X).map r = ⊥ := disjoint_self.mp
      (IsPGroup.disjoint_of_ne 3 2 (by decide) _ _ h3map h2map)
    simpa only [r,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh
  have hEsat := SectionOne.oneSevenGenerated_eq_of_threeCore_le hOne D hD E0
    hprod.1 (hthreeR.trans hRE)
  have hJglobal : J = SectionOne.oneJ (V := V) (T : Subgroup X) := by
    rw [hJinf]
    change (T : Subgroup X) ⊓ E0 = _
    rw [hEsat]
    exact (SectionOne.oneSeven_global_identification hOne T).1.symm
  exact h22.part_b.symm.trans hJglobal
end Stellmacher.SectionTwo
