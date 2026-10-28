module

public import Stellmacher.SectionTwo.LemmaTwoTwo
public import Stellmacher.SectionTwo.QuotientOppositeLift
public import Stellmacher.SectionOne.OneSevenOppositeSylow

/-!
# The opposite conjugate in Stellmacher (2.3)

In the noncentralizing case of (2.3), let `J` be the elementary Thompson
subgroup of the ambient Sylow subgroup and let `E` be its normal closure.
There is one `x ∈ E` such that `J` and `Jˣ`, together with the part of `E`
centralizing `V`, generate `E`; their fixed subgroups also span `V`.

Pass to the faithful conjugation action on `V` through `G / C_G(V)`. Lemma
(2.2) identifies the image of `E` with its normal internal product of
`SL₂(2)` factors. The simultaneous opposite-Sylow result from (1.7) chooses
one conjugator whose two Sylow intersections generate this product and whose
fixed spaces span the module. The generic quotient lift then gives both
assertions in the ambient group with the same lifted element.

This is the two-conjugate structural step in the proof of Stellmacher (2.3),
Journal of Algebra 190 (1997), p. 20; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionTwo

universe u

private theorem quotient_opposite
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (hJne : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≠ ⊥) :
    letI := quotientConjugationAction S q hq hker
    let J := elementaryAbelianMaxJ (S : Subgroup G)
    let E := Subgroup.normalClosure (J : Set G)
    ∃ b ∈ E.map q, E.map q = J.map q ⊔ (J.map q).conjBy b ∧
      FixedPoints.subgroup (J.map q) (vSubgroup S) ⊔
        FixedPoints.subgroup ((J.map q).conjBy b) (vSubgroup S) = ⊤ := by
  classical
  let V := vSubgroup S
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let Jb := J.map q
  let Eb := ⁅SectionOne.oddCore barG, Jb⁆ ⊔ Jb
  let T := S.mapSurjective hq
  let : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let := quotientConjugationAction S q hq hker
  have h1 : SectionOne.Hypotheses barG V :=
    quotientConjugationAction_hypotheses h S q hq hker hJne
  let I := {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)}
  let A : I → Subgroup barG := fun a => a.val.map q
  have hA : ∀ a, SectionOne.oneA (V := V) (T : Subgroup barG) (A a) :=
    fun a => maxElementary_map_mem_oneA h S q hq hker a.val a.property
  have hJgen : Jb = ⨆ a, A a := by
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply sSup_le
      intro a ha
      exact Subgroup.map_le_iff_le_comap.mp (le_iSup A (⟨a, ha⟩ : I))
    · exact iSup_le fun a => Subgroup.map_mono (le_sSup a.property)
  obtain ⟨hJinf, _⟩ :=
    SectionOne.offender_generated_selected_product h1 T A hA Jb hJgen
  obtain ⟨_, _, F, hprod, hF⟩ :=
    SectionOne.offender_selected_finite_product h1 T A hA Jb hJgen
  let B := (S : Subgroup G) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient J : Set G)
  have h22 := lemma_two_two h S q hq hker ((S : Subgroup G).map q) Jb
    (B.map q) rfl B rfl rfl rfl hJne
  have hEb : Eb.Normal := h22.part_a
  let _ : Eb.Normal := hEb
  have hclosure : Subgroup.normalClosure (Jb : Set barG) = Eb := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal (show Jb ≤ Eb from le_sup_right)
    · exact sup_le
        ((Subgroup.commutator_mono le_rfl Subgroup.le_normalClosure).trans
          (Subgroup.commutator_le_right _ _)) Subgroup.le_normalClosure
  have himage : E.map q = Eb := by
    rw [show E = Subgroup.normalClosure (J : Set G) from rfl,
      Subgroup.map_normalClosure _ q hq]
    exact hclosure
  obtain ⟨b, hb, hgen, hspan⟩ :=
    SectionOne.oneSevenFactor_exists_opposite_sylow h1 T Eb hEb F hprod hF
  rw [← hJinf] at hgen hspan
  refine ⟨b, ?_, ?_, hspan⟩
  · rwa [himage]
  · rw [himage]
    exact hgen

/-- The common opposite conjugator and fixed-space span used in the
noncentralizing case of Stellmacher (2.3). -/
public theorem two_three_opposite_conjugate
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) :
    let J := elementaryAbelianMaxJ (S : Subgroup G)
    let E := Subgroup.normalClosure (J : Set G)
    ∃ x ∈ E, E = (J ⊔ J.conjBy x) ⊔ (E ⊓ cSubgroup S) ∧
      vSubgroup S =
        (vSubgroup S ⊓ Subgroup.centralizer (J : Set G)) ⊔
          (vSubgroup S ⊓ Subgroup.centralizer (J.conjBy x : Set G)) := by
  let V := vSubgroup S
  let C := cSubgroup S
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : C.Normal := Subgroup.normal_centralizer
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : q.ker = cSubgroup S := QuotientGroup.ker_mk' C
  have hJne : J.map q ≠ ⊥ := by
    intro hbot
    have hJC : J ≤ q.ker := (Subgroup.map_eq_bot_iff (f := q) _).mp hbot
    rw [hker] at hJC
    exact hnot (Subgroup.le_centralizer_iff.mpr hJC)
  obtain ⟨b, hb, hgen, hspan⟩ := quotient_opposite h S q hq hker hJne
  simpa only [hker] using
    quotient_opposite_lift S q hq hker E J Subgroup.le_normalClosure b hb hgen hspan

end Stellmacher.SectionTwo
