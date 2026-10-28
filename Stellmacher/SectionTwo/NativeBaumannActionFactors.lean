module

public import Stellmacher.SectionTwo.LemmaTwoTwo
public import Stellmacher.SectionOne.WeaklyClosedOffenderBaumannProduct

/-!
# Rich action factors of the native Baumann closure

For the exact Section Two quotient action on V=⟨Ω₁(Z(S))^G⟩, this module
retains the one-seven factor data in the Baumann normal closure. Its Thompson
and Baumann images coincide, and the same finite family gives the group
product and the fixed-space/commutator module product. Each factor retains its
one-seven predicate and its normality inside that closure.

Maximal elementary subgroup images give offenders. Their join is the Thompson
image; its weak closure descends through the quotient. The Baumann fixed-space
theorem verifies pointwise fixation, so the generic weakly closed offender
product theorem applies directly. All constructions use the original named
quotient-conjugation action. No equivalent replacement module is introduced.

This is the richer form of the native action argument in Stellmacher (2.2),
Journal of Algebra 190 (1997), p.20, needed to identify the selected factor's
actual module in (6.1), p.30. The numbered (2.2) interface remains unchanged.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem nativeBaumann_action_factors
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hJne : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≠ ⊥) :
    letI := quotientConjugationAction S q hq hker
    let L := Subgroup.normalClosure (B.map q : Set barG)
    (elementaryAbelianMaxJ (S : Subgroup G)).map q = B.map q ∧
      ∃ (n : ℕ) (D : Fin n → Subgroup barG),
        L = ⨆ i, D i ∧ IsInternalDirectProductFamily L D ∧ Function.Injective D ∧
        (∀ i, SectionOne.IsOneSevenFactor (V := vSubgroup S) (D i)) ∧
        (∀ i, ((D i).subgroupOf L).Normal) ∧
        IsInternalDirectProductFamily (⊤ : Subgroup (vSubgroup S))
          (fun i : Option (Fin n) => match i with
            | none => FixedPoints.subgroup L (vSubgroup S)
            | some i => commutatorAction (D i) (vSubgroup S)) := by
  let V := vSubgroup S
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let _ := quotientConjugationAction S q hq hker
  let J := (elementaryAbelianMaxJ (S : Subgroup G)).map q
  let T := S.mapSurjective hq
  let I := {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)}
  let A : I → Subgroup barG := fun a => a.val.map q
  have hA : ∀ a, SectionOne.oneA (V := V) (T : Subgroup barG) (A a) :=
    fun a => maxElementary_map_mem_oneA h S q hq hker a.val a.property
  have hJgen : J = ⨆ i, A i := by
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply sSup_le
      intro a ha
      exact Subgroup.map_le_iff_le_comap.mp (le_iSup A (⟨a, ha⟩ : I))
    · exact iSup_le fun i => Subgroup.map_mono (le_sSup i.property)
  have hweak : ∀ g : barG, J.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup barG) →
      J.map (MulAut.conj g).toMonoidHom = J := by
    intro g hg
    exact weakly_closed_map_of_surjective S (elementaryAbelianMaxJ (S : Subgroup G))
      (sSup_le fun _ ha => ha.1)
      (fun g hg => elementaryAbelianMaxJ_map_eq_of_le (S : Subgroup G) (MulAut.conj g) hg)
      q hq g hg
  have hJB : J ≤ B.map q := by
    apply Subgroup.map_mono
    rw [hB]
    refine le_inf (sSup_le fun _ ha => ha.1) ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm
  have hBS : B.map q ≤ (T : Subgroup barG) := by
    apply Subgroup.map_mono
    rw [hB]
    exact inf_le_left
  have hBfix : B.map q ≤ fixingSubgroup barG (FixedPoints.subgroup J V : Set V) :=
    baumann_image_fixes_thompson_fixedPoints h S q hq hker B (hB ▸ inf_le_right)
  have h1 := quotientConjugationAction_hypotheses h S q hq hker hJne
  exact SectionOne.weakly_closed_offender_baumann_product h1.G_solvable h1.action_faithful
    h1.twoCore_eq_bot T A hA J (B.map q) hJgen hweak hJB hBS hBfix

end Stellmacher.SectionTwo
