module
public import Stellmacher.SectionTwo.LemmaTwoTwo
public import Stellmacher.SectionTwo.TwoThreeCentralizingCase
public import Stellmacher.SectionTwo.BaumannThompsonSupplement

/-!
# The final Sylow reduction in Stellmacher (2.3)

Assume the Section 2 hypotheses, the core-centralizer equality, and that
the 2-core of the Thompson normal closure E lies in the Baumann subgroup B.
Then B is the ambient image of a Sylow 2-subgroup of its normal closure L.
The centralizing case is handled by the independent proved special case.

Otherwise (2.2) identifies the images of J(S) and B. Reconstructing its
quotient action and selected maximal-elementary offender family gives the
image of J(S) as the intersection of the quotient Sylow subgroup and the
image of E. For e in S∩E, choose
j in J(S) with the same quotient image. The difference ej⁻¹ lies in E
and in O₂(G), hence in O₂(E) and therefore B. This proves S∩E≤B.
The Baumann supplement theorem gives L=EB. Ordinary product decomposition
then yields S∩L=B, and normality of L supplies the required Sylow witness.

This is the final inference in Stellmacher (2.3), Journal of Algebra 190
(1997), p.20, following refs/latex/stellmacher-n-group.tex. The core bound
is an explicit premise here and is proved separately via opposite conjugates.
-/

namespace Stellmacher.SectionTwo
universe u

private theorem sylow_inf_le_baumann_of_image_le
    {G X : Type*} [Group G] [Finite G] [Group X]
    (S : Sylow 2 G) (E J B : Subgroup G)
    (q : G →* X) (hker : q.ker = cSubgroup S)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓
      Subgroup.centralizer (vSubgroup S : Set G))
    (hJS : J ≤ (S : Subgroup G)) (hJE : J ≤ E) (hJB : J ≤ B)
    (himage : ((S : Subgroup G) ⊓ E).map q ≤ J.map q)
    (hEB : twoCoreAmbient E ≤ B) : (S : Subgroup G) ⊓ E ≤ B := by
  have hrestrict : (pCore 2 G).subgroupOf E ≤ pCore 2 E :=
    le_sSup ⟨inferInstance, (pCore_isPGroup (p := 2) (G := G)).comap_of_injective
      E.subtype E.subtype_injective⟩
  intro e he
  obtain ⟨j, hj, hje⟩ := himage (Subgroup.mem_map_of_mem q he)
  have hdE : e * j⁻¹ ∈ E := E.mul_mem he.2 (E.inv_mem (hJE hj))
  have hdS : e * j⁻¹ ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem he.1 ((S : Subgroup G).inv_mem (hJS hj))
  have hdk : e * j⁻¹ ∈ q.ker := by
    change q (e * j⁻¹) = 1
    rw [map_mul, map_inv, hje, mul_inv_cancel]
  have hdcore : e * j⁻¹ ∈ pCore 2 G := by
    rw [hcore]
    refine ⟨hdS, ?_⟩
    change e * j⁻¹ ∈ cSubgroup S
    rwa [← hker]
  have hdEB : e * j⁻¹ ∈ B := hEB (Subgroup.mem_map.mpr
    ⟨⟨e * j⁻¹, hdE⟩, hrestrict hdcore, rfl⟩)
  have hh := B.mul_mem hdEB (hJB hj)
  simpa only [inv_mul_cancel_right] using hh

private theorem sylow_of_normal_supplement_inf_le
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (E B L : Subgroup G) [E.Normal] [L.Normal]
    (hBS : B ≤ (S : Subgroup G)) (hL : L = E ⊔ B)
    (hSEB : (S : Subgroup G) ⊓ E ≤ B) :
    ∃ P : Sylow 2 L, P.map L.subtype = B := by
  have hSL : (S : Subgroup G) ⊓ L = B := by
    apply le_antisymm
    · intro s hs
      rw [hL] at hs
      obtain ⟨e, he, b, hb, heb⟩ := Subgroup.mem_sup_of_normal_left.mp hs.2
      have heS : e ∈ (S : Subgroup G) := by
        have heq : e = s * b⁻¹ := by rw [← heb]; group
        rw [heq]
        exact (S : Subgroup G).mul_mem hs.1 ((S : Subgroup G).inv_mem (hBS hb))
      rw [← heb]
      exact B.mul_mem (hSEB ⟨heS, he⟩) hb
    · exact le_inf hBS (by rw [hL]; exact le_sup_right)
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal L
  refine ⟨P, ?_⟩
  rw [hP, Subgroup.subgroupOf_map_subtype, hSL]

public theorem two_three_sylow_of_core_le_baumann
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓
      Subgroup.centralizer (vSubgroup S : Set G))
    (B L : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hL : L = Subgroup.normalClosure (B : Set G))
    (hEB : twoCoreAmbient (Subgroup.normalClosure
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) ≤ B) :
    ∃ P : Sylow 2 L, P.map L.subtype = B := by
  by_cases hcent : vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)
  · exact lemma_two_three_of_v_centralizes_j h S hcore B L hB hL hcent
  let V := vSubgroup S
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let C := cSubgroup S
  let : (vSubgroup S).Normal := by unfold vSubgroup; infer_instance
  let : C.Normal := by unfold C cSubgroup; infer_instance
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : q.ker = cSubgroup S := QuotientGroup.ker_mk' C
  have hJne : J.map q ≠ ⊥ := by
    intro hbot
    have hJC : J ≤ Subgroup.centralizer (vSubgroup S : Set G) := by
      change J ≤ cSubgroup S
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff J).mp hbot
    exact hcent (Subgroup.le_centralizer_iff.mp hJC)
  have h22 := lemma_two_two h S q hq hker ((S : Subgroup G).map q) (J.map q)
    (B.map q) rfl B hB rfl rfl hJne
  have hJS : J ≤ (S : Subgroup G) := sSup_le fun _ hA => hA.1
  let Jb := J.map q
  let Eb := ⁅SectionOne.oddCore (G ⧸ C), Jb⁆ ⊔ Jb
  let : Eb.Normal := h22.part_a
  have hclosure : Subgroup.normalClosure (Jb : Set (G ⧸ C)) = Eb := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal (show Jb ≤ Eb from le_sup_right)
    · exact sup_le
        ((Subgroup.commutator_mono le_rfl Subgroup.le_normalClosure).trans
          (Subgroup.commutator_le_right _ _)) Subgroup.le_normalClosure
  have himage : E.map q = Eb := by
    rw [show E = Subgroup.normalClosure (J : Set G) from rfl,
      Subgroup.map_normalClosure _ q hq]
    exact hclosure
  let : IsElementaryAbelian 2 V :=
    (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let := quotientConjugationAction S q hq hker
  have h1 : SectionOne.Hypotheses (G ⧸ C) V :=
    quotientConjugationAction_hypotheses h S q hq hker hJne
  let T := S.mapSurjective hq
  let I := {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)}
  let A : I → Subgroup (G ⧸ C) := fun a => a.val.map q
  have hA : ∀ a, SectionOne.oneA (V := V) (T : Subgroup (G ⧸ C)) (A a) :=
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
  have hJimage : J.map q = (S : Subgroup G).map q ⊓ E.map q := by
    change Jb = (T : Subgroup (G ⧸ C)) ⊓ E.map q
    rw [himage]
    exact hJinf
  have hLsup : L = E ⊔ B := hL.trans
    (normalClosure_baumann_eq_thompson_sup_of_image_eq S B hB q hker hcore h22.part_b)
  have hJE : J ≤ E := Subgroup.le_normalClosure
  have hJB : J ≤ B := by
    rw [hB]
    refine le_inf hJS ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 j hj |>.symm
  have hmaple : ((S : Subgroup G) ⊓ E).map q ≤ J.map q := by
    rw [hJimage]
    exact le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
  have hSEB := sylow_inf_le_baumann_of_image_le S E J B q hker hcore hJS hJE hJB
    hmaple hEB
  let : L.Normal := hL ▸ inferInstance
  exact sylow_of_normal_supplement_inf_le S E B L
    (hB ▸ inf_le_left) hLsup hSEB

end Stellmacher.SectionTwo
