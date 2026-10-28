module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SylowSource
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.PointFixed
public import Theory.GroupTheory.ElementaryPairInvolutionUnion
/-!
# All maximal elementary subgroups of the original source Sylow

After core absorption, Q=U is the kernel of the Baumann action on U.
A noncentral element of Uˣ therefore detects the full fixed space, which is
Z(R)=U∩Uˣ. Every involution of R=UUˣ lies in U∪Uˣ. Hence every elementary
subgroup lies in one factor; their known maximum orders prove that these
are exactly the maximal elementary subgroups by inclusion.

Source: Aschbacher–Smith, Lemma 2.4.8(7), printed pp.529 and531.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_elementary_subgroup_pair
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let U := sourceModule (d.block.map d.H.subtype)
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    (∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ V) ∧
      ∀ E : Subgroup G, E ≤ R → IsElementaryAbelian 2 E → E ≤ U ∨ E ≤ V := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  obtain ⟨c,F,hF,h,hint,y,hy,hnc⟩ := d.single_natural_configuration hG T hST.le hsingle hK
    (T : Subgroup G) hST.le le_rfl ht.1
  have hh := ChapterC.Section06.rankOne_family_from_original c h ht.1 y hy hnc
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  have hSR : RankOne.S S = R := hh.2.1
  have hUQ : U = twoCore d.H := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  have hQU : RankOne.Q S L = U := hh.1.trans hUQ.symm
  have hpair : U ⊔ V = R := (hf.2.2.2 x hxT hxS).1.symm
  have hUV : U ⊓ V = R ⊓ centralizer (R : Set G) :=
    source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hUR : U ≤ R := le_sup_left.trans_eq hpair
  have hVR : V ≤ R := le_sup_right.trans_eq hpair
  let : IsElementaryAbelian 2 (U : Type _) := h.elementary
  let : IsElementaryAbelian 2 (V : Type _) := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hVU : V ≤ normalizer (U : Set G) :=
    hVR.trans (hSR ▸ h.coordinates.normalizes)
  have hfix : ∀ v ∈ V, v ∉ U → ∀ u ∈ U, Commute v u → u ∈ V := by
    intro v hv hvU u hu hc
    have hvS : v ∈ RankOne.S S := hSR.symm ▸ hVR hv
    have hvc : v ∉ centralizer (U : Set G) := by
      intro he
      have hvQ : v ∈ RankOne.Q S L := h.core.symm ▸ ⟨hvS,he⟩
      exact hvU (hQU ▸ hvQ)
    have hfU : RankOne.moduleConjugate h.coordinates.normalizes ⟨v,hvS⟩ ⟨u,hu⟩ = ⟨u,hu⟩ := by
      apply Subtype.ext
      change v*u*v⁻¹=u
      rw [hc.eq,mul_inv_cancel_right]
    have huC := h.fixed_by_noncentral_imp_fixed_by_all ⟨v,hvS⟩ hvc ⟨u,hu⟩ hfU
    have huZ : u ∈ R ⊓ centralizer (R : Set G) := ⟨hUR hu,hSR ▸ huC⟩
    exact (hUV.symm ▸ huZ).2
  have hu := elementary_pair_involution_union R U V hpair hVU hfix
  change (∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ V) ∧ _
  refine ⟨hu,?_⟩
  intro E hER hE
  let := hE
  exact le_one_of_elementwise_union E U V (fun e he =>
    hu e (hER he) (elemPow_eq_one_of_isElementaryAbelian e he))

/-- Maximality here is by inclusion, so smaller maximal elementary subgroups are excluded. -/
theorem lemma_2_4_8_7
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let U := sourceModule (d.block.map d.H.subtype)
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    ∀ E : Subgroup G,
      (E ≤ R ∧ IsElementaryAbelian 2 E ∧
        ∀ W : Subgroup G, E ≤ W → W ≤ R → IsElementaryAbelian 2 W → W=E) ↔ E=U ∨ E=V := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  have hp := hf.2.2.2 x hxT hxS
  have hUR : U ≤ R := le_sup_left.trans_eq hp.1.symm
  have hVR : V ≤ R := le_sup_right.trans_eq hp.1.symm
  have hUA : U ∈ Stellmacher.elementaryAbelianMaxSubgroups S := by
    rw [hp.2.1]
    exact Set.mem_insert _ _
  have hVA : V ∈ Stellmacher.elementaryAbelianMaxSubgroups S := by
    rw [hp.2.1]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hm (W : Subgroup G) (hWR : W ≤ R) (hWA : W ∈ Stellmacher.elementaryAbelianMaxSubgroups S) :
      W ≤ R ∧ IsElementaryAbelian 2 W ∧
        ∀ E : Subgroup G, W ≤ E → E ≤ R → IsElementaryAbelian 2 E → E=W := by
    refine ⟨hWR,hWA.2.1,?_⟩
    intro E hWE hER hE
    exact (eq_of_le_of_card_ge hWE (hWA.2.2 E (hER.trans hRS) hE)).symm
  change ∀ E : Subgroup G, _
  intro E
  constructor
  · rintro ⟨hER,hE,hmax⟩
    rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).2
      E hER hE with hEU | hEV
    · exact Or.inl (hmax U hEU hUR hUA.2.1).symm
    · exact Or.inr (hmax V hEV hVR hVA.2.1).symm
  · rintro (rfl|rfl)
    · exact hm U hUR hUA
    · exact hm V hVR hVA
end CFSG.Quasithin.Chapter2.LinearShadows.Single
