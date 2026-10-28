module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCoreIdentification
public import Stellmacher.ElementaryAbelianMaxPair
public import Stellmacher.ElementaryAbelianMaxPair.Normalizers

/-!
# The original pair of elementary sixteens

Every element of the closure U outside Z_S fixes exactly Z_S on V:
a nonidentity natural automizer moves at least two binary dimensions.
Since T∩L=UV, its involutions therefore lie in U or V, and every elementary
subgroup lies in one of those two groups. They are precisely its maximum
elementary subgroups. The component Sylow normalizer fixes V, hence also U.
Together with C_G(z), it generates the source overgroup acting on this same U.

Source: Aschbacher--Smith, 6.2.11, printed p.686, the paragraph constructing L₀.
This provides the original ambient action; the A₇ recognition and H-star
contradiction are not asserted here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
variable {G : Type*} [Group G] [Finite G] {P : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Every noncentral element of U has exactly Z_S as its fixed subgroup
on the original natural layer. -/
theorem four_closure_element_fixed
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    {u : G} (hu : u ∈ sourceClosure (P : Subgroup G) L R z)
    (hus : u ∉ ZS (P : Subgroup G) L R) :
    layer L R ⊓ centralizer ({u} : Set G) = ZS (P : Subgroup G) L R := by
  let B := layer L R
  let U := sourceClosure (P : Subgroup G) L R z
  let S := ZS (P : Subgroup G) L R
  let C := B ⊓ centralizer (zpowers u : Set G)
  let := h.layer_elementary
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  have hUT : U ≤ (P : Subgroup G) := by
    have hc := pCoreIn_le_sylow (Centralizer z) (P.subtype hP)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hP] at hc
    exact (local_closure_core h hnatural hz ho hP).1.trans hc
  have hUN := (zpowers_le.mpr (hUT hu)).trans h.sylow_normalizes_layer
  have hne : ChapterE.inducedAutomizer B (zpowers u) ≠ ⊥ := by
    intro he
    have hc := (ChapterE.inducedAutomizer_eq_bot_iff hUN).mp he (mem_zpowers u)
    exact hus ((four_closure_centralizer_layer h hnatural hz ho hP hplane hcard).le ⟨hu, hc⟩)
  obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha : (a : ChapterE.Automizer B) ≠ 1 := fun he => hane (Subtype.ext he)
  have hlo := (natural_automizer_fixedCodim_ge hnatural.2.1 hNL ha).trans
    (ChapterE.fixedCodim_mono (ChapterE.automizerRepresentation B) (zpowers_le.mpr a.property))
  rw [ChapterE.fixedCodim_inducedAutomizer B (zpowers u) hUN] at hlo
  have hidx : 4 ≤ C.relIndex B := Nat.pow_le_of_le_log
    (C.subgroupOf B).index_ne_zero_of_finite hlo
  have hSC : S ≤ C := le_inf inf_le_left
    (((ZS_le_sourceClosure_intersection h hz).trans inf_le_left).trans
      (U.le_centralizer.trans (centralizer_le (zpowers_le.mpr hu))))
  have hc := (C.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ B from inf_le_left)).toEquiv,
    hnatural.2.1.card] at hc
  have he : C = S := (eq_of_le_of_card_ge hSC (by
    rw [(h.natural_ZS_geometry hnatural).2.1]
    change Nat.card C * C.relIndex B = 2 ^ (2 * 2) at hc
    norm_num at hc
    nlinarith)).symm
  simpa only [C, B, S, zpowers_eq_closure, centralizer_closure] using he

/-- The involutions of the actual component Sylow lie in its two original
sixteens. No abstract isomorphism or replacement of U is used. -/
theorem four_component_sylow_involutions
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    {x : G} (hx : x ∈ (P : Subgroup G) ⊓ L) (hx2 : x ^ 2 = 1) :
    x ∈ sourceClosure (P : Subgroup G) L R z ∨ x ∈ layer L R := by
  let U := sourceClosure (P : Subgroup G) L R z
  let B := layer L R
  let := h.layer_elementary
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  have hU : U ≤ (P : Subgroup G) ⊓ L := by
    rw [four_component_sylow_eq_sup h hnatural hz ho hP hplane hNL hcard]
    exact le_sup_left
  have hUN : U ≤ normalizer (B : Set G) := (hU.trans inf_le_left).trans h.sylow_normalizes_layer
  have hprod : x ∈ (B : Set G) * (U : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left B U hUN, sup_comm,
      ← four_component_sylow_eq_sup h hnatural hz ho hP hplane hNL hcard]
    exact hx
  obtain ⟨b, hb, u, hu, rfl⟩ := hprod
  by_cases hus : u ∈ ZS (P : Subgroup G) L R
  · exact Or.inr (B.mul_mem hb hus.1)
  · have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b hb
    have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
    have hcomm : b * u = u * b := by
      have hi : (b * u)⁻¹ = b * u := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx2)
      have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb2)
      have hiu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hu2)
      simpa only [mul_inv_rev, hib, hiu] using hi.symm
    have hbs : b ∈ ZS (P : Subgroup G) L R :=
      (four_closure_element_fixed h hnatural hz ho hP hplane hNL hcard hu hus).le
        ⟨hb, mem_centralizer_singleton_iff.mpr hcomm⟩
    exact Or.inl (U.mul_mem ((ZS_le_sourceClosure_intersection h hz).trans inf_le_left hbs) hu)

/-- Every elementary subgroup of T∩L lies in one of the two sixteens. -/
theorem four_component_sylow_elementary_dichotomy
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (P : Subgroup G) ⊓ L) :
    A ≤ sourceClosure (P : Subgroup G) L R z ∨ A ≤ layer L R := by
  let := hA
  apply SubgroupClass.subset_union.mp
  intro a ha
  exact four_component_sylow_involutions h hnatural hz ho hP hplane hNL hcard
    (hAT ha) (elemPow_eq_one_of_isElementaryAbelian a ha)

/-- The actual component Sylow has precisely the two original sixteens
as its maximum elementary subgroups. -/
theorem four_component_sylow_maximum_family
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    Stellmacher.elementaryAbelianMaxSubgroups ((P : Subgroup G) ⊓ L) =
      {sourceClosure (P : Subgroup G) L R z, layer L R} := by
  let := h.layer_elementary
  let := four_closure_elementary h hnatural hz ho hP hplane hcard
  apply Stellmacher.maxFamily_eq_pair_of_cover
  · rw [four_component_sylow_eq_sup h hnatural hz ho hP hplane hNL hcard]
    exact le_sup_left
  · exact le_inf h.layer_le_T h.layer_le_L
  · rw [four_closure_card h hnatural hz ho hP hplane hcard, hnatural.2.1.card]
    decide
  · intro A hA
    exact four_component_sylow_elementary_dichotomy h hnatural hz ho hP hplane hNL hcard A hA.2.1 hA.1

/-- The component Sylow normalizer preserves the original closure, since
it fixes V in its two-member maximum family. -/
theorem four_component_sylow_normalizer_closure
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    L ⊓ normalizer (((P : Subgroup G) ⊓ L : Subgroup G) : Set G) ≤
      normalizer (sourceClosure (P : Subgroup G) L R z : Set G) := by
  let U := sourceClosure (P : Subgroup G) L R z
  let B := layer L R
  have hfamily := four_component_sylow_maximum_family h hnatural hz ho hP hplane hNL hcard
  have hU : U ∈ Stellmacher.elementaryAbelianMaxSubgroups ((P : Subgroup G) ⊓ L) := by
    rw [hfamily]
    exact Set.mem_insert _ _
  obtain ⟨_, _, _, _, _, hm⟩ := hnatural.2.1
  intro g hg
  have hB : B.map (MulAut.conj g).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp (hm.normalizes hg.1)
  have hh := Stellmacher.maxFamily_conj_mem hU hg.2
  simp only [hfamily, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases hh with hh | hh
  · exact hh
  · have he : U = B := (map_injective (MulAut.conj g).injective) (hh.trans hB.symm)
    have hi := (four_intersection_geometry h hnatural hz ho hP hplane hcard).2.2.1
    change B ⊓ U = ZS (P : Subgroup G) L R at hi
    rw [he, inf_idem] at hi
    have hc := congrArg (fun K : Subgroup G => Nat.card K) hi
    rw [hnatural.2.1.card, (h.natural_ZS_geometry hnatural).2.1] at hc
    norm_num at hc

/-- Both generating subgroups in the source L₀ preserve the same original
sixteen, supplying its actual ambient action. -/
theorem four_generated_overgroup_normalizes_closure
    (h : Hypothesis611 KnownSimple.IsKnownSimple P L M R n)
    (hnatural : Conclusion6127 (P : Subgroup G) L M R n)
    (hz : z ∈ ZS (P : Subgroup G) L R) (ho : orderOf z = 2)
    (hP : (P : Subgroup G) ≤ Centralizer z)
    (hplane : normalizer (ZS (P : Subgroup G) L R : Set G) ≤ normalizer (layer L R : Set G))
    (hNL : normalizer (layer L R : Set G) ≤ normalizer (L : Set G))
    (hcard : Nat.card (layer L R ⊓ (Centralizer z).pCoreIn 2 : Subgroup G) = 4) :
    (L ⊓ normalizer (((P : Subgroup G) ⊓ L : Subgroup G) : Set G)) ⊔ Centralizer z ≤
      normalizer (sourceClosure (P : Subgroup G) L R z : Set G) :=
  sup_le (four_component_sylow_normalizer_closure h hnatural hz ho hP hplane hNL hcard)
    (closure_normalized _ _ _ _)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalQuotientAction
