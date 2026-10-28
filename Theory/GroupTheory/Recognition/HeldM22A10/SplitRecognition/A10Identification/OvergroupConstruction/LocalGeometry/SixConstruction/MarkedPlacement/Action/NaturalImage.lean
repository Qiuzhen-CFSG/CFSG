module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Action.Kernel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Membership
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.MarkedPlacement.Fusion
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# The natural symmetric image of the supplied A₆

The marked involutions lambda and mu-prime fix Klein four-groups in the
supplied A₆. An exceptional involution of Aut(A₆) has fixed subgroup of
order ten, so these two actions belong to the natural S₆. The centralizer
decomposition puts its entire action in that S₆. The faithful extension
A<mu-prime> has order 720 and hence maps onto it. The full action has kernel
of order four, identified with the actual ambient centralizer of A in C_G(mu).

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 4.2, pp.234–235. The exceptional fixed
subgroup theorem is GLS, Volume 3, Proposition 5.2.7(a).
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

open AlternatingSix.ShadowLocal GLS3.Chapter5

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G)))

/-- The full centralizer acts on the actual alternating carrier. -/
@[expose] public noncomputable def sectionFullAction :
    centralizer ({mu D e} : Set G) →* AutA6 :=
  (MulAut.congr s.ambientAlternatingEquiv).toMonoidHom.comp
    (s.ambientSubgroup.normalizerMonoidHom.comp
      (inclusion s.le_normalizer_ambientSubgroup))

/-- Transport of the extension action through the supplied A₆ equivalence. -/
@[expose] public noncomputable def sectionAlternatingAction :
    sectionExtension D e s →* AutA6 :=
  (MulAut.congr s.ambientAlternatingEquiv).toMonoidHom.comp (sectionAction D e s)

private theorem fullAction_apply (x : centralizer ({mu D e} : Set G))
    (a : s.ambientSubgroup) :
    sectionFullAction D e s x (s.ambientAlternatingEquiv a) =
      s.ambientAlternatingEquiv
        ⟨(x : G) * (a : G) * (x : G)⁻¹,
          (s.le_normalizer_ambientSubgroup x.property a).mp a.property⟩ := by
  simp only [sectionFullAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private theorem fullAction_inner (a : s.ambientSubgroup) :
    sectionFullAction D e s ⟨a, s.ambientSubgroup_le a.property⟩ =
      MulAut.conj (s.ambientAlternatingEquiv a) := by
  ext b : 1
  obtain ⟨b, rfl⟩ := s.ambientAlternatingEquiv.surjective b
  rw [fullAction_apply]
  change s.ambientAlternatingEquiv (a * b * a⁻¹) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

private theorem natural_of_fixed_four (β : AutA6) (hβ : β ^ 2 = 1)
    (F : Subgroup A6) (hF : Nat.card F = 4)
    (hfix : F ≤ automorphismFixedSubgroup β) : β ∈ natural := by
  by_cases h1 : β = 1
  · exact h1 ▸ natural.one_mem
  by_contra hn
  have hc := outside_natural_involution_fixed_card β (orderOf_eq_prime hβ h1) hn
  have hd := card_dvd_of_le hfix
  rw [hF, hc] at hd
  norm_num at hd

private theorem fullAction_natural_of_four
    (x : centralizer ({mu D e} : Set G)) (hx : (x : G) ^ 2 = 1)
    (F : Subgroup G) (hFA : F ≤ s.ambientSubgroup) (hF : Nat.card F = 4)
    (hFx : F ≤ centralizer ({(x : G)} : Set G)) :
    sectionFullAction D e s x ∈ natural := by
  let F' := (F.subgroupOf s.ambientSubgroup).map s.ambientAlternatingEquiv.toMonoidHom
  refine natural_of_fixed_four _ ?_ F' ?_ ?_
  · rw [← map_pow]
    have hx' : x ^ 2 = 1 := Subtype.ext hx
    rw [hx', map_one]
  · dsimp only [F']
    rw [card_map_of_injective s.ambientAlternatingEquiv.injective,
      Nat.card_congr (subgroupOfEquivOfLe hFA).toEquiv, hF]
  · rintro _ ⟨a, ha, rfl⟩
    change sectionFullAction D e s x (s.ambientAlternatingEquiv a) =
      s.ambientAlternatingEquiv a
    rw [fullAction_apply]
    apply congrArg s.ambientAlternatingEquiv
    apply Subtype.ext
    have hc := mem_centralizer_singleton_iff.mp (hFx ha)
    change (x : G) * (a : G) * (x : G)⁻¹ = (a : G)
    change (a : G) * (x : G) = (x : G) * (a : G) at hc
    rw [← hc, mul_inv_cancel_right]

private def fixedSecond (i : Fin 2) : CentralizerModels.a10Centralizer :=
  if i = 0 then modelElement 3 * modelElement 6 else modelElement 2 * modelElement 7

private def fixedActor (i : Fin 2) : CentralizerModels.a10Centralizer :=
  if i = 0 then modelElement 6 else modelElement 2

private def modelFixedFour (i : Fin 2) : Subgroup CentralizerModels.a10Centralizer :=
  closure ({modelElement 0 * modelElement 1, fixedSecond i} : Set _)

private theorem modelFixedFour_card (i : Fin 2) : Nat.card (modelFixedFour i) = 4 := by
  let : IsKleinFour (modelFixedFour i) := by
    apply isKleinFour_closure_pair
    · decide +kernel
    · fin_cases i <;> decide +kernel
    · decide +kernel
    · fin_cases i <;> decide +kernel
    · fin_cases i <;> decide +kernel
    · change _ * _ = _ * _
      fin_cases i <;> decide +kernel
  exact IsKleinFour.card_four

private theorem modelFixedFour_centralizes (i : Fin 2) :
    modelFixedFour i ≤ centralizer ({fixedActor i} : Set _) := by
  apply (closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · apply mem_centralizer_singleton_iff.mpr
    fin_cases i <;> decide +kernel
  · have he := Set.mem_singleton_iff.mp hx
    subst x
    apply mem_centralizer_singleton_iff.mpr
    fin_cases i <;> decide +kernel

private theorem fixedActor_commutes_mu (i : Fin 2) :
    fixedActor i * modelElement 1 = modelElement 1 * fixedActor i := by
  fin_cases i <;> decide +kernel

private theorem markedAction_natural (i : Fin 2)
    (hsecond : D.a10ModelEmbedding e (fixedSecond i) ∈ s.ambientSubgroup) :
    sectionFullAction D e s
      ⟨D.a10ModelEmbedding e (fixedActor i), by
        apply mem_centralizer_singleton_iff.mpr
        simpa only [map_mul, element] using
          congrArg (D.a10ModelEmbedding e) (fixedActor_commutes_mu i)⟩ ∈ natural := by
  let f := D.a10ModelEmbedding e
  refine fullAction_natural_of_four D e s _ ?_ ((modelFixedFour i).map f) ?_ ?_ ?_
  · have hs : fixedActor i ^ 2 = 1 := by fin_cases i <;> decide +kernel
    simpa only [map_pow, map_one] using congrArg f hs
  · rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · change f (modelElement 0 * modelElement 1) ∈ s.ambientSubgroup
      simpa only [map_mul, f, element] using pi_mu_mem_section D e s
    · have he := Set.mem_singleton_iff.mp hx
      subst x
      exact hsecond
  · rw [card_map_of_injective (D.a10ModelEmbedding_injective e), modelFixedFour_card]
  · rintro _ ⟨a, ha, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f
      (mem_centralizer_singleton_iff.mp (modelFixedFour_centralizes i ha))

/-- Both marked fixed four-groups force the full centralizer action to be natural. -/
public theorem sectionFullAction_range_le_natural
    (ht : tau D e * lam D e ∈ s.ambientSubgroup)
    (hs : mu' D e * xi D e ∈ s.ambientSubgroup) :
    (sectionFullAction D e s).range ≤ natural := by
  let C := centralizer ({mu D e} : Set G)
  let f := sectionFullAction D e s
  let N := (natural.comap f).map C.subtype
  have hin (x : C) (hx : f x ∈ natural) : (x : G) ∈ N := ⟨x, hx, rfl⟩
  have hC : C ≤ N := by
    change centralizer ({mu D e} : Set G) ≤ N
    rw [section_centralizer_decomposition D e s]
    apply sup_le
    · apply sup_le
      · apply (closure_le _).mpr
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · apply hin ⟨mu D e, mem_centralizer_singleton_iff.mpr rfl⟩
          have he : f ⟨mu D e, mem_centralizer_singleton_iff.mpr rfl⟩ = 1 := by
            ext a : 1
            obtain ⟨a, rfl⟩ := s.ambientAlternatingEquiv.surjective a
            rw [fullAction_apply]
            change s.ambientAlternatingEquiv _ = s.ambientAlternatingEquiv a
            apply congrArg s.ambientAlternatingEquiv
            apply Subtype.ext
            change mu D e * (a : G) * (mu D e)⁻¹ = (a : G)
            have hc : (a : G) * mu D e = mu D e * (a : G) :=
              mem_centralizer_singleton_iff.mp (s.ambientSubgroup_le a.property)
            rw [← hc, mul_inv_cancel_right]
          rw [he]
          exact natural.one_mem
        · have he := Set.mem_singleton_iff.mp hx
          subst x
          apply hin ⟨lam D e, mem_centralizer_singleton_iff.mpr (mu_commute_lam D e).symm.eq⟩
          exact markedAction_natural D e s 0 (by simpa only [fixedSecond, ↓reduceIte, map_mul, element] using ht)
      · intro a ha
        apply hin ⟨a, s.ambientSubgroup_le ha⟩
        rw [fullAction_inner D e s ⟨a, ha⟩]
        exact inner_le_natural ⟨s.ambientAlternatingEquiv ⟨a, ha⟩, rfl⟩
    · apply zpowers_le.mpr
      apply hin ⟨mu' D e, mem_centralizer_singleton_iff.mpr (mu_commute_mu' D e).symm.eq⟩
      exact markedAction_natural D e s 1 (by simpa only [fixedSecond, show (1 : Fin 2) ≠ 0 by decide,
        ↓reduceIte, map_mul, element] using hs)
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy, he⟩ := hC x.property
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy


/-- Mu-prime is outside the supplied A₆: conjugating it by lambda would
otherwise put mu in A₆. -/
public theorem mu'_not_mem_section : mu' D e ∉ s.ambientSubgroup := by
  intro hm
  have hl : lam D e ∈ normalizer (s.ambientSubgroup : Set G) :=
    s.le_normalizer_ambientSubgroup
      (mem_centralizer_singleton_iff.mpr (mu_commute_lam D e).symm.eq)
  have hconj : lam D e * mu' D e * (lam D e)⁻¹ = mu D e * mu' D e := by
    have hmodel : modelElement 6 * modelElement 2 * (modelElement 6)⁻¹ =
        modelElement 1 * modelElement 2 := by decide +kernel
    simpa only [map_mul, map_inv, element] using congrArg (D.a10ModelEmbedding e) hmodel
  have hc := (hl (mu' D e)).mp hm
  rw [hconj] at hc
  exact mu_not_mem_section D e s (by
    simpa only [mul_inv_cancel_right] using s.ambientSubgroup.mul_mem hc
      (s.ambientSubgroup.inv_mem hm))

private theorem extension_le_centralizer :
    sectionExtension D e s ≤ centralizer ({mu D e} : Set G) :=
  sup_le s.ambientSubgroup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mu_commute_mu' D e).symm.eq))

private theorem alternatingAction_eq_full (x : sectionExtension D e s) :
    sectionAlternatingAction D e s x =
      sectionFullAction D e s ⟨x, extension_le_centralizer D e s x.property⟩ := rfl

private theorem alternatingAction_range_le_full :
    (sectionAlternatingAction D e s).range ≤ (sectionFullAction D e s).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x, extension_le_centralizer D e s x.property⟩,
    (alternatingAction_eq_full D e s x).symm⟩

/-- The actual extension has index two over A₆ and order 720. -/
public theorem sectionExtension_card [Finite G] : Nat.card (sectionExtension D e s) = 720 := by
  have hi : (s.ambientSubgroup.subgroupOf (sectionExtension D e s)).index = 2 := by
    apply relIndex_eq_two_iff_exists_notMem_and.mpr
    refine ⟨mu' D e, mem_sup_right (mem_zpowers _), mu'_not_mem_section D e s, ?_⟩
    intro x hx
    obtain ⟨a, ha, j, rfl⟩ := sectionExtension_cosets D e s x hx
    fin_cases j
    · exact Or.inr (by simpa only [Fin.val_zero, pow_zero, mul_one] using ha)
    · apply Or.inl
      simpa only [Fin.val_one, pow_one, mul_assoc, ← pow_two,
        element_square D e 2 (by decide), mul_one] using ha
  have hc : Nat.card (s.ambientSubgroup.subgroupOf (sectionExtension D e s)) = 360 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show s.ambientSubgroup ≤ sectionExtension D e s from le_sup_left)).toEquiv,
      Nat.card_congr s.ambientAlternatingEquiv.toEquiv]
    exact card_A6
  rw [← (s.ambientSubgroup.subgroupOf (sectionExtension D e s)).index_mul_card, hi, hc]

/-- Faithfulness identifies the actual extension image with the natural S₆. -/
public theorem sectionAlternatingAction_range_eq_natural [Finite G]
    (ht : tau D e * lam D e ∈ s.ambientSubgroup)
    (hs : mu' D e * xi D e ∈ s.ambientSubgroup)
    (hfaith : Function.Injective (sectionAction D e s)) :
    (sectionAlternatingAction D e s).range = natural := by
  have hf : Function.Injective (sectionAlternatingAction D e s) :=
    (MulAut.congr s.ambientAlternatingEquiv).injective.comp hfaith
  apply Subgroup.eq_of_le_of_card_ge
    ((alternatingAction_range_le_full D e s).trans
      (sectionFullAction_range_le_natural D e s ht hs))
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    sectionExtension_card D e s, card_natural]

/-- The full centralizer has the same image as its faithful supplied extension. -/
public theorem sectionFullAction_range_eq_natural [Finite G]
    (ht : tau D e * lam D e ∈ s.ambientSubgroup)
    (hs : mu' D e * xi D e ∈ s.ambientSubgroup)
    (hfaith : Function.Injective (sectionAction D e s)) :
    (sectionFullAction D e s).range = natural := by
  apply le_antisymm (sectionFullAction_range_le_natural D e s ht hs)
  rw [← sectionAlternatingAction_range_eq_natural D e s ht hs hfaith]
  exact alternatingAction_range_le_full D e s

/-- The kernel is the ambient centralizer intersected with the acting group;
no ambient normality of the A₆ is asserted. -/
public theorem sectionFullAction_ker :
    (sectionFullAction D e s).ker =
      (sectionCentralizer D e s).subgroupOf (centralizer ({mu D e} : Set G)) := by
  rw [sectionFullAction, MonoidHom.ker_comp_of_injective _ _
    (MulAut.congr s.ambientAlternatingEquiv).injective]
  ext x
  change s.ambientSubgroup.normalizerMonoidHom
      (inclusion s.le_normalizer_ambientSubgroup x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  change (x : G) ∈ centralizer (s.ambientSubgroup : Set G) ↔
    (x : G) ∈ centralizer ({mu D e} : Set G) ⊓ centralizer (s.ambientSubgroup : Set G)
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

/-- Held's symmetric extension and the order of its full centralizing kernel,
conditional only on the two marked memberships and the faithful section action. -/
public theorem section_extension_and_centralizer_card_of_faithful [Finite G]
    (ht : tau D e * lam D e ∈ s.ambientSubgroup)
    (hs : mu' D e * xi D e ∈ s.ambientSubgroup)
    (hfaith : Function.Injective (sectionAction D e s)) :
    Nonempty (sectionExtension D e s ≃* Equiv.Perm (Fin 6)) ∧
      Nat.card (sectionCentralizer D e s) = 4 := by
  have hf : Function.Injective (sectionAlternatingAction D e s) :=
    (MulAut.congr s.ambientAlternatingEquiv).injective.comp hfaith
  constructor
  · exact ⟨(MonoidHom.ofInjective hf).trans
      ((MulEquiv.subgroupCongr (sectionAlternatingAction_range_eq_natural D e s ht hs hfaith)).trans
        permSixMulEquivNaturalAlternatingAutomorphisms.symm)⟩
  · have hc : Nat.card (centralizer ({mu D e} : Set G)) = 2880 := s.card
    have h := (sectionFullAction D e s).ker.card_mul_index
    rw [index_ker, sectionFullAction_range_eq_natural D e s ht hs hfaith, card_natural,
      hc, sectionFullAction_ker,
      Nat.card_congr (subgroupOfEquivOfLe
        (show sectionCentralizer D e s ≤ centralizer ({mu D e} : Set G) from inf_le_left)).toEquiv] at h
    omega

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
