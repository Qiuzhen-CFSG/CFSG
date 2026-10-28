module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SolvableImages
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarLocalTests

/-!
# Closing the constrained containing-component branch of 10.2.6

Apply C.2.7 to the actual strict containing component and the original
R = O₂(L₀T). Its map to the star component has solvable kernel. The complete
star-model tests prove distinctness of the two containing components and
force three to divide the original quotient. The already established
odd-rank contradiction then excludes this branch.

Both factors are treated with their original relative normality, exchanger
and half-join. No cubic divisor is imposed on Suzuki: a three-free original
quotient cannot survive in a small star model, and the other star models
force a cubic in the actual local image. The final application reduces the
literal pair to a strict quasisimple containing component without assuming
distinctness. The quasisimple and zero-kernel normalizer branches and final
assembly remain with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the
sole external source input, discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith C.2.7 and 10.2.6, pp.145--147,748--749.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- The first strict containing component cannot satisfy F*(K) = O₂(K). -/
theorem ContainingPair.first_not_constrained_of_strict
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁) :
    generalizedFitting K₁ ≠ pCore 2 K₁ := by
  intro hf
  let K := K₁.map H.subtype
  let a := K₁.equivMapOfInjective H.subtype H.subtype_injective
  have hmap : K.subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hK : K ∈ cComponentsIn H := ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩
  have hKN : (K.subgroupOf H).Normal := hmap.symm ▸ C.first_normal
  have hBK : L.map (MulAut.conj (1 : G)).toMonoidHom < K := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hstrict
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    simpa only [hid,Subgroup.map_id,map_subgroupOf_eq_of_le C.left_le] using hh
  have hfK : generalizedFitting K = pCore 2 K := by
    have hh := congrArg (Subgroup.map a.toMonoidHom) hf
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hh
  let I := C.c27_input_of_strict hn (one_mem _) hK hKN hBK hfK
  let R := (localJoin T L).pCoreIn 2
  let q := (toStarImage K R).comp a.toMonoidHom
  have hq : Function.Surjective q := (toStarImage_surjective K R).comp a.surjective
  let : Group.IsSolvable (toStarImage K R).ker := toStarImage_ker_solvable_from_source I
  let f : q.ker →* (toStarImage K R).ker :=
    (a.toMonoidHom.comp q.ker.subtype).codRestrict _ (fun x => x.property)
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (f := f)
    (fun x y h => Subtype.ext (a.injective (congrArg Subtype.val h)))
  have ht : (⊤ : Subgroup K₁).IsCComponent := by
    simpa only [subgroupOf_self] using C.first_component.subgroupOf le_rfl
  have hX : (⊤ : Subgroup (starImage K R K)).IsCComponent := by
    simpa only [map_top_of_surjective _ hq] using cComponent_map_of_solvable_ker ht q hq
  obtain ⟨hu,hsmall | hc⟩ := StarModels.sylow_tests (star_model_from_source I) hX
  · exact C.impossible_of_first_small_solvable_image hchoice hmany hn hna q hq hu hsmall
  · exact C.impossible_of_first_solvable_image_local_cubic hchoice hmany hn hna q hq hu hc

/-- The second strict containing component cannot satisfy F*(K) = O₂(K). -/
theorem ContainingPair.second_not_constrained_of_strict
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂) :
    generalizedFitting K₂ ≠ pCore 2 K₂ := by
  intro hf
  let K := K₂.map H.subtype
  let a := K₂.equivMapOfInjective H.subtype H.subtype_injective
  have hmap : K.subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  have hK : K ∈ cComponentsIn H := ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩
  have hKN : (K.subgroupOf H).Normal := hmap.symm ▸ C.second_normal
  have hBK : L.map (MulAut.conj (t : G)).toMonoidHom < K := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hstrict
    simpa only [map_subgroupOf_eq_of_le C.right_le] using hh
  have hfK : generalizedFitting K = pCore 2 K := by
    have hh := congrArg (Subgroup.map a.toMonoidHom) hf
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hh
  let I := C.c27_input_of_strict hn C.t_mem hK hKN hBK hfK
  let R := (localJoin T L).pCoreIn 2
  let q := (toStarImage K R).comp a.toMonoidHom
  have hq : Function.Surjective q := (toStarImage_surjective K R).comp a.surjective
  let : Group.IsSolvable (toStarImage K R).ker := toStarImage_ker_solvable_from_source I
  let f : q.ker →* (toStarImage K R).ker :=
    (a.toMonoidHom.comp q.ker.subtype).codRestrict _ (fun x => x.property)
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (f := f)
    (fun x y h => Subtype.ext (a.injective (congrArg Subtype.val h)))
  have ht : (⊤ : Subgroup K₂).IsCComponent := by
    simpa only [subgroupOf_self] using C.second_component.subgroupOf le_rfl
  have hX : (⊤ : Subgroup (starImage K R K)).IsCComponent := by
    simpa only [map_top_of_surjective _ hq] using cComponent_map_of_solvable_ker ht q hq
  obtain ⟨hu,hsmall | hc⟩ := StarModels.sylow_tests (star_model_from_source I) hX
  · exact C.impossible_of_second_small_solvable_image hchoice hmany hn hna q hq hu hsmall
  · exact C.impossible_of_second_solvable_image_local_cubic hchoice hmany hn hna q hq hu hc

/-- The actual pair now has a strict quasisimple containing component.
No distinctness, model-recognition or C.2.7 premise is added. -/
theorem ContainingPair.exists_strict_quasisimple_component
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    ∃ (s : G) (K : Subgroup G), (s = 1 ∨ s = t) ∧ s ∈ (T : Subgroup G) ∧
      K ∈ cComponentsIn H ∧ (K.subgroupOf H).Normal ∧
      L.map (MulAut.conj s).toMonoidHom < K ∧ IsQuasisimple K := by
  have ho := oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna C.half_le
  rcases C.strict with hs | hs
  · have hfit := C.first_not_constrained_of_strict hchoice hmany hn hna hs
    have hq : IsQuasisimple K₁ := by
      rcases C.first_component.component_or_generalizedFitting_eq_pCore ho with hq | hf
      · exact hq.2
      · exact (hfit hf).elim
    let := hq
    let a := K₁.equivMapOfInjective H.subtype H.subtype_injective
    have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
      comap_map_eq_self_of_injective H.subtype_injective K₁
    refine ⟨1,K₁.map H.subtype,Or.inl rfl,one_mem _,
      ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩,
      hmap.symm ▸ C.first_normal,?_,IsQuasisimple.of_mulEquiv a⟩
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hs
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
    simpa only [hid,Subgroup.map_id,map_subgroupOf_eq_of_le C.left_le] using hh
  · have hfit := C.second_not_constrained_of_strict hchoice hmany hn hna hs
    have hq : IsQuasisimple K₂ := by
      rcases C.second_component.component_or_generalizedFitting_eq_pCore ho with hq | hf
      · exact hq.2
      · exact (hfit hf).elim
    let := hq
    let a := K₂.equivMapOfInjective H.subtype H.subtype_injective
    have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
      comap_map_eq_self_of_injective H.subtype_injective K₂
    refine ⟨t,K₂.map H.subtype,Or.inr rfl,C.t_mem,
      ⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩,
      hmap.symm ▸ C.second_normal,?_,IsQuasisimple.of_mulEquiv a⟩
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hs
    simpa only [map_subgroupOf_eq_of_le C.right_le] using hh

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
