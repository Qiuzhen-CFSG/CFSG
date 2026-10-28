module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinarySolvableBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Linear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Solvable

/-!
# The original ordinary linear-three marked intersection is its Borel

The original seed gives a nontrivial Sylow-central involution of the same
ordinary component. Native fixed-group solvability, through the retained
central cover, makes its marked intersection solvable. Native solvable
Sylow control and the actual local residual-normalizer bounds then identify
that intersection with its full Borel, before global residual normalization.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem raw_ordinary_fixed_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (hfaith : centralInvolutions T ⊓ centralizer (L : Set G) = ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hf : ∀ (P : Sylow 2 L) (a : MulAut L), orderOf a = 2 →
      (∀ x ∈ P, a x = x) → Group.IsSolvable a.fixedSubgroup) :
    Group.IsSolvable ((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L : Subgroup G) := by
  let ML := (centralizer (Z1 : Set G) ⊓ Mc) ⊓ L
  obtain ⟨z,hz,hzne⟩ := (bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  let α := L.normalizerMonoidHom ⟨z,hnZ hz⟩
  have ha (x : L) : (α x : G) = z*x*z⁻¹ := rfl
  obtain ⟨P,hP⟩ := hSyl
  have hfix : ∀ x ∈ P, α x = x := by
    intro x hx
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (centralInvolutions_le_centralizer_sylow T hz x
        ((hP ▸ mem_map_of_mem L.subtype hx).1).1).symm
  have hz2 : z*z=1 := by
    have hh := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    simpa only [pow_two] using hh.2.1
  have hα2 : α^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (α (α x) : G) = x
    rw [ha,ha]
    calc
      z*(z*(x:G)*z⁻¹)*z⁻¹ = (z*z)*x*(z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hαne : α ≠ 1 := by
    intro he
    have hc : z ∈ centralizer (L : Set G) := by
      intro x hx
      have hh := ha (⟨x,hx⟩ : L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    exact hzne (mem_bot.mp (hfaith ▸ ⟨hz,hc⟩))
  let : Group.IsSolvable α.fixedSubgroup := hf P α (orderOf_eq_prime hα2 hαne) hfix
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro x hx
    exact hMc.2 (fun w hw => (centralInvolutions_le_centralizer_sylow T hw x hx).symm)
  have hres := residual_le_centralizer_Z
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1,hTMc⟩
  let j : ML →* Mc := inclusion (show ML ≤ Mc from inf_le_left.trans inf_le_right)
  let f : solvableResidual ML →* α.fixedSubgroup := {
    toFun x := ⟨⟨x.val.val,x.val.property.2⟩,by
      rw [MulAut.mem_fixedSubgroup]
      apply Subtype.ext
      rw [ha]
      have hc := hres (mem_map_of_mem Mc.subtype
        (map_solvableResidual_le j (mem_map_of_mem j x.property))) z hz
      exact mul_inv_eq_iff_eq_mul.mpr hc⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun a : α.fixedSubgroup => ((a : L) : G)) hxy))
  let : Group.IsSolvable (solvableResidual ML) :=
    Group.isSolvable_of_isSolvable_injective hinj
  exact (Group.isSolvable_iff_subgroup_quotient (solvableResidual ML)).mpr
    ⟨inferInstance,inferInstance⟩

/-- The actual higher-field linear-three quotient identifies the same marked
intersection with its full Borel, using the original local controls. -/
theorem PreparedChosenModule.raw_ordinary_linearThree_borel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (hfaith : centralInvolutions T ⊓ centralizer (L : Set G) = ⊥)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hcontrol : ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2).characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 (centralizer (Z1 : Set G) ⊓ Mc : Subgroup G)).map
      (centralizer (Z1 : Set G) ⊓ Mc).subtype : Set G) ≤ Mc)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    ((centralizer (Z1 : Set G) ⊓ Mc) ⊓ L) =
      (normalizer ((((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L).subgroupOf L : Set L)).map
        L.subtype := by
  let := h.elementary
  let H := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ H
  let B := (normalizer ((S ⊓ L).subgroupOf L : Set L)).map L.subtype
  let : IsQuasisimple (L.subgroupOf H) := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLG)
  let ec := (QuotientGroup.quotientMulEquivOfEq hcenter).trans e
  have hsol : Group.IsSolvable ((H ⊓ Mc) ⊓ L : Subgroup G) := by
    apply raw_ordinary_fixed_solvable hG T hempty hM hu hnZ hfaith hSylL
    intro P a ha hfix
    apply MulAut.fixed_solvable_of_centralQuotient ec _ P a ha hfix
    intro Q b hb hQ
    apply Matrix.PSL3.LinearThree.sylow_fixed_solvable F (by omega) hF Q b _ hQ
    intro he
    rw [he,orderOf_one] at hb
    omega
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hc : SolvableSylowControl 2 L := SolvableSylowControl.of_surjective_pKernel f hf hk
    (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le F (by omega) hF)
  have hB : HasCharacteristicTwo B := by
    obtain ⟨P,hP⟩ := hSylL
    have hP' : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
      apply map_injective L.subtype_injective
      rw [hP,map_subgroupOf_eq_of_le inf_le_right]
    let B0 := normalizer (P : Set L)
    have hb : HasCharacteristicTwo B0 := by
      apply f.centralizer_pCore_subgroup_of_image hk
      rw [P.normalizer_map_surjective f hf]
      exact Matrix.PSL3.LinearThree.BorelStructure.sylowNormalizer_core_selfCentralizing
        F (by omega) hF (P.mapSurjective hf)
    have he : B0.map L.subtype = B := by
      change (normalizer ((P : Subgroup L) : Set L)).map _ = _
      rw [hP']
    exact hb.of_equiv ((B0.equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr he))
  have hSM : S ≤ H ⊓ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨hx.2,hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz x hx.1).symm)⟩
  exact raw_ordinary_solvable_borel_eq H Mc S L
    (caseI_centralizer_sqtk hG Z1 hZne ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left)))
    hSM (T.isPGroup'.to_le inf_le_left) hSylG hLG hL hSylL hcontrol hbound hsol hc hB

end CFSG.Quasithin.Chapter15.Section01
