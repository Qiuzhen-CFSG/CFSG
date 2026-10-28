module
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Theory.GroupTheory.CComponent.SimplePairKernel
public import Theory.GroupTheory.ReducedNormal.OrbitReduced
public import Theory.Representation.NormalElementaryQuotient.CentralChief
public import Theory.Representation.BinaryOffender.CubicSection

/-!
# The faithful core quotient of a swapped Fundamental Setup module

The noncentral homogeneous seed prevents either original component from
lying in the local conjugation kernel. Simplicity of the intrinsic core
quotients makes that normal kernel a two-group; reducedness gives equality
with the original two-core. The first isomorphism theorem then identifies
the actual core quotient with the original conjugation image, preserving
the action formula and cubic bound. Its action remains faithful after
removing all fixed vectors.

The original component and its exchanged conjugate remain distinct ordinary
components in this quotient. Their intrinsic quotient markings and normal
join are retained. FaithfulSections applies these results to the remaining
pure-point configuration. The kernel argument generalizes the checked
A₅ proof in Chapter10.SourceA5ActionKernel, using only simple core quotients.
Source: Aschbacher--Smith 3.2.2(8), 10.1.1--2 and 12.1.4,
printed pp.579,741--742,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem local_module_kernel_isTwoGroup
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsPGroup 2 (centralizer
      (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L))) := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let U := D.moduleSubgroup.subgroupOf H
  let C := centralizer (U : Set H)
  have hUH : D.moduleSubgroup ≤ H := D.module_le_core.trans (pCoreIn_le 2 H)
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let : C.Normal := inferInstance
  have hAC : ¬ A ≤ C := by
    intro hc
    have hLC : L ≤ centralizer (D.moduleSubgroup : Set G) := by
      intro l hl v hv
      exact congrArg H.subtype (hc (show (⟨l,hLH hl⟩ : H) ∈ A from hl)
        ⟨v,hUH hv⟩ hv)
    have hOC : localOrbit T L ≤ centralizer (D.moduleSubgroup : Set G) :=
      iSup_conjugates_le_of_le_normalizer L T _ hLC
        (D.sylow_normalizes_module.trans (normalizer_le_normalizer_centralizer _))
    apply D.homogeneous.isIrrPlus.not_le_fixedSpace
      (ReducedNormal.representation H)
    intro w hw x
    have hxc : ((x : H) : G) ∈ centralizer (D.seed : Set G) :=
      (centralizer_le (le_componentOrbit D.seed T)) (hOC x.property)
    exact ReducedNormal.representation_fixes_of_centralizes_subspaceImage
      H D.seedSpace (x : H) hxc w hw
  obtain ⟨t,ht,htn,hpair,_⟩ := Chapter10.source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tH).toMonoidHom from rfl, map_map,
      show H.subtype.comp (MulAut.conj tH).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp H.subtype from rfl, ←map_map, hmapA]
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj tH)
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hp : A ⊔ B = (localOrbit T L).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,map_subgroupOf_eq_of_le le_sup_left,hpair]
  let : (A ⊔ B).Normal := hp ▸ normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  let a : A ≃* L := subgroupOfEquivOfLe hLH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := aq.isSimpleGroup
  let b : A ≃* B := (MulAut.conj tH).subgroupMap A
  let : IsSimpleGroup (B ⧸ pCore 2 B) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.isSimpleGroup
  apply isTwoGroup_of_normal_avoiding_simpleCore_pair A B
    ((T : Subgroup G).subgroupOf H) C hA hB hne T.isPGroup'.comap_subtype
    ?_ hAC ?_
  · rw [hp, ←subgroupOf_sup (show localOrbit T L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right), subgroupOf_self]
  · intro hBC
    apply hAC
    intro a ha
    have hc := hBC (mem_map_of_mem (MulAut.conj tH).toMonoidHom ha)
    have hh := (inferInstance : C.Normal).conj_mem _ hc tH⁻¹
    simpa [MulAut.conj_apply,mul_assoc] using hh

/-- The local conjugation kernel is exactly the original O₂(L₀T). -/
theorem local_module_kernel_eq_twoCore
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) =
      pCore 2 (localJoin T L) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, local_module_kernel_isTwoGroup D hn⟩
  · intro x hx v hv
    exact Subtype.ext (D.core_centralizes_module (mem_map_of_mem H.subtype hx) v hv)

/-- The same original core quotient is the faithful conjugation actor. -/
theorem local_module_action_equiv
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ e : XiQuotient (localJoin T L) ≃*
        ChapterD.internalActionImage (localJoin T L)
          D.moduleSubgroup D.join_normalizes_module,
      ∀ x : localJoin T L,
        (e (QuotientGroup.mk' (pCore 2 (localJoin T L)) x) : MulAut D.moduleSubgroup) =
          ChapterD.UniqueFactor.actionHom (localJoin T L) D.moduleSubgroup
            D.join_normalizes_module x := by
  let H := localJoin T L
  let a := ChapterD.UniqueFactor.actionHom H D.moduleSubgroup D.join_normalizes_module
  have hk : a.ker = pCore 2 H := by
    rw [ChapterD.UniqueFactor.actionHom_ker]
    have hc : (centralizer (D.moduleSubgroup : Set G)).subgroupOf H =
        centralizer (D.moduleSubgroup.subgroupOf H : Set H) := by
      ext x
      constructor
      · intro hx v hv
        exact Subtype.ext (hx v hv)
      · intro hx v hv
        exact congrArg H.subtype (hx ⟨v,D.module_le_core.trans (pCoreIn_le 2 H) hv⟩ hv)
    rw [hc]
    exact local_module_kernel_eq_twoCore D hn
  let e := (QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (ChapterD.UniqueFactor.actionQuotientEquiv H D.moduleSubgroup D.join_normalizes_module)
  refine ⟨e,?_⟩
  intro x
  rfl

/-- The genuine core quotient acts faithfully on the original FSU module,
and still does so after dividing out its full fixed subspace. -/
theorem local_module_faithful_action
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    letI := D.module_elementary
    ∃ ρ : Representation (ZMod 2) (XiQuotient (localJoin T L)) (Additive D.moduleSubgroup),
      Function.Injective ρ ∧ Function.Injective (fixedQuotient ρ ⊤) ∧
      (∀ (x : localJoin T L) (v : D.moduleSubgroup),
        (ρ (QuotientGroup.mk' (pCore 2 (localJoin T L)) x) (Additive.ofMul v)).toMul =
          ⟨(x : G) * v * (x : G)⁻¹,
            (D.join_normalizes_module x.property v).mp v.property⟩) ∧
      (cubicRatio (ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
        D.moduleSubgroup D.join_normalizes_module) ≤ 2 → cubicRatio ρ ≤ 2) := by
  let := D.module_elementary
  obtain ⟨e,he⟩ := local_module_action_equiv D hn
  let τ := ChapterD.UniqueFactor.imageRepresentation (localJoin T L)
    D.moduleSubgroup D.join_normalizes_module
  let ρ := τ.comp e.toMonoidHom
  have hf : Function.Injective ρ :=
    (ChapterD.UniqueFactor.imageRepresentation_injective _ _ _).comp e.injective
  refine ⟨ρ,hf,faithful_fixedQuotient_of_core ρ hf (pCore_quotient_pCore_eq_bot 2),?_,?_⟩
  · intro x v
    change (e (QuotientGroup.mk' (pCore 2 (localJoin T L)) x)).val v = _
    rw [he]
    rfl
  · intro hc
    exact cubicRatio_comp_equiv_le_nat τ e 2 hc

include D

/-- The original component embeds as an ordinary component of the faithful
core quotient, with its intrinsic quotient marking preserved. -/
theorem local_quotient_original_component :
    let H := localJoin T L
    let q := QuotientGroup.mk' (pCore 2 H)
    IsComponent (XiQuotient H) ((L.subgroupOf H).map q) ∧
      Nonempty (((L.subgroupOf H).map q) ≃* XiQuotient L) := by
  let H := localJoin T L
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a : A ≃* L := subgroupOfEquivOfLe hLH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let eqt := cComponentTwoCoreQuotientEquiv hA
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  exact ⟨⟨hA.subnormal.map (QuotientGroup.mk'_surjective _),
    IsQuasisimple.of_mulEquiv eqt⟩,⟨eqt.symm.trans aq⟩⟩

/-- The second original component remains distinct after removing the actual core. -/
theorem local_quotient_component_pair
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let H := localJoin T L
    let q := QuotientGroup.mk' (pCore 2 H)
    let A := (L.subgroupOf H).map q
    ∃ t : H, (t : G) ∈ T ∧ (t : G) ∉ normalizer (L : Set G) ∧
      let B := A.map (MulAut.conj (q t)).toMonoidHom
      IsComponent (XiQuotient H) A ∧ IsComponent (XiQuotient H) B ∧ A ≠ B ∧
      Nonempty (A ≃* XiQuotient L) ∧ Nonempty (B ≃* XiQuotient L) ∧
      (A ⊔ B).Normal ∧
      A ⊔ B = ((localOrbit T L).subgroupOf H).map q := by
  let H := localJoin T L
  let q := QuotientGroup.mk' (pCore 2 H)
  let A₀ := L.subgroupOf H
  let A := A₀.map q
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨t,ht,htn,hpair,_⟩ := Chapter10.source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B₀ := A₀.map (MulAut.conj tH).toMonoidHom
  let B := A.map (MulAut.conj (q tH)).toMonoidHom
  have hmapA : A₀.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B₀.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B₀ = A₀.map (MulAut.conj tH).toMonoidHom from rfl,map_map,
      show H.subtype.comp (MulAut.conj tH).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hA₀ : A₀.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hB₀ : B₀.IsCComponent := hA₀.map_equiv (MulAut.conj tH)
  have hne₀ : A₀ ≠ B₀ := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hBq : B₀.map q = B := by
    rw [show B₀ = A₀.map (MulAut.conj tH).toMonoidHom from rfl,map_map]
    change A₀.map (q.comp (MulAut.conj tH).toMonoidHom) =
      (A₀.map q).map (MulAut.conj (q tH)).toMonoidHom
    rw [map_map]
    congr 1
  have hp : A₀ ⊔ B₀ = (localOrbit T L).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,map_subgroupOf_eq_of_le le_sup_left,hpair]
  have hpq : A ⊔ B = ((localOrbit T L).subgroupOf H).map q := by
    rw [←hBq,←Subgroup.map_sup,hp]
  have hnO : ((localOrbit T L).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer
      (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  obtain ⟨hA,⟨eA⟩⟩ := local_quotient_original_component D
  refine ⟨tH,ht,htn,hA,hA.map_conj (q tH),?_,⟨eA⟩,
    ⟨((MulAut.conj (q tH)).subgroupMap A).symm.trans eA⟩,?_,hpq⟩
  · intro he
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact hne₀ (hA₀.eq_of_map_quotient_eq hB₀ (pCore 2 H) (he.trans hBq.symm))
  · rw [hpq]
    exact Normal.map hnO q (QuotientGroup.mk'_surjective _)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
