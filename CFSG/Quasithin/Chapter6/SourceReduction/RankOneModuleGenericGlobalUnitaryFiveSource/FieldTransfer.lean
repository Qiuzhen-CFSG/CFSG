module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Thompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedAction
public import Theory.GroupTheory.IrreducibleNormalizerCore
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.CyclicQuotientInvolutionTransfer
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# Cyclic field transfer for the prepared unitary-five row

The literal Hermitian module makes the plane-core center irreducible under
L. The two-core of LT therefore centralizes that center; the native
two-element square-map calculation puts this two-core inside O₂(L).
Consequently the field action of the full original Sylow subgroup on the
actual quotient L/O₂(L) has exactly the original S as kernel. Its index
divides the field degree four. Generalized Thompson transfer in the original
nonabelian simple group puts every ambient involution into S.

The other endpoint's SU₃(4) quotient is not used as a PSL₂ quotient. Both
comparison orientations and the whole residual are retained. These results
feed the literal chosen-module application and the remaining ambient fusion
argument; they assert neither S=T nor full ambient centralizer containment.
Source: Aschbacher–Smith F.4.35–38 and 5.3.3, printed pp.292–294,659
(`refs/quasithin.pdf`), using the generalized Thompson transfer theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc

/-- Every L-invariant subgroup of the actual plane-core center is trivial
or the whole center, by the literal Hermitian module. -/
theorem Preparation.unitaryFive_plane_center_irreducible
    (E : Subgroup G)
    (hEZ : E ≤ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hLE : L ≤ normalizer (E : Set G)) :
    E = ⊥ ∨ E = (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype := by
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  obtain ⟨e,f,hf⟩ := d.unitaryFive_plane_center_hermitian_model h hH hp U hc
  let B := (E.subgroupOf Z).map f.toMonoidHom
  have hb : ∀ g x, x ∈ B → multiplicativeAction 2 g x ∈ B := by
    rintro g _ ⟨v,hv,rfl⟩
    obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
    let w := f.symm (multiplicativeAction 2 g (f v))
    have hw : w.val = (l : G)*v.val*(l : G)⁻¹ := by
      have hh := hf l v
      change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
      rw [hl] at hh
      exact hh
    refine ⟨w,?_,f.apply_symm_apply _⟩
    change w.val ∈ E
    rw [hw]
    exact (mem_normalizer_iff.mp (hLE l.property) v.val).mp hv
  rcases multiplicativeAction_irreducible 2 B hb with he | he
  · left
    apply E.eq_bot_iff_forall.mpr
    intro x hx
    have hm : f ⟨x,hEZ hx⟩ ∈ B := mem_map_of_mem f.toMonoidHom hx
    rw [he,mem_bot] at hm
    exact congrArg Subtype.val (f.injective (hm.trans f.map_one.symm))
  · right
    apply le_antisymm hEZ
    intro x hx
    have hm : f ⟨x,hx⟩ ∈ B := he ▸ mem_top _
    obtain ⟨v,hv,hvx⟩ := hm
    have heq : v.val = x := congrArg Subtype.val (f.injective hvx)
    exact heq ▸ (show v.val ∈ E from hv)

/-- The two-core of the original join LT lies in L. Irreducibility first
puts it in the center-action kernel, then the native two-element calculation
puts it in the two-core of the full normalizer. -/
theorem Preparation.unitaryFive_sylow_join_core_le :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ L := by
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  let M := normalizer (L : Set G)
  let Y := L ⊔ (T : Subgroup G)
  have hYN : Y ≤ M := sup_le L.le_normalizer h.sylow_normalizes
  have hnorm : M = normalizer (Z : Set G) :=
    (d.unitaryFive_core_center_normalizers h hH hp U hc 0).symm
  have hz : Y.pCoreIn 2 ≤ centralizer (Z : Set G) :=
    pCoreIn_le_centralizer_of_irreducible Z L Y
      (((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map
        (L.pCoreIn 2).subtype).isPGroup
      ((map_subtype_le _).trans ((pCoreIn_le 2 L).trans le_sup_left))
      (hYN.trans_eq hnorm) le_sup_left
      (d.unitaryFive_plane_center_irreducible h hH hp U hc)
  have hloc := d.unitaryFive_normalizer_local_conditions h hH hp U hc
  have hcore : M.pCoreIn 2 = L.pCoreIn 2 := hloc.twoCore_left
  let ec : pCore 2 M ≃* L.pCoreIn 2 :=
    ((pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hcore)
  have hep : Nonempty (L.pCoreIn 2 ≃* PlaneCore.Parameters U.form) := by
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    obtain ⟨hr⟩ := hr
    obtain ⟨_,⟨e⟩,_⟩ := d.unitaryFive_local_structure h hH.1.1.2 hp U hr
    exact ⟨((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
      ((LocalCoreTransport.coreEquiv 2 e).trans U.rightLocalImageCoreParameters)⟩
  obtain ⟨ep⟩ := hep
  intro x hx
  let r : M := ⟨x,hYN (pCoreIn_le 2 Y hx)⟩
  obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 Y).exists_pow_pow_eq_one ⟨x,hx⟩
  have hr : r^(2^k) = 1 := Subtype.ext (congrArg (fun v : Y.pCoreIn 2 => v.val) hk)
  have hrz : r ∈ centralizer ((center (pCore 2 M)).map (pCore 2 M).subtype : Set M) := by
    rintro _ ⟨z,hz',rfl⟩
    apply Subtype.ext
    exact hz hx z.val.val ⟨ec z,(centerCongr ec ⟨z,hz'⟩).property,rfl⟩
  have hrQ := PlaneCore.twoElement_mem_core_of_center_centralizing U.form (ec.trans ep)
    U.rightLeviTrace U.rightLeviTrace_spec
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hloc.fitting_left) r k hr hrz
  have hxQ : x ∈ M.pCoreIn 2 := ⟨r,hrQ,rfl⟩
  rw [hcore] at hxQ
  exact pCoreIn_le 2 L hxQ


omit d h hH hp hc in
/-- The field component of the action of the full Sylow subgroup on the
actual left PSL₂ quotient. -/
@[expose] def unitaryFiveSylowFieldAction
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) : T →* (F ≃+* F) :=
  (Theory.PSL2.fieldProjection F).comp ((MulAut.congr e).toMonoidHom.comp
    ((pCoreJoinAction 2 hTL).comp (inclusion le_sup_right)))

omit d h hH hp hc [Finite G] in
private theorem plane_quotient_action_inner_iff
    {K V : Subgroup G} (hVK : V ≤ normalizer (K : Set G))
    (hV : IsPGroup 2 V) (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hcore : (K ⊔ V : Subgroup G).pCoreIn 2 ≤ K)
    (x : (K ⊔ V : Subgroup G)) :
    pCoreJoinAction 2 hVK x ∈ MulAut.innerSubgroup (K ⧸ pCore 2 K) ↔ x.val ∈ K := by
  let f := pCoreJoinAction 2 hVK
  constructor
  · rintro ⟨z,hzinner⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) z
    have he : f (inclusion le_sup_left k) = f x :=
      (pCoreJoinAction_on_component 2 hVK k).trans hzinner
    have hx : x * (inclusion le_sup_left k)⁻¹ ∈ f.ker := by
      change f (x * (inclusion le_sup_left k)⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [pCoreJoinAction_kernel 2 hVK hV hz] at hx
    have hk := hcore (mem_map_of_mem (K ⊔ V).subtype hx)
    have hh := K.mul_mem hk k.property
    change (x.val * k.val⁻¹) * k.val ∈ K at hh
    simpa only [inv_mul_cancel_right] using hh
  · intro hx
    let k : K := ⟨x.val,hx⟩
    have he : inclusion (show K ≤ K ⊔ V from le_sup_left) k = x := Subtype.ext rfl
    rw [←he,pCoreJoinAction_on_component]
    exact ⟨_,rfl⟩

/-- The actual left quotient field action has precisely the original source S
as kernel; the SU₃ quotient on the other endpoint is not substituted for it. -/
theorem Preparation.unitaryFive_sylow_field_kernel
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    (unitaryFiveSylowFieldAction h.sylow_normalizes e).ker =
      (sourceS L H).subgroupOf (T : Subgroup G) := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [center_map_equiv,Subgroup.map_bot]
    apply bot_unique
    intro x hx
    apply Theory.PSL2.psl2_conj_eq_one_implies x
    ext y
    change x*y*x⁻¹=y
    rw [←mem_center_iff.mp hx y,mul_inv_cancel_right]
  have hs := d.unitaryFive_sourceS_eq h hH.1.1.2 hp U hc
  ext t
  change Theory.PSL2.fieldProjection F
    ((MulAut.congr e) (pCoreJoinAction 2 h.sylow_normalizes
      (inclusion le_sup_right t))) = 1 ↔ t.val ∈ sourceS L H
  rw [←MonoidHom.mem_ker,Theory.PSL2.fieldProjection_ker]
  have hi (a : MulAut (L ⧸ pCore 2 L)) :
      MulAut.congr e a ∈ Theory.PSL2.inner F ↔
        a ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    change MulAut.congr e a ∈ MulAut.innerSubgroup (Theory.PSL2.Group F) ↔ _
    rw [←MulAut.map_innerSubgroup_congr e]
    exact mem_map_iff_mem (MulAut.congr e).injective
  rw [hi,plane_quotient_action_inner_iff _ T.isPGroup' hz
    (d.unitaryFive_sylow_join_core_le h hH hp U hc),hs]
  exact ⟨fun ht => ⟨t.property,ht⟩,fun ht => ht.2⟩

/-- The original full Sylow/source Sylow index divides four, the degree of
its actual PSL₂(16) field. -/
theorem Preparation.unitaryFive_source_sylow_index_dvd :
    (sourceS L H).relIndex (T : Subgroup G) ∣ 4 := by
  have hn : n = 4 := by
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    exact (d.unitaryFive_local_structure h hH.1.1.2 hp U hr.some).1
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  change ((sourceS L H).subgroupOf (T : Subgroup G)).index ∣ 4
  rw [←d.unitaryFive_sylow_field_kernel h hH hp U hc e,index_ker]
  exact (unitaryFiveSylowFieldAction h.sylow_normalizes e).range.card_subgroup_dvd_card.trans
    (dvd_of_eq ((FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF).trans hn))

/-- Generalized Thompson transfer through the actual PSL₂(16) quotient
fuses every ambient involution into the original S, without assuming S=T. -/
theorem Preparation.unitaryFive_involution_fused_into_sourceS
    (x : G) (hx : orderOf x=2) : ∃ y ∈ sourceS L H, IsConj x y := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup (F ≃+* F) := IsCyclic.commGroup
  let : IsSimpleGroup G := h.qtke.simple
  obtain ⟨a,hxa⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have ha : orderOf a=2 := by
    rw [←Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hxa
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  obtain ⟨b,hab,hb⟩ := T.exists_isConj_ker_of_cyclic_of_simple h.qtke.nonabelian
    (unitaryFiveSylowFieldAction h.sylow_normalizes e) a ha
  have hbS : b.val ∈ sourceS L H := by
    change b ∈ (sourceS L H).subgroupOf (T : Subgroup G)
    rw [←d.unitaryFive_sylow_field_kernel h hH hp U hc e]
    exact hb
  exact ⟨b.val,hbS,hxa.trans hab⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
