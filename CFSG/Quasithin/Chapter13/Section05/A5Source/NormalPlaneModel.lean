module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBNPair
public import Theory.Representation.BinaryAlternatingFiveExtension.FaithfulExtension
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The marked plane endpoint in the original normal A₅ branch

The original LT action on V has image A₅ or S₅ and kernel C_LT(V)=V.
The natural A₅ extension and the faithful-kernel symmetric extension split,
with an isomorphism retaining every module coordinate. Relabelling the
source Sylow flag sends V₁ to the all-one four-vector. The proved source
identities H=C_G(V₁) and H∩LT=L₁T then mark the common subgroup as the
centralizer of this same vector in the affine model.

Both alternatives are proved from the original Context and normal-branch
hypotheses, including the actual source module and subgroup inclusions.
No split-extension, odd-involution lift, or marked endpoint equivalence is
assumed. Matching this endpoint to the quaternion endpoint remains the
separate compatible-amalgam recognition step.

Source: Aschbacher–Smith, 13.5.17, printed p.922, following the source
identities 13.5.15(6–7), combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.CentralizerReduction Section06.TerminalContradiction.Ratio Section08
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
namespace Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)

/-- The literal natural-module embedding into the original plane endpoint LT. -/
def planeVector : Multiplicative (core (Fin 5)) →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
  d.flag.module.map.codRestrict (L ⊔ (T : Subgroup G))
    (fun v => (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))
      (d.chosen.le_sylow (A5Module.map_mem d.flag.module v)))

private theorem planeVector_range : d.planeVector.range = V.subgroupOf (L ⊔ (T : Subgroup G)) := by
  ext x
  change (∃ v, d.planeVector v = x) ↔ x.val ∈ V
  constructor
  · rintro ⟨v,rfl⟩
    exact A5Module.map_mem d.flag.module v
  · intro hx
    obtain ⟨v,hv⟩ := d.flag.module.range_eq.ge hx
    exact ⟨v,Subtype.ext hv⟩

private theorem planeVector_injective : Function.Injective d.planeVector := by
  intro x y h
  exact d.flag.module.injective (congrArg Subtype.val h)

/-- With the source centralizer identified, the plane group has a marked
ordinary or symmetric affine model, preserving every original module vector. -/
theorem plane_coordinate_models (hC : centralizer (V : Set G) = V) :
    (∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃*
        AlternatingFiveExtension.AlternatingModel,
      ∀ v, E (d.planeVector v) = SemidirectProduct.inl v) ∨
    (∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃*
        Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5),
      ∀ v, E (d.planeVector v) = SemidirectProduct.inl v) := by
  let M := L ⊔ (T : Subgroup G)
  let q := d.localActor
  have hk : q.ker = V.subgroupOf M := by
    ext m
    change d.flag.normalizerAction ⟨m,_⟩ = 1 ↔ m.val ∈ V
    rw [actor_eq_one_iff,hC]
  let eV := (MonoidHom.ofInjective d.planeVector_injective).trans (MulEquiv.subgroupCongr d.planeVector_range)
  let e : q.ker ≃* Multiplicative (core (Fin 5)) := (MulEquiv.subgroupCongr hk).trans eV.symm
  have hei (v : Multiplicative (core (Fin 5))) : (e.symm v : M) = d.planeVector v := rfl
  have he (m : M) (v : q.ker) : e (MulAut.conjNormal m v) =
      AlternatingFiveExtension.coreAction (q m) (e v) := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply Subtype.ext
    rw [hei]
    apply Subtype.ext
    have hv : (v.val : G) = d.flag.module.map (e v) := by
      exact congrArg (fun x : q.ker => (x.val:G)) (e.symm_apply_apply v).symm
    change (m:G)*(v.val:G)*(m:G)⁻¹ = d.flag.module.map _
    rw [hv]
    exact d.flag.normalizer_equivariant ⟨m,(sup_le d.chosen.normalizes d.flag.T_normalizes) m.property⟩ (e v).toAdd
  have hd : q.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le d.alternating_le_localActor
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · right
    have hq : Function.Surjective q := MonoidHom.range_eq_top.mp (index_eq_one.mp hi)
    obtain ⟨E,_,hEe⟩ := AlternatingFiveExtension.exists_marked_symmetric_equiv q hq e he
    refine ⟨E,fun v => ?_⟩
    rw [←hei,hEe,e.apply_symm_apply]
  · left
    have hr : q.range = alternatingGroup (Fin 5) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    let qA := q.codRestrict (alternatingGroup (Fin 5)) (fun m => hr ▸ (show q m ∈ q.range from ⟨m,rfl⟩))
    have hqA : Function.Surjective qA := by
      intro a
      have ham : a.val ∈ q.range := hr.symm ▸ a.property
      obtain ⟨m,hm⟩ := ham
      exact ⟨m,Subtype.ext hm⟩
    have hkA : qA.ker=q.ker := by
      ext x
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    let eA := (MulEquiv.subgroupCongr hkA).trans e
    have heiA (v : Multiplicative (core (Fin 5))) : (eA.symm v : M) = d.planeVector v := rfl
    have heA (m : M) (v : qA.ker) : eA (MulAut.conjNormal m v) =
        Multiplicative.ofAdd (coreRepresentation (Fin 5) (qA m).val (eA v).toAdd) :=
      he m ⟨v.val,hkA.le v.property⟩
    obtain ⟨E,_,hEe⟩ := AlternatingFiveExtension.exists_marked_equiv qA hqA eA heA
    refine ⟨E,fun v => ?_⟩
    rw [←heiA,hEe,eA.apply_symm_apply]

private theorem plane_subgroup_marks {A : Type*} [Group A]
    (ρ : A →* MulAut (Multiplicative (core (Fin 5))))
    (E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (core (Fin 5)) ⋊[ρ] A)
    (hE : ∀ v, E (d.planeVector v)=SemidirectProduct.inl v)
    (hz : (zpowers (Multiplicative.ofAdd z)).map d.flag.module.map = V₁)
    {B : Subgroup G}
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (V₁ : Set G)) :
    (V.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        (SemidirectProduct.inl : Multiplicative (core (Fin 5)) →*
          Multiplicative (core (Fin 5)) ⋊[ρ] A).range ∧
      (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        zpowers (SemidirectProduct.inl (Multiplicative.ofAdd z)) ∧
      (B.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd z)} :
          Set (Multiplicative (core (Fin 5)) ⋊[ρ] A)) := by
  let M := L ⊔ (T : Subgroup G)
  have hcomp : E.toMonoidHom.comp d.planeVector = SemidirectProduct.inl :=
    MonoidHom.ext hE
  have hV : (V.subgroupOf M).map E.toMonoidHom =
      (SemidirectProduct.inl : Multiplicative (core (Fin 5)) →*
        Multiplicative (core (Fin 5)) ⋊[ρ] A).range := by
    rw [←d.planeVector_range,MonoidHom.map_range,hcomp]
  have hVM : V₁ ≤ M := (d.flag.one_le_two.trans d.flag.two_le_V).trans
    (d.chosen.le_sylow.trans le_sup_right)
  have hline : (zpowers (Multiplicative.ofAdd z)).map d.planeVector = V₁.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hVM,map_map]
    exact hz
  have hlineE : (V₁.subgroupOf M).map E.toMonoidHom =
      zpowers (SemidirectProduct.inl (Multiplicative.ofAdd z)) := by
    rw [←hline,map_map,hcomp,MonoidHom.map_zpowers]
  have hBc : B.subgroupOf M = centralizer (V₁.subgroupOf M : Set M) := by
    ext m
    change m.val ∈ B ↔ _
    rw [hB]
    constructor
    · intro hm v hv
      exact Subtype.ext (hm.2 v.val hv)
    · intro hm
      refine ⟨m.property,fun v hv => ?_⟩
      exact congrArg Subtype.val (hm ⟨v,hVM hv⟩ hv)
  refine ⟨hV,hlineE,?_⟩
  rw [hBc]
  have ht := map_inf_centralizer_of_injective E.toMonoidHom E.injective ⊤ (V₁.subgroupOf M)
  rw [top_inf_eq,←MonoidHom.range_eq_map,E.toMonoidHom.range_eq_top.mpr E.surjective,
    top_inf_eq,hlineE] at ht
  simpa only [zpowers_eq_closure,centralizer_closure] using ht.symm

end Context

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The original plane endpoint is the ordinary or symmetric binary affine
five-point group. A single equivalence retains the original module V, central
line V₁, and common Borel L₁T. No splitting or model hypothesis is an input. -/
theorem source_normal_plane_marked_models :
    (∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃*
        AlternatingFiveExtension.AlternatingModel,
      (V.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        (SemidirectProduct.inl : Multiplicative (core (Fin 5)) →*
          AlternatingFiveExtension.AlternatingModel).range ∧
      (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        zpowers (SemidirectProduct.inl (Multiplicative.ofAdd z)) ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd z)} :
          Set AlternatingFiveExtension.AlternatingModel)) ∨
    (∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃*
        Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5),
      (V.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        (SemidirectProduct.inl : Multiplicative (core (Fin 5)) →*
          Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5)).range ∧
      (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        zpowers (SemidirectProduct.inl (Multiplicative.ofAdd z)) ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        centralizer ({SemidirectProduct.inl (Multiplicative.ofAdd z)} :
          Set (Multiplicative (core (Fin 5)) ⋊[AlternatingFiveExtension.coreAction] Equiv.Perm (Fin 5)))) := by
  obtain ⟨g,hz,_,_,_,_⟩ := d.flag.exists_coordinate_witness
  let d' : Context T L V V₁ V₂ V₃ := {d with flag := d.flag.relabel g}
  have hline : (zpowers (Multiplicative.ofAdd z)).map d'.flag.module.map = V₁ := by
    have hh := congrArg (Subgroup.map d.flag.module.map) hz
    rw [MonoidHom.map_zpowers,d.flag.preimage_map V₁
      (d.flag.one_le_two.trans d.flag.two_le_V)] at hh
    rw [MonoidHom.map_zpowers]
    exact hh
  have hC : centralizer (V : Set G)=V := (normal_maximal_core_eq_module d hA312 hH hU hn).2.2
  have hB : residualCentralizer L V₁ ⊔ (T : Subgroup G) =
      (L ⊔ (T : Subgroup G)) ⊓ centralizer (V₁ : Set G) := by
    rw [←normal_local_intersection d hA312 hH hU hn,
      normal_eq_point_centralizer d hA312 hH hU hn]
    exact inf_comm _ _
  rcases d'.plane_coordinate_models hC with ⟨E,hE⟩ | ⟨E,hE⟩
  · exact Or.inl ⟨E,d'.plane_subgroup_marks _ E hE hline hB⟩
  · exact Or.inr ⟨E,d'.plane_subgroup_marks _ E hE hline hB⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
