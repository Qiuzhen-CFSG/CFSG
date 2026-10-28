module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers.TableRows
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers.Transport
public import Theory.Mathieu.M12.Properties.InvolutionFusion
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Normalized residual A₅ subgroups in the H.11 involution centralizers

For an involution that is not two-central in the ambient group, the two
explicit table rows identify its residual centralizer with C₂ × S₅ or C₂ × A₅.
The image of the derived subgroup is therefore A₅. The residual centralizer
is normalized by the full ambient centralizer, which also normalizes this
characteristic subgroup.

To exclude the marked central inner class, extend the native residual Sylow
to an ambient Sylow. Its intersection with the normal residual is exactly
the original Sylow. The ambient Sylow therefore normalizes that intersection
and fixes its unique nonidentity central element. Conjugacy and the given
residual marking transport this genuine ambient two-centrality.

This is the group-theoretic step in Aschbacher–Smith H.11.1(5), combined
manuscript of 1 March 2004, printed pp.392–393 (PDF pp.403–404). The two table
rows remain explicit premises; no module-action conclusion is assumed.
-/

open Subgroup Sporadic.Mathieu
open Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers

section Algebra
variable {G H : Type*} [Group G] [Group H]
private noncomputable def derivedEquiv (e : G ≃* H) : _root_.commutator G ≃* _root_.commutator H :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl))

private noncomputable def derivedProductEquiv (A B : Type*) [CommGroup A] [Group B] :
    _root_.commutator (A × B) ≃* _root_.commutator B := by
  have he : _root_.commutator (A × B) = (⊥ : Subgroup A).prod (_root_.commutator B) := by
    change ⁅(⊤ : Subgroup (A × B)), ⊤⁆ = _
    rw [← top_prod_top, commutator_prod_prod]
    rw [← _root_.commutator_def, commutator_eq_bot]
    rfl
  exact (MulEquiv.subgroupCongr he).trans
    (((⊥ : Subgroup A).prodEquiv (_root_.commutator B)).trans MulEquiv.uniqueProd)

private noncomputable def derivedSymmetricEquiv :
    _root_.commutator (Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) ≃*
      alternatingGroup (Fin 5) :=
  (derivedProductEquiv _ _).trans
    (MulEquiv.subgroupCongr (alternatingGroup.commutator_perm_eq (by simp)))

private noncomputable def derivedAlternatingEquiv :
    _root_.commutator (Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) ≃*
      alternatingGroup (Fin 5) :=
  (derivedProductEquiv _ _).trans
    ((MulEquiv.subgroupCongr (commutator_alternatingGroup_eq_top (by simp))).trans
      Subgroup.topEquiv)

private noncomputable def centralizerConjEquiv (x y : G) (h : IsConj x y) :
    centralizer ({x} : Set G) ≃* centralizer ({y} : Set G) := by
  let g := (isConj_iff.mp h).choose
  have hg := (isConj_iff.mp h).choose_spec
  have he : (MulAut.conj g) x = y := hg
  have ee := MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)
  rw [MulAut.congr_conj, he, MulAut.fixedSubgroup_conj, MulAut.fixedSubgroup_conj] at ee
  exact ee
end Algebra

section Lifting
variable {G H : Type*} [Group G] [Group H]

private theorem twoCentral_of_fixed_sylow (f : H →* G) (hf : Function.Injective f)
    [f.range.Normal] (P : Sylow 2 H) (z : P)
    (hz : ∀ a : MulAut P, a z = z) : TwoCentral (f (z : H)) := by
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  let I := (P : Subgroup H).map f
  let e : P ≃* I := (P : Subgroup H).equivMapOfInjective f hf
  have hI : I = f.range ⊓ (Q : Subgroup G) := by
    dsimp [I]
    rw [← hQ, map_comap_eq]
  have hN : (Q : Subgroup G) ≤ normalizer (I : Set G) := by
    rw [hI]
    exact (le_inf le_normalizer_of_normal (Q : Subgroup G).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hzQ : f (z : H) ∈ Q := by
    have hm : f (z : H) ∈ I := mem_map_of_mem f z.property
    rw [hI] at hm
    exact hm.2
  refine ⟨Q, hzQ, mem_center_iff.mpr ?_⟩
  intro q
  let a := I.normalizerMonoidHom ⟨(q : G), hN q.property⟩
  have he : a (e z) = e z := by
    have hh := hz (MulAut.congr e.symm a)
    change e.symm (a (e z)) = z at hh
    exact e.symm.injective (hh.trans (e.symm_apply_apply z).symm)
  have hh := congrArg (fun x : I => (x : G)) he
  change (q : G) * f (z : H) * (q : G)⁻¹ = f (z : H) at hh
  exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh)

private theorem native_center_fixed (a : MulAut M12SmallPair.sylowCandidate) :
    a ⟨M12SmallPair.z, M12SmallPair.core_le_sylowCandidate M12SmallPair.z_mem_core⟩ =
      ⟨M12SmallPair.z, M12SmallPair.core_le_sylowCandidate M12SmallPair.z_mem_core⟩ := by
  let z : M12SmallPair.sylowCandidate :=
    ⟨M12SmallPair.z, M12SmallPair.core_le_sylowCandidate M12SmallPair.z_mem_core⟩
  have hc : z ∈ center M12SmallPair.sylowCandidate :=
    (M12SmallPair.sylowCandidate_center_mem z).mpr (Or.inr rfl)
  have hac : a z ∈ center M12SmallPair.sylowCandidate :=
    (centerCongr a ⟨z, hc⟩).property
  rcases (M12SmallPair.sylowCandidate_center_mem (a z)).mp hac with ha | ha
  · have he : a z = 1 := Subtype.ext ha
    have he' : z = 1 := a.injective (he.trans a.map_one.symm)
    have hn : M12SmallPair.z = 1 := congrArg Subtype.val he'
    have ho := M12SmallPair.z_order
    simp [hn] at ho
  · exact Subtype.ext ha

private theorem marked_twoCentral (L : Subgroup G) [L.Normal] (e : L ≃* M12) :
    TwoCentral (e.symm M12SmallPair.z : G) := by
  let f := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hr : f.range = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
  let : f.range.Normal := hr ▸ inferInstance
  exact twoCentral_of_fixed_sylow f hf M12SmallPair.commonSylow
    ⟨M12SmallPair.z, M12SmallPair.core_le_sylowCandidate M12SmallPair.z_mem_core⟩
    native_center_fixed
end Lifting

section FixedSubgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)
private noncomputable def residualFixedEquiv (t : G) :
    (solvableResidual G ⊓ centralizer ({t} : Set G) : Subgroup G) ≃*
      (d.embedding t).fixedSubgroup where
  toFun x := ⟨h.residualEquiv ⟨x, x.property.1⟩,
    (MulAut.mem_fixedSubgroup _ _).mpr
      ((embedding_fixes_iff_commute ρ h d t ⟨x, x.property.1⟩).mpr
        (mem_centralizer_singleton_iff.mp x.property.2).symm)⟩
  invFun y := ⟨h.residualEquiv.symm y, (h.residualEquiv.symm y).property,
    mem_centralizer_singleton_iff.mpr (by
      have hy : d.embedding t (h.residualEquiv (h.residualEquiv.symm y)) =
          h.residualEquiv (h.residualEquiv.symm y) := by
        simpa only [MulEquiv.apply_symm_apply] using
          (MulAut.mem_fixedSubgroup (d.embedding t) y).mp y.property
      exact ((embedding_fixes_iff_commute ρ h d t _).mp hy).symm)⟩
  left_inv x := Subtype.ext (congrArg (fun x : solvableResidual G => (x : G))
    (h.residualEquiv.symm_apply_apply ⟨x, x.property.1⟩))
  right_inv y := Subtype.ext (h.residualEquiv.apply_symm_apply y)
  map_mul' x y := Subtype.ext (h.residualEquiv.map_mul ⟨x, x.property.1⟩ ⟨y, y.property.1⟩)
end FixedSubgroup

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)

private theorem central_class_twoCentral (t : solvableResidual G)
    (hc : IsConj M12SmallPair.z (h.residualEquiv t)) : TwoCentral (t : G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hz := marked_twoCentral (solvableResidual G) h.residualEquiv
  have he : (MulAut.conj (h.residualEquiv.symm g : G))
      (h.residualEquiv.symm M12SmallPair.z : G) = (t : G) := by
    have hh := congrArg (fun x : M12 => (h.residualEquiv.symm x : G)) hg
    simpa only [MulAut.conj_apply, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, MulEquiv.symm_apply_apply] using hh
  rw [← he]
  exact hz.map _

include d in
/-- Every non-two-central involution has a residual A₅ centralized by it and
normalized by its full ambient centralizer, conditional on the two table rows. -/
public theorem exists_normal_residual_a5 (hin : InnerCentralizerRow)
    (hout : OuterFixedSubgroupRows) (t : G) (ht : orderOf t = 2) (hnt : ¬ TwoCentral t) :
    ∃ (E : Subgroup G) (_ : E ≃* alternatingGroup (Fin 5)),
      E ≤ solvableResidual G ∧ E ≤ centralizer ({t} : Set G) ∧
        centralizer ({t} : Set G) ≤ normalizer (E : Set G) := by
  classical
  let C := solvableResidual G ⊓ centralizer ({t} : Set G)
  let ef : C ≃* (d.embedding t).fixedSubgroup := residualFixedEquiv ρ h d t
  have hd : Nonempty (_root_.commutator C ≃* alternatingGroup (Fin 5)) := by
    by_cases htL : t ∈ solvableResidual G
    · let x : solvableResidual G := ⟨t, htL⟩
      have hx : orderOf (h.residualEquiv x) = 2 := by
        rw [h.residualEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
        exact ht
      have hc := M12InvolutionFusion.involution_fusion (h.residualEquiv x) hx
      have hnc : ¬ IsConj M12SmallPair.z (h.residualEquiv x) :=
        fun hh => hnt (central_class_twoCentral ρ h x hh)
      have hi := hc.resolve_left hnc
      obtain ⟨ei⟩ := hin
      have he : (d.embedding t).fixedSubgroup =
          centralizer ({h.residualEquiv x} : Set M12) := by
        rw [show d.embedding t = MulAut.conj (h.residualEquiv x) from d.embedding_residual x,
          MulAut.fixedSubgroup_conj]
      let ec := ef.trans ((MulEquiv.subgroupCongr he).trans
        ((centralizerConjEquiv _ _ hi).symm.trans ei))
      exact ⟨(derivedEquiv ec).trans derivedSymmetricEquiv⟩
    · have ha : orderOf (d.embedding t) = 2 :=
        (orderOf_injective d.embedding d.embedding_injective t).trans ht
      have houter : d.embedding t ∉ MulAut.innerSubgroup M12 :=
        fun hh => htL ((d.embedding_mem_inner_iff t).mp hh)
      obtain ⟨eo⟩ := hout (d.embedding t) ha houter
      exact ⟨(derivedEquiv (ef.trans eo)).trans derivedAlternatingEquiv⟩
  obtain ⟨ed⟩ := hd
  let E := (_root_.commutator C).map C.subtype
  let eE : E ≃* _root_.commutator C :=
    ((_root_.commutator C).equivMapOfInjective C.subtype C.subtype_injective).symm
  have hCN : centralizer ({t} : Set G) ≤ normalizer (C : Set G) :=
    (le_inf le_normalizer_of_normal (centralizer ({t} : Set G)).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  exact ⟨E, eE.trans ed, (map_subtype_le _).trans inf_le_left,
    (map_subtype_le _).trans inf_le_right,
    hCN.trans (normalizer_le_normalizer_characteristic_image C (_root_.commutator C))⟩

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers
