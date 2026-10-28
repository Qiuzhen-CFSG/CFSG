module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Reducible

/-!
# Fusion at the original ambient group and Sylow subgroup: EightGeometry

These are ambient-local versions of the existing source fusion proofs. Only
the structural premise changes: each use is at the original G,T,L,V. The
literal module actions, quotient maps, point Sylow subgroups and conjugators
are preserved. The universal APIs remain available in their original modules.

Source: Aschbacher–Smith, 12.2.16, printed pp.799–800; the reducible
normalizer argument uses 3.3.1 and B.5.1 as in the original proofs.
-/

/- Adapted from FusionEightGeometryModule. -/
section
public section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace AlternatingEightFusion

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (C : AlternatingEightFusion T L V)

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

variable (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T)

include D

include h structural

public theorem core_le_pointSylow_at : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ C.pointSylow := by
  rw [← chosen_sylow_centralizer_eq_core_at h D structural]
  intro x hx
  exact ⟨hx.1, mem_centralizer_singleton_iff.mpr (hx.2 C.v C.v.property).symm⟩

public theorem pointOmega_le_coreOmega_at :
    omegaCenterIn C.pointSylow ≤ omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  intro x hx
  obtain ⟨hxT, hxc, hxs⟩ := (mem_omegaCenterIn_iff _ _).mp hx
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨?_, centralizer_le (C.core_le_pointSylow_at h D structural) hxc, hxs⟩
  rw [← chosen_sylow_centralizer_eq_core_at h D structural]
  exact ⟨hxT.1, centralizer_le (C.chosen_le_pointSylow D) hxc⟩

public theorem pointSpan_le_coreOmega_at :
    C.pointSpan ≤ omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  apply iSup_conjugates_le_of_le_normalizer _ _ _ (C.pointOmega_le_coreOmega_at h D structural)
  exact ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)).trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))).trans
    (normalizer_le_normalizer_omegaCenterIn _)

public theorem pointSpan_elementary_at : IsElementaryAbelian 2 C.pointSpan :=
  IsElementaryAbelian.of_le (C.pointSpan_le_coreOmega_at h D structural)

public theorem pointSpan_le_sylow_at : C.pointSpan ≤ (T : Subgroup G) := by
  intro x hx
  have hc := ((mem_omegaCenterIn_iff _ _).mp (C.pointSpan_le_coreOmega_at h D structural hx)).1
  rw [← chosen_sylow_centralizer_eq_core_at h D structural] at hc
  exact hc.1

public theorem core_centralizes_pointSpan_at : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
    centralizer (C.pointSpan : Set G) := by
  apply le_centralizer_iff.mp
  intro x hx
  exact ((mem_omegaCenterIn_iff _ _).mp (C.pointSpan_le_coreOmega_at h D structural hx)).2.1

public theorem pointSpan_reduced_of_normalizes_at
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (C.pointSpan : Set G)) :
    IsPReduced 2 (C.pointSpan.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let H := L ⊔ (T : Subgroup G)
  let W := C.pointSpan.subgroupOf H
  let := C.pointSpan_elementary_at h D structural
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.subgroupOf ((C.pointSpan_le_sylow_at h D structural).trans le_sup_right)
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  apply (((structural L h).2.2 V D).2.1).of_le_of_sylow_centralizer_le
    (T.subtype le_sup_right) (fun x hx => C.chosen_le_pointSpan D hx)
  intro x hx y hy
  have hxV : (x : G) ∈ centralizer (V : Set G) := by
    intro v hv
    exact congrArg H.subtype (hx.2 ⟨v, (le_sup_right : (T : Subgroup G) ≤ H) (D.le_sylow hv)⟩ hv)
  have hxQ := (chosen_sylow_centralizer_eq_core_at h D structural).le ⟨hx.1, hxV⟩
  exact Subtype.ext ((C.core_centralizes_pointSpan_at h D structural hxQ) y hy)

include C

public theorem thompson_moves_chosen_at :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  intro hc
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural L h).2.2 V D).2.2.2 with hn | hz
    · exact hn
    · exact (C.z_ne (mem_bot.mp (hz ▸
        (show (C.z : G) ∈ V ⊓ centralizer (L : Set G) from ⟨C.z.property, C.z_fixed⟩)))).elim
  have hfull : (D.fundamentalSetup h.toHypothesis1221).fullModule = V := by
    rw [D.fundamentalSetup_fullModule]
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hMV)
      (le_componentOrbit _ _)
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ C.pointSylow := by
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hc hx) C.v C.v.property).symm
  have hn := (Chapter10.source_two_overgroup_normalizer_le_of_centralizes
    (D.fundamentalSetup h.toHypothesis1221) (hfull.symm ▸ hc)
    C.pointSylow (T.isPGroup'.to_le inf_le_left) hJ).2
  have hn' : normalizer (C.pointSylow : Set G) ≤ normalizer (L : Set G) := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal, D.localOrbit_eq] using hn
  exact C.outside (hn' C.normalizes)

omit D h structural [Finite G] in

public theorem pointSylow_normalizes_pointSpan_at
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    C.pointSylow ≤ normalizer (C.pointSpan : Set G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  have hnL := hTL ht.1
  have hnE := normalizer_le_normalizer_omegaCenterIn C.pointSylow
    (C.pointSylow.le_normalizer ht)
  have hm : C.pointSpan.map (MulAut.conj t).toMonoidHom ≤ C.pointSpan := by
    change (⨆ l : L, (omegaCenterIn C.pointSylow).map
      (MulAut.conj (l : G)).toMonoidHom).map (MulAut.conj t).toMonoidHom ≤ _
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro l
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    apply (le_iSup (fun l : L => (omegaCenterIn C.pointSylow).map
      (MulAut.conj (l : G)).toMonoidHom)
      ⟨t * l * t⁻¹, (mem_normalizer_iff.mp hnL l).mp l.property⟩)
    refine ⟨t * e * t⁻¹, (mem_normalizer_iff.mp hnE e).mp he, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    group
  exact hm (mem_map_of_mem (MulAut.conj t).toMonoidHom hx)

omit D h structural [Finite G] in

public theorem pointSpan_normalizes_of_supplement_at
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : (T : Subgroup G) ≤ L ⊔ C.pointSylow) :
    L ⊔ (T : Subgroup G) ≤ normalizer (C.pointSpan : Set G) :=
  sup_le (le_normalizer_componentOrbit _ _)
    (hs.trans (sup_le (le_normalizer_componentOrbit _ _)
      (C.pointSylow_normalizes_pointSpan_at hTL)))

public theorem pointSpanModule_of_normalizes_at
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (C.pointSpan : Set G)) : C.PointSpanModule := by
  have he := C.pointSpan_elementary_at h D structural
  refine ⟨he, C.pointSpan_le_sylow_at h D structural, hn,
    C.pointSpan_reduced_of_normalizes_at h D structural hn, ?_⟩
  let := he
  apply Chapter3.internalActionImage_isFFModule_of_thompson_not_le
    T (L ⊔ (T : Subgroup G)) C.pointSpan le_sup_right
      (C.pointSpan_le_sylow_at h D structural) hn
  intro hJ
  exact C.thompson_moves_chosen_at h D structural
    (hJ.trans (centralizer_le (C.chosen_le_pointSpan D)))

public theorem pointSpanModule_of_pointSylow_supplement_at
    (hs : (T : Subgroup G) ≤ L ⊔ C.pointSylow) : C.PointSpanModule :=
  C.pointSpanModule_of_normalizes_at h D structural
    (C.pointSpan_normalizes_of_supplement_at (structural L h).1 hs)

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionEightGeometryModuleSupplement. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace AlternatingEightFusion

universe u

variable {G : Type u} [Group G] [Finite G]

variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in

private theorem model_orbit_eq_at (C : AlternatingEightFusion T L V)
    (x : BinaryPermutation.core (Fin 8)) :
    (fun w : BinaryPermutation.core (Fin 8) =>
      ((C.vectorEquiv.symm (Multiplicative.ofAdd w)) : G)) ''
      (Set.range fun a : alternatingGroup (Fin 8) =>
        BinaryPermutation.alternatingCoreRepresentation (Fin 8) a x) =
      conjugacyOrbit L ((C.vectorEquiv.symm (Multiplicative.ofAdd x)) : G) := by
  ext y
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (C.groupEquiv.symm a)
    refine ⟨l,?_⟩
    have hi := C.intertwines l (C.vectorEquiv.symm (Multiplicative.ofAdd x))
    rw [C.vectorEquiv.apply_symm_apply,hl,C.groupEquiv.apply_symm_apply] at hi
    exact hi.symm
  · rintro ⟨l,rfl⟩
    refine ⟨_,⟨C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l),rfl⟩,?_⟩
    simpa only [C.vectorEquiv.apply_symm_apply, toAdd_ofAdd] using
      C.intertwines l (C.vectorEquiv.symm (Multiplicative.ofAdd x))

omit [Finite G] in

private theorem conjugacyOrbit_image_at (A : Subgroup G) (x t : G)
    (ht : t ∈ normalizer (A : Set G)) :
    (MulAut.conj t) '' conjugacyOrbit A x = conjugacyOrbit A (t*x*t⁻¹) := by
  ext y
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨⟨t*a*t⁻¹,(ht a).mp a.property⟩,?_⟩
    simp [MulAut.conj_apply,mul_assoc]
  · rintro ⟨a,rfl⟩
    have ha : t⁻¹ * (a : G) * t ∈ A := by
      simpa using ((normalizer (A : Set G)).inv_mem ht a).mp a.property
    refine ⟨(t⁻¹*a*t)*x*(t⁻¹*a*t)⁻¹,⟨⟨_,ha⟩,rfl⟩,?_⟩
    simp [MulAut.conj_apply,mul_assoc]

public theorem sylow_point_orbit_control_at (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) :
    ∀ t ∈ (T : Subgroup G), ∃ l ∈ L,
      t * (C.v : G) * t⁻¹ = l * (C.v : G) * l⁻¹ := by
  intro t ht
  have htL := (structural L h).1 ht
  have htV := ((structural L h).2.2 V D).1 ht
  let c := V.normalizerMonoidHom ⟨t,htV⟩
  let m := C.vectorEquiv.symm.trans (c.trans C.vectorEquiv)
  let e : BinaryPermutation.core (Fin 8) ≃+ BinaryPermutation.core (Fin 8) :=
    AddEquiv.toMultiplicative.symm m
  let j : BinaryPermutation.core (Fin 8) → G :=
    fun w => (C.vectorEquiv.symm (Multiplicative.ofAdd w) : G)
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (C.vectorEquiv.symm.injective.comp Multiplicative.ofAdd.injective)
  have he (w : BinaryPermutation.core (Fin 8)) :
      j (e w) = t * j w * t⁻¹ := by
    change (C.vectorEquiv.symm (C.vectorEquiv (c (C.vectorEquiv.symm
      (Multiplicative.ofAdd w)))) : G) = _
    rw [C.vectorEquiv.symm_apply_apply]
    rfl
  have ho (w : BinaryPermutation.core (Fin 8)) :
      e '' (Set.range fun a : alternatingGroup (Fin 8) =>
        BinaryPermutation.alternatingCoreRepresentation (Fin 8) a w) =
      Set.range fun a : alternatingGroup (Fin 8) =>
        BinaryPermutation.alternatingCoreRepresentation (Fin 8) a (e w) := by
    apply Set.image_injective.mpr hj
    rw [Set.image_image]
    have he' : (fun x => j (e x)) = (fun x => MulAut.conj t (j x)) := funext he
    rw [he', ← Set.image_image]
    change (MulAut.conj t) '' (j '' _) = j '' _
    rw [model_orbit_eq_at,model_orbit_eq_at,conjugacyOrbit_image_at L _ t htL]
    exact congrArg (conjugacyOrbit L) (he w).symm
  have hw := BinaryPermutation.eight_core_weight_two_of_orbit_image e ho
    (C.vectorEquiv C.v).toAdd C.weight_two
  obtain ⟨a,ha⟩ := BinaryPermutation.exists_even_permutation_of_weight
    (by decide : 3 ≤ Fintype.card (Fin 8)) (C.vectorEquiv C.v).toAdd.val
    (e (C.vectorEquiv C.v).toAdd).val (C.weight_two.trans hw.symm)
  have ha' : BinaryPermutation.alternatingCoreRepresentation (Fin 8) a
      (C.vectorEquiv C.v).toAdd = e (C.vectorEquiv C.v).toAdd := Subtype.ext ha
  have hv : j (C.vectorEquiv C.v).toAdd = (C.v : G) := by
    simp only [j,ofAdd_toAdd,C.vectorEquiv.symm_apply_apply]
  have horbit : j (e (C.vectorEquiv C.v).toAdd) ∈
      conjugacyOrbit L (j (C.vectorEquiv C.v).toAdd) := by
    rw [← model_orbit_eq_at]
    exact ⟨_,⟨a,ha'⟩,rfl⟩
  obtain ⟨l,hl⟩ := horbit
  refine ⟨l,l.property,?_⟩
  rw [he,hv] at hl
  exact hl.symm

public theorem pointSylow_supplement_at (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) :
    (T : Subgroup G) ≤ L ⊔ C.pointSylow :=
  T.le_sup_pointCentralizer_of_orbit_control L (structural L h).1 C.v
    C.sylow C.sylow_image (C.sylow_point_orbit_control_at h D structural)

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionEightGeometryModuleComplete. -/
section
public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace AlternatingEightFusion

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

public theorem pointSpanModule_at (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T)
    (_hnone : NoEscape L V) : C.PointSpanModule :=
  C.pointSpanModule_of_pointSylow_supplement_at h D structural
    (C.pointSylow_supplement_at h D structural)

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionEightGeometry. -/
section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace AlternatingEightFusion

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (C : AlternatingEightFusion T L V)

public theorem pointFixed_disjoint_conjugate_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T)
    (hT : C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G)) :
    C.pointFixed ⊓ C.pointFixed.map (MulAut.conj C.g).toMonoidHom = ⊥ := by
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      (structural L h).1) (le_componentOrbit L T)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  have hd := hu.centralizer_intersection C.g (by simpa only [horbit] using C.outside)
  change (omegaCenterIn (T : Subgroup G) ⊓ centralizer (componentOrbit L T : Set G)) ⊓
    (omegaCenterIn (T : Subgroup G) ⊓ centralizer (componentOrbit L T : Set G)).map
      (MulAut.conj C.g).toMonoidHom = ⊥ at hd
  rw [horbit] at hd
  have hle : C.pointFixed ≤ omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) := by
    intro x hx
    have hh := (mem_omegaCenterIn_iff _ _).mp hx.1
    exact ⟨(mem_omegaCenterIn_iff _ _).mpr ⟨hh.1.1, hT hx, hh.2.2⟩, hx.2⟩
  exact bot_unique ((inf_le_inf hle (map_mono hle)).trans hd.le)

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end

/- Adapted from FusionEightGeometryDecompositionPointGeometry. -/
section
open Subgroup Theory.GroupTheory

open scoped Pointwise

open BinaryPermutation Representation

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace AlternatingEightFusion

variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (C : AlternatingEightFusion T L V)

public theorem pointSylow_supplement_inside_at
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) :
    (T : Subgroup G) ≤ C.pointSylow ⊔ ((T : Subgroup G) ⊓ L) := by
  have hn : C.pointSylow ≤ normalizer (L : Set G) :=
    inf_le_left.trans (structural L h).1
  intro t ht
  have hm : t ∈ (L : Set G) * (C.pointSylow : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L C.pointSylow hn]
    exact C.pointSylow_supplement_at h D structural ht
  obtain ⟨l,hl,p,hp,he⟩ := hm
  have hlT : l ∈ (T : Subgroup G) := by
    have hmem := (T : Subgroup G).mul_mem ht ((T : Subgroup G).inv_mem hp.1)
    simpa only [← he, mul_inv_cancel_right] using hmem
  rw [← he]
  exact (C.pointSylow ⊔ ((T : Subgroup G) ⊓ L)).mul_mem
    (mem_sup_right ⟨hlT,hl⟩) (mem_sup_left hp)

public theorem pointFixed_conclusions_of_moved_and_fixed_comparison_at
    {K : GroupClass} (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) (R : C.PointSpanModule)
    (hm : ⁅C.pointSpan, L⁆ ≤ V)
    (hfixed : V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore) :
    omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed ∧
      C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G) :=
  C.pointFixed_conclusions_of_moved_and_point_geometry D R hm
    (C.pointComponentImage_fixed_le_core hnone) hfixed
    (C.pointSylow_supplement_inside_at h D structural)

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end

/- Adapted from FusionEightGeometryDecompositionPointGeometryFixedComparison. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace AlternatingEightFusion

universe u

variable {G : Type u} [Group G] [Finite G]

variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

public theorem point_fixed_comparison_at (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) :
    V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore := by
  obtain ⟨P,hP⟩ := C.pointComponentImage_is_sylow hnone
  intro w hw
  refine ⟨hw.1, ?_⟩
  intro t ht
  have htL := (structural L h).1 ht.1
  have htV := ((structural L h).2.2 V D).1 ht.1
  let c := V.normalizerMonoidHom ⟨t,htV⟩
  let m := C.vectorEquiv.symm.trans (c.trans C.vectorEquiv)
  let e : core (Fin 8) ≃+ core (Fin 8) := AddEquiv.toMultiplicative.symm m
  let j : core (Fin 8) → G :=
    fun a => (C.vectorEquiv.symm (Multiplicative.ofAdd a) : G)
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (C.vectorEquiv.symm.injective.comp Multiplicative.ofAdd.injective)
  have he (a : core (Fin 8)) : j (e a) = t * j a * t⁻¹ := by
    change (C.vectorEquiv.symm (C.vectorEquiv (c (C.vectorEquiv.symm
      (Multiplicative.ofAdd a)))) : G) = _
    rw [C.vectorEquiv.symm_apply_apply]
    rfl
  have hjv (a : V) : j (C.vectorEquiv a).toAdd = (a : G) := by
    simp only [j,ofAdd_toAdd,C.vectorEquiv.symm_apply_apply]
  have ha (l : L) (a : core (Fin 8)) :
      j (alternatingCoreRepresentation (Fin 8) (C.componentProjection l) a) =
        (l : G) * j a * (l : G)⁻¹ := by
    simpa only [j, componentProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      C.vectorEquiv.apply_symm_apply,toAdd_ofAdd] using
      C.intertwines l (C.vectorEquiv.symm (Multiplicative.ofAdd a))
  have ho (a : core (Fin 8)) :
      e '' (Set.range fun b : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) b a) =
      Set.range fun b : alternatingGroup (Fin 8) =>
        alternatingCoreRepresentation (Fin 8) b (e a) := by
    ext y
    constructor
    · rintro ⟨_,⟨b,rfl⟩,rfl⟩
      obtain ⟨l,hl⟩ := C.componentProjection_surjective b
      let l' : L := ⟨t*l*t⁻¹,(htL l).mp l.property⟩
      refine ⟨C.componentProjection l', ?_⟩
      apply hj
      rw [← hl]
      simp only [he,ha]
      simp [l',mul_assoc]
    · rintro ⟨b,rfl⟩
      obtain ⟨l,hl⟩ := C.componentProjection_surjective b
      have hl' : t⁻¹ * (l : G) * t ∈ L := by
        simpa using ((normalizer (L : Set G)).inv_mem htL l).mp l.property
      let l' : L := ⟨t⁻¹*l*t,hl'⟩
      refine ⟨alternatingCoreRepresentation (Fin 8) (C.componentProjection l') a,
        ⟨C.componentProjection l',rfl⟩,?_⟩
      apply hj
      rw [← hl]
      simp only [he,ha]
      simp [l',mul_assoc]
  have hev : e (C.vectorEquiv C.v).toAdd = (C.vectorEquiv C.v).toAdd := by
    apply hj
    rw [he,hjv]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp ht.2)
  have hez : e (C.vectorEquiv C.z).toAdd = (C.vectorEquiv C.z).toAdd := by
    apply hj
    rw [he,hjv]
    exact mul_inv_eq_iff_eq_mul.mpr
      (((mem_omegaCenterIn_iff _ _).mp (C.fixed_mem_pointSylow_omega_at h D structural)).2.1 t ht)
  have htn : t ∈ normalizer (L ⊓ C.pointSylow : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨htL,C.pointSylow.le_normalizer ht⟩
  have htc := normalizer_le_normalizer_centralizer (L ⊓ C.pointSylow) htn
  have hF (a : core (Fin 8)) :
      a ∈ fixedSpace (alternatingCoreRepresentation (Fin 8)) C.pointComponentImage ↔
        j a ∈ centralizer (L ⊓ C.pointSylow : Set G) := by
    simpa only [C.vectorEquiv.apply_symm_apply,toAdd_ofAdd] using
      C.pointComponentImage_fixed_iff (C.vectorEquiv.symm (Multiplicative.ofAdd a))
  have heF (a : core (Fin 8))
      (ha : a ∈ fixedSpace (alternatingCoreRepresentation (Fin 8)) C.pointComponentImage) :
      e a ∈ fixedSpace (alternatingCoreRepresentation (Fin 8)) C.pointComponentImage := by
    apply (hF (e a)).mpr
    rw [he]
    exact (htc _).mp ((hF a).mp ha)
  have hwF := (C.pointComponentImage_fixed_iff ⟨w,hw.1⟩).mpr hw.2
  have hfix := EightPointRigidity.fixedSpace_rigidity
    (C.vectorEquiv C.v).toAdd (C.vectorEquiv C.z).toAdd C.weight_two C.constant P e
    (eight_core_weight_two_of_orbit_image e ho) hev hez
    (by simpa only [hP] using heF) (C.vectorEquiv ⟨w,hw.1⟩).toAdd
    (by simpa only [hP] using hwF)
  have hfinal := congrArg j hfix
  rw [he,hjv] at hfinal
  exact mul_inv_eq_iff_eq_mul.mp hfinal

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionEightGeometryTerminal. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

open BinaryPermutation

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace AlternatingEightFusion

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable (C : AlternatingEightFusion T L V)

public theorem pointCore_inf_pointFixed_card_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T) :
    Nat.card (C.pointCore ⊓ C.pointFixed : Subgroup G) = 2 := by
  let := D.elementary
  have hzE := C.fixed_mem_pointSylow_omega_at h D structural
  have hzU : (C.z : G) ∈ C.pointCore := by
    rw [C.pointCore_eq_inf_omega D]
    exact ⟨C.z.property, hzE⟩
  have he : C.pointCore ⊓ C.pointFixed = zpowers (C.z : G) := by
    apply le_antisymm
    · intro x hx
      rcases C.fixed_line x hx.1.1 hx.2.2 with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · exact zpowers_le.mpr ⟨hzU, hzE, C.z_fixed⟩
  rw [he, Nat.card_zpowers]
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ C.z.property) C.z_ne

public theorem pointCore_intersection_card_le_two_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T) (hnone : NoEscape L V) :
    Nat.card (C.pointCore ⊓ C.pointCore.map (MulAut.conj C.g).toMonoidHom :
      Subgroup G) ≤ 2 := by
  let A : AlternatingEightCoreCoordinates L V :=
    ⟨C.groupEquiv, C.vectorEquiv, C.intertwines⟩
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    apply (((structural L h).2.2 V D).2.2.2).resolve_right
    intro he
    exact C.z_ne (mem_bot.mp (he ▸
      (show (C.z : G) ∈ V ⊓ centralizer (L : Set G) from ⟨C.z.property,C.z_fixed⟩)))
  obtain ⟨P,hP⟩ := C.pointComponentImage_is_sylow hnone
  obtain ⟨f,hf⟩ := EightPointSylowParity.exists_weight_parity
    (C.vectorEquiv C.v).toAdd.val C.weight_two P
  let H := C.pointCore ⊓ C.pointCore.map (MulAut.conj C.g).toMonoidHom
  have hHV : H ≤ V := inf_le_left.trans inf_le_left
  let q : H →* Multiplicative (ZMod 2) :=
    ((f.comp (core (Fin 8)).subtype).toAddMonoidHom.toMultiplicative).comp
      (C.vectorEquiv.toMonoidHom.comp (Subgroup.inclusion hHV))
  have hodd (x : H) (hx : (x : G) ≠ 1) :
      f (C.vectorEquiv ⟨x,hHV x.property⟩).toAdd.val = 1 := by
    have hxg := x.property.2
    obtain ⟨y,hy,he⟩ := hxg
    have hy1 : y ≠ 1 := by
      intro hy1
      exact hx (he.symm.trans (by rw [hy1, map_one]))
    have hw := A.outside_weights_at h D structural hnone hMV
      ⟨y,hy.1⟩ ⟨x,hHV x.property⟩ hy1 C.outside he
    apply hf _ ?_ (hw.elim (fun hh => Or.inr hh.2) (fun hh => Or.inl hh.2))
    rw [hP]
    rintro ⟨a,ha⟩
    obtain ⟨l,hl,rfl⟩ := ha
    have hc : (l : G) ∈ centralizer ({(x : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (x.property.1.2 l hl)
    exact congrArg (fun w : core (Fin 8) => w.val)
      ((C.componentProjection_fixes_iff l ⟨x,hHV x.property⟩).mpr hc)
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).mpr
    intro x hx
    by_contra hn
    have ho := hodd x (fun he => hn (Subtype.ext he))
    have hz : f (C.vectorEquiv ⟨x,hHV x.property⟩).toAdd.val = 0 :=
      congrArg Multiplicative.toAdd hx
    exact one_ne_zero (ho.symm.trans hz)
  have hc := Nat.card_le_card_of_injective q hq
  simpa only [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using hc

public theorem omega_le_of_pointCore_decomposition_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T) (hnone : NoEscape L V)
    (hsplit : omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed)
    (hT : C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G)) :
    omegaCenterIn C.pointSylow ≤ V := by
  have hlo := two_lt_card_inf_conjugate_of_disjoint_supplement
    (omegaCenterIn C.pointSylow) C.pointCore C.pointFixed
    (C.pointCore_le_omega D) inf_le_left hsplit
    (C.pointCore_inf_pointFixed_card_at h D structural) C.g
    (normalizer_le_normalizer_omegaCenterIn C.pointSylow C.normalizes)
    (C.pointFixed_disjoint_conjugate_at h structural hT)
  exact (not_lt_of_ge (C.pointCore_intersection_card_le_two_at h D structural hnone) hlo).elim

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionEightGeometryComplete. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace AlternatingEightFusion

variable (C : AlternatingEightFusion T L V)

public theorem omega_le_of_original_hypotheses_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T) (hnone : NoEscape L V) :
    omegaCenterIn C.pointSylow ≤ V := by
  let R := C.pointSpanModule_at h D structural hnone
  have hm := C.pointSpan_commutator_eq_chosen h.toHypothesis1221 D R
  have hfixed := C.point_fixed_comparison_at h D structural hnone
  obtain ⟨hsplit, hT⟩ :=
    C.pointFixed_conclusions_of_moved_and_fixed_comparison_at h D structural hnone R hm.le hfixed
  exact C.omega_le_of_pointCore_decomposition_at h D structural hnone hsplit hT

end AlternatingEightFusion

public theorem globalTI_of_row_reductions_of_eight_geometry_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple.{u} T) (hnone : NoEscape L V)
    (fixedFree : V ⊓ centralizer (L : Set G) = ⊥ → IsTISubgroup V)
    (reducible : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V)) :
    IsTISubgroup V :=
  globalTI_of_row_reductions_at h D structural hnone fixedFree reducible
    (fun C => C.omega_le_of_original_hypotheses_at h D structural hnone)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end
