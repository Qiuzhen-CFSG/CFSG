module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecompositionPointGeometry
public import Theory.Representation.BinaryPermutation.EightPointSylowRigidity


/-!
# Comparing the actual A₈ point fixed spaces

Conjugation by an element of C_T(v) normalizes L, V and L ∩ C_T(v).
Through the literal quotient and vector markings it therefore preserves
the A₈ orbit partition and the fixed space of the component intersection.
The orbit argument distinguishes weight two from weight six. The point
centralizer fixes v, while the established central-omega placement fixes
the constant vector z.

The intrinsic point-Sylow rigidity theorem now makes this action trivial
on the entire component fixed space. This proves the fixed-space
comparison required by
pointFixed_conclusions_of_moved_and_fixed_comparison; the remaining
central-omega assembly belongs to the point-geometry consumer.

Source: Aschbacher--Smith, 12.2.16, printed p.800, the corrected
point-fixed decomposition on the seven-dimensional augmentation core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
/-- The fixed space of the literal component image is the centralizer of the
intersection in the original module. -/
theorem pointComponentImage_fixed_iff (C : AlternatingEightFusion T L V) (w : V) :
    (C.vectorEquiv w).toAdd ∈ fixedSpace (alternatingCoreRepresentation (Fin 8))
      C.pointComponentImage ↔ (w : G) ∈ centralizer (L ⊓ C.pointSylow : Set G) := by
  constructor
  · intro hw l hl
    have hf := hw ⟨C.componentProjection ⟨l,hl.1⟩, mem_map_of_mem _ hl.2⟩
    exact mem_centralizer_singleton_iff.mp
      ((C.componentProjection_fixes_iff ⟨l,hl.1⟩ w).mp hf)
  · intro hw a
    obtain ⟨l,hl,he⟩ := a.property
    have hf := (C.componentProjection_fixes_iff l w).mpr
      (mem_centralizer_singleton_iff.mpr (hw l ⟨l.property,hl⟩))
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, he] using hf

/-- Vectors centralized by the component part of the point Sylow are fixed by
its whole action on the original seven-dimensional augmentation core. -/
theorem point_fixed_comparison (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) :
    V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore := by
  obtain ⟨P,hP⟩ := C.pointComponentImage_is_sylow hnone
  intro w hw
  refine ⟨hw.1, ?_⟩
  intro t ht
  have htL := (structural G T L h).1 ht.1
  have htV := ((structural G T L h).2.2 V D).1 ht.1
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
      (((mem_omegaCenterIn_iff _ _).mp (C.fixed_mem_pointSylow_omega h D structural)).2.1 t ht)
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
