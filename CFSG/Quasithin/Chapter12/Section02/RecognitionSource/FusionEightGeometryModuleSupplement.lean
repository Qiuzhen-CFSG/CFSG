module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAlternatingEight
public import Theory.Representation.BinaryPermutation.EightCoreNormalizer
public import Theory.GroupTheory.ConjugationOrbitSize
public import Theory.GroupTheory.PointCentralizerSylowSupplement

/-!
# The original A₈ point-Sylow supplement

The structural hypotheses make T normalize both L and the chosen module V.
Via the actual quotient and vector markings, conjugation by T therefore
permutes the A₈ orbits on the seven-dimensional augmentation core. The
weight-two orbit is distinguished from the equally sized weight-six orbit
by its additive triangles, so every T-conjugate of v is L-conjugate to v.

Thus C_LT(v) supplements L in LT. The quotient LT/L is a two-group, and
restricting the supplied Sylow of C_G(v) to C_LT(v) shows that its literal
image C_T(v) still supplements L. This proves T ≤ L ∨ C_T(v), the input
of FusionEightGeometryModule.pointSpanModule_of_pointSylow_supplement.

Only the normalization clauses of Structural1222 are needed here; neither
NoEscape nor any point-span or central-omega conclusion is assumed.

Source: Aschbacher--Smith, 12.2.16, final paragraph, printed p.800,
where T = T_v(T ∩ L) and T_v = C_T(v).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The original marking takes each conjugate under the model to its literal
L-conjugate. -/
private theorem model_orbit_eq (C : AlternatingEightFusion T L V)
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
private theorem conjugacyOrbit_image (A : Subgroup G) (x t : G)
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

/-- Every original Sylow conjugate of the marked weight-two point is an
L-conjugate, on the literal augmentation core. -/
theorem sylow_point_orbit_control (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) :
    ∀ t ∈ (T : Subgroup G), ∃ l ∈ L,
      t * (C.v : G) * t⁻¹ = l * (C.v : G) * l⁻¹ := by
  intro t ht
  have htL := (structural G T L h).1 ht
  have htV := ((structural G T L h).2.2 V D).1 ht
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
    rw [model_orbit_eq,model_orbit_eq,conjugacyOrbit_image L _ t htL]
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
    rw [← model_orbit_eq]
    exact ⟨_,⟨a,ha'⟩,rfl⟩
  obtain ⟨l,hl⟩ := horbit
  refine ⟨l,l.property,?_⟩
  rw [he,hv] at hl
  exact hl.symm
/-- The literal point Sylow supplements L in LT, as used in original 12.2.16. -/
theorem pointSylow_supplement (C : AlternatingEightFusion T L V)
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) :
    (T : Subgroup G) ≤ L ⊔ C.pointSylow :=
  T.le_sup_pointCentralizer_of_orbit_control L (structural G T L h).1 C.v
    C.sylow C.sylow_image (C.sylow_point_orbit_control h D structural)

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
