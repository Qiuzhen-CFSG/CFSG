/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Uses the licensed hyperbolic-pair transport and standard-complement ports.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.PointStabilizer
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.JointGeneration

/-!
# Normalized hyperbolic-pair coordinates and complement extension

Every nonzero singular vector in a split quadratic space has a normalized
singular partner. Any such pair can be moved to the first coordinate pair by an
actual isometry; its perpendicular complement is then the literal smaller split
space, by deleting the first pair of coordinates. The inverse inserts zero
coordinates and applies the inverse ambient isometry.

Extension commutes with this pair transport. Consequently a proof that extension
reflects elementary membership at the standard pair supplies the same conclusion
for every normalized pair. That standard-pair premise is explicit here; the
transport theorem does not assert it.

Source: the hyperbolic-pair and standard-complement constructions adapted in
ReflectionGeneration/JointGeneration.lean and StandardComplement.lean from ATLAS;
this interface connects them to PointStabilizer.lean's explicit factorization.
-/

@[expose] public noncomputable section
universe u
open Theory.AlgebraicGroup
open ClassicalOrthogonal.Quadratic
namespace ClassicalOrthogonal.ReflectionGeneration
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)
variable (e f u v : V) (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)
variable (hu : Q u = 0) (hv : Q v = 0) (huv : Q.polarBilin u v = 1)

/-- Complement extension commutes with transport of the marked hyperbolic pair. -/
theorem isometryTransport_complementLift (i : Q.IsometryEquiv Q)
    (hie : i e = u) (hif : i f = v)
    (k : quadraticIsometrySubgroup (complementForm Q e f)) :
    isometryGroupTransport i (complementLift Q e f he hf hef k) =
      complementLift Q u v hu hv huv
        (isometryGroupTransport (complementTransport Q i e f u v hie hif) k) := by
  let j := complementTransport Q i e f u v hie hif
  let a := isometryGroupTransport i (complementLift Q e f he hf hef k)
  have ha_u : a.val u = u := by
    change i ((complementLift Q e f he hf hef k).val (i.symm u)) = u
    have hiu : i.symm u = e := i.symm_apply_eq.mpr hie.symm
    rw [hiu, complementLift_fix_e, hie]
  have ha_v : a.val v = v := by
    change i ((complementLift Q e f he hf hef k).val (i.symm v)) = v
    have hiv : i.symm v = f := i.symm_apply_eq.mpr hif.symm
    rw [hiv, complementLift_fix_f, hif]
  let b := complementLift Q u v hu hv huv (isometryGroupTransport j k)
  have hb_u : b.val u = u := complementLift_fix_e Q u v hu hv huv _
  have hb_v : b.val v = v := complementLift_fix_f Q u v hu hv huv _
  have hab : (⟨a, ha_u, ha_v⟩ : pairStabilizer Q u v) = ⟨b, hb_u, hb_v⟩ := by
    apply pairRestriction_injective Q u v hu hv huv
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change a.val x.val = b.val x.val
    rw [complementLift_apply Q u v hu hv huv (isometryGroupTransport j k) x]
    change i ((complementLift Q e f he hf hef k).val (j.symm x).val) =
      i (k.val (j.symm x)).val
    rw [complementLift_apply]
  exact congrArg Subtype.val hab

variable {n : ℕ}

/-- Any marked hyperbolic pair has actual normalized split coordinates. -/
theorem exists_pair_normalizationD (e f : VectorD (n+1) F)
    (he : formD (n+1) F e = 0) (hf : formD (n+1) F f = 0)
    (hef : (formD (n+1) F).polarBilin e f = 1) :
    ∃ i : (formD (n+1) F).IsometryEquiv (formD (n+1) F),
      i e = ClassicalOrthogonal.e 0 ∧ i f = ClassicalOrthogonal.f 0 := by
  have hrad : (formD (n+1) F).radical = ⊥ := by
    apply bot_unique
    intro x hx
    rw [Submodule.mem_bot]
    apply polarD_separating x
    intro w
    exact LinearMap.congr_fun hx.2 w
  obtain ⟨g, _, hge, hgf⟩ := elementaryReflection_pair_transport (formD (n+1) F)
    hrad e f (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0)
    he hf (formD_e 0) (formD_f 0) hef (polarD_ef 0)
  exact ⟨isometryCarrierEquiv _ g, hge, hgf⟩

/-- A nonzero singular vector is completed to a normalized hyperbolic pair. -/
theorem exists_singular_partnerD (e : VectorD (n+1) F) (he : e ≠ 0)
    (hqe : formD (n+1) F e = 0) :
    ∃ f, formD (n+1) F f = 0 ∧ (formD (n+1) F).polarBilin e f = 1 := by
  have hn : ¬ ∀ w, (formD (n+1) F).polarBilin e w = 0 := by
    intro h
    exact he (polarD_separating e h)
  obtain ⟨w, hw⟩ := exists_normalized_partner (formD (n+1) F) e hn
  exact ⟨w - formD (n+1) F w • e, partner_correction _ e w hqe hw⟩

/-- The concrete complement isometry removes the normalized first coordinate pair. -/
def normalizedComplementD (e f : VectorD (n+1) F)
    (i : (formD (n+1) F).IsometryEquiv (formD (n+1) F))
    (hie : i e = ClassicalOrthogonal.e 0) (hif : i f = ClassicalOrthogonal.f 0) :
    (complementForm (formD (n+1) F) e f).IsometryEquiv (formD n F) :=
  (complementTransport _ i e f _ _ hie hif).trans standardComplementD

theorem normalizedComplementD_apply (e f : VectorD (n+1) F)
    (i : (formD (n+1) F).IsometryEquiv (formD (n+1) F))
    (hie : i e = ClassicalOrthogonal.e 0) (hif : i f = ClassicalOrthogonal.f 0)
    (x : complement (formD (n+1) F) e f) :
    normalizedComplementD e f i hie hif x = tailD (i x.val) := rfl

theorem normalizedComplementD_symm_apply (e f : VectorD (n+1) F)
    (i : (formD (n+1) F).IsometryEquiv (formD (n+1) F))
    (hie : i e = ClassicalOrthogonal.e 0) (hif : i f = ClassicalOrthogonal.f 0)
    (x : VectorD n F) :
    ((normalizedComplementD e f i hie hif).symm x).val = i.symm (insertD x) := rfl

/-- The only extra elementary-membership input is at the standard pair.
Transport then supplies it at every actual normalized hyperbolic pair. -/
theorem complementLift_mem_elementary_iff_of_standard
    (hstandard : ∀ k : quadraticIsometrySubgroup
        (complementForm (formD (n+1) F) (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0)),
      complementLift (formD (n+1) F) _ _ (formD_e 0) (formD_f 0) (polarD_ef 0) k ∈
        elementarySubgroup (formD (n+1) F) →
      k ∈ elementarySubgroup (complementForm (formD (n+1) F)
        (ClassicalOrthogonal.e 0) (ClassicalOrthogonal.f 0)))
    (e f : VectorD (n+1) F) (he : formD (n+1) F e = 0) (hf : formD (n+1) F f = 0)
    (hef : (formD (n+1) F).polarBilin e f = 1)
    (k : quadraticIsometrySubgroup (complementForm (formD (n+1) F) e f)) :
    complementLift (formD (n+1) F) e f he hf hef k ∈ elementarySubgroup (formD (n+1) F) ↔
      k ∈ elementarySubgroup (complementForm (formD (n+1) F) e f) := by
  refine ⟨fun hk => ?_, complementLift_mem_elementary _ _ _ _ _ _ k⟩
  obtain ⟨i, hie, hif⟩ := exists_pair_normalizationD e f he hf hef
  have h := isometryTransport_mem_elementary i _ hk
  rw [isometryTransport_complementLift (formD (n+1) F) e f _ _ he hf hef
    (formD_e 0) (formD_f 0) (polarD_ef 0) i hie hif] at h
  exact (isometryTransport_mem_elementary_iff _ k).mp (hstandard _ h)

end ClassicalOrthogonal.ReflectionGeneration
