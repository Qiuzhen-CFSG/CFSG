module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveDefs
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# The projective orbit map from a marked complementary root space

A point stabilizer normalizes the root group defined by its actual displacement
and fixed axis. Hence a root-normalizer invariant subspace has a well-defined
orbit map on field lines. Two-transitivity transports its marked complementary
pair to every pair of distinct points, proving disjointness and spanning.
Conjugating the literal root conditions proves both incident-root clauses; in
the natural plane every incident hyperplane equals the given point.

The argument permits zero target spaces and in fact needs neither finiteness
nor characteristic two of the coefficient field. It uses no recognition input.

Source: Aschbacher–Smith, G.1.1, G.1.3 and G.1.5(3), printed pp.327–328,
PDF pp.338–339. The G.2.3 application is in the parent `ProjectiveOrbit` module.
-/

@[expose] public section
open scoped MatrixGroups LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
variable {F : Type*} [Field F]

private theorem map_rep_mul {k H V : Type*} [Field k] [Group H]
    [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (a b : H) (X : Submodule k V) :
    (X.map (ρ b)).map (ρ a) = X.map (ρ (a * b)) := by
  rw [← Submodule.map_comp, map_mul]
  rfl

private theorem map_rep_inv {k H V : Type*} [Field k] [Group H]
    [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (a : H) (X : Submodule k V) :
    (X.map (ρ a)).map (ρ a⁻¹) = X := by
  rw [map_rep_mul, inv_mul_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]

/-- The translate of an actual field line under the natural matrix action. -/
noncomputable def translate (a : SL(2, F)) (A : Point F) : Point F :=
  Projectivization.equivSubmodule F (Fin 2 → F)
    (a • (Projectivization.equivSubmodule F (Fin 2 → F)).symm A)

private theorem submodule_smul (a : SL(2, F)) (p : ℙ F (Fin 2 → F)) :
    (a • p).submodule = p.submodule.map (Representation.specialLinearNatural 2 a) := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [Projectivization.smul_mk, Projectivization.submodule_mk,
      Submodule.map_span, Set.image_singleton]
    rfl

theorem translate_val (a : SL(2, F)) (A : Point F) :
    (translate a A).val = A.val.map (Representation.specialLinearNatural 2 a) := by
  change (a • (Projectivization.equivSubmodule F (Fin 2 → F)).symm A).submodule = _
  rw [submodule_smul]
  congr 1
  exact congrArg Subtype.val ((Projectivization.equivSubmodule F (Fin 2 → F)).apply_symm_apply A)

private theorem exists_translate (A B : Point F) : ∃ a : SL(2, F), translate a A = B := by
  let : MulAction.IsPretransitive SL(2, F) (ℙ F (Fin 2 → F)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq SL(2, F)
    ((Projectivization.equivSubmodule F (Fin 2 → F)).symm A)
    ((Projectivization.equivSubmodule F (Fin 2 → F)).symm B)
  refine ⟨a, ?_⟩
  unfold translate
  rw [ha]
  exact (Projectivization.equivSubmodule F (Fin 2 → F)).apply_symm_apply B

private theorem exists_pair_translate (A B C D : Point F) (hAB : A ≠ B) (hCD : C ≠ D) :
    ∃ a : SL(2, F), translate a A = C ∧ translate a B = D := by
  let e := Projectivization.equivSubmodule F (Fin 2 → F)
  obtain ⟨a, ha, hb⟩ := (MulAction.is_two_pretransitive_iff
    (G := SL(2, F)) (α := ℙ F (Fin 2 → F))).mp inferInstance
    (e.symm.injective.ne hAB) (e.symm.injective.ne hCD)
  exact ⟨a, (congrArg e ha).trans (e.apply_symm_apply C),
    (congrArg e hb).trans (e.apply_symm_apply D)⟩

private theorem root_conjugate (A : Submodule F (Fin 2 → F)) (a r : SL(2, F))
    (hr : r ∈ rootGroup F A) :
    a * r * a⁻¹ ∈ rootGroup F (A.map (Representation.specialLinearNatural 2 a)) := by
  constructor
  · intro v
    refine Submodule.mem_map.mpr ⟨_, hr.1 ((Representation.specialLinearNatural 2) a⁻¹ v), ?_⟩
    simp only [map_sub, map_mul, Module.End.mul_apply, Representation.self_inv_apply]
  · rintro v ⟨w, hw, rfl⟩
    simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply, hr.2 w hw]

/-- A matrix stabilizing a field line normalizes its literal transvection group. -/
theorem mem_root_normalizer_of_map_eq (A : Submodule F (Fin 2 → F)) (a : SL(2, F))
    (ha : A.map (Representation.specialLinearNatural 2 a) = A) :
    a ∈ Subgroup.normalizer (rootGroup F A : Set SL(2, F)) := by
  have hai : A.map (Representation.specialLinearNatural 2 a⁻¹) = A := by
    calc
      _ = (A.map (Representation.specialLinearNatural 2 a)).map
        (Representation.specialLinearNatural 2 a⁻¹) := congrArg _ ha.symm
      _ = A := map_rep_inv _ _ _
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    simpa only [ha] using root_conjugate A a r hr
  · intro hr
    have h := root_conjugate A a⁻¹ (a * r * a⁻¹) hr
    simpa only [hai, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
      mul_one] using h


private theorem exists_equivariant_orbit
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) SL(2, F) M) (A : Point F)
    (X : Submodule (ZMod 2) M)
    (hN : ∀ a ∈ Subgroup.normalizer (rootGroup F A.val : Set SL(2, F)),
      X.map (σ a) = X) :
    ∃ φ : Point F → Submodule (ZMod 2) M,
      φ A = X ∧
      (∀ a (B : Point F), B.val = A.val.map (Representation.specialLinearNatural 2 a) →
        φ B = X.map (σ a)) ∧
      ∀ a (B C : Point F), C.val = B.val.map (Representation.specialLinearNatural 2 a) →
        φ C = (φ B).map (σ a) := by
  classical
  have htrans (B : Point F) : ∃ a : SL(2, F),
      B.val = A.val.map (Representation.specialLinearNatural 2 a) := by
    obtain ⟨a, rfl⟩ := exists_translate A B
    exact ⟨a, translate_val a A⟩
  let k (B : Point F) := (htrans B).choose
  have hk (B : Point F) : B.val = A.val.map (Representation.specialLinearNatural 2 (k B)) :=
    (htrans B).choose_spec
  let φ (B : Point F) := X.map (σ (k B))
  have hφ (a : SL(2, F)) (B : Point F)
      (hB : B.val = A.val.map (Representation.specialLinearNatural 2 a)) :
      φ B = X.map (σ a) := by
    have hs : A.val.map (Representation.specialLinearNatural 2 ((k B)⁻¹ * a)) = A.val := by
      rw [← map_rep_mul, ← hB, hk B, map_rep_inv]
    have hn := hN ((k B)⁻¹ * a) (mem_root_normalizer_of_map_eq A.val _ hs)
    have hm := congrArg (fun Y : Submodule (ZMod 2) M => Y.map (σ (k B))) hn
    rw [map_rep_mul, mul_inv_cancel_left] at hm
    exact hm.symm
  refine ⟨φ, ?_, hφ, ?_⟩
  · simpa only [map_one, Module.End.one_eq_id, Submodule.map_id] using
      hφ 1 A (by rw [map_one, Module.End.one_eq_id, Submodule.map_id])
  · intro a B C hC
    rw [hφ (a * k B) C (by rw [hC, hk B, map_rep_mul])]
    exact (map_rep_mul σ a (k B) X).symm

private theorem incident_axis_eq (A : Point F) (B : Submodule F (Fin 2 → F))
    (hdim : Module.finrank F B + 1 = Module.finrank F (Fin 2 → F))
    (hAB : A.val ≤ B) : A.val = B := by
  apply Submodule.eq_of_le_of_finrank_eq hAB
  rw [A.property]
  have hd : Module.finrank F (Fin 2 → F) = 2 := by simp
  rw [hd] at hdim
  omega

/-- G.1.5(3): a complementary marked root space extends to an equivariant
projective map satisfying every clause of G.1.3, including multiplicity zero. -/
theorem exists_orbit_criterion
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) SL(2, F) M) (A : Point F)
    (X : Submodule (ZMod 2) M) (t : SL(2, F))
    (hne : A.val ≠ A.val.map (Representation.specialLinearNatural 2 t))
    (hsplit : IsCompl X (X.map (σ t)))
    (hN : ∀ a ∈ Subgroup.normalizer (rootGroup F A.val : Set SL(2, F)),
      X.map (σ a) = X)
    (hroot : ∀ a ∈ rootGroup F A.val,
      LinearMap.range (σ a - 1) ≤ X ∧ ∀ v ∈ X, σ a v = v) :
    ∃ φ : Point F → Submodule (ZMod 2) M,
      φ A = X ∧
      (∀ a (B : Point F), B.val = A.val.map (Representation.specialLinearNatural 2 a) →
        φ B = X.map (σ a)) ∧ Criterion σ φ := by
  obtain ⟨φ, hA, hφ, hequiv⟩ := exists_equivariant_orbit σ A X hN
  have hAt : φ (translate t A) = X.map (σ t) := hφ t _ (translate_val t A)
  have hroot_all (C : Point F) (r : SL(2, F)) (hr : r ∈ rootGroup F C.val) :
      (∀ v : M, σ r v - v ∈ φ C) ∧ (∀ v ∈ φ C, σ r v = v) := by
    obtain ⟨a, ha⟩ := exists_translate A C
    have hC : C.val = A.val.map (Representation.specialLinearNatural 2 a) := by
      rw [← ha, translate_val]
    have hr' : a⁻¹ * r * a ∈ rootGroup F A.val := by
      have h := root_conjugate C.val a⁻¹ r hr
      simpa only [inv_inv, hC, map_rep_inv] using h
    obtain ⟨hm, hf⟩ := hroot _ hr'
    rw [hφ a C hC]
    constructor
    · intro v
      have hv : σ (a⁻¹ * r * a) (σ a⁻¹ v) - σ a⁻¹ v ∈ X :=
        hm ⟨σ a⁻¹ v, rfl⟩
      refine Submodule.mem_map.mpr ⟨_, hv, ?_⟩
      simp only [map_sub, map_mul, Module.End.mul_apply,
        Representation.self_inv_apply]
    · rintro v ⟨w, hw, rfl⟩
      apply (σ.apply_bijective a⁻¹).injective
      simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using hf w hw
  refine ⟨φ, hA, hφ, ⟨hequiv, ?_, ?_, ?_, ?_⟩⟩
  · intro C B hdim hCB r hr v
    have hB := incident_axis_eq C B hdim hCB
    subst B
    exact (hroot_all C r hr).1 v
  · intro C B hdim hCB D hDB r hr v hv
    have hB := incident_axis_eq C B hdim hCB
    have hD : D = C := Subtype.ext ((incident_axis_eq D B hdim hDB).trans hB.symm)
    subst D
    subst B
    exact (hroot_all C r hr).2 v hv
  · intro B C hBC
    have hAt_ne : A ≠ translate t A := by
      intro he
      exact hne ((congrArg Subtype.val he).trans (translate_val t A))
    obtain ⟨a, ha, hc⟩ := exists_pair_translate A (translate t A) B C hAt_ne hBC
    have hB : B.val = A.val.map (Representation.specialLinearNatural 2 a) := by
      rw [← ha, translate_val]
    have hC : C.val = (translate t A).val.map (Representation.specialLinearNatural 2 a) := by
      rw [← hc, translate_val]
    rw [hequiv a A B hB, hequiv a (translate t A) C hC, hA, hAt]
    exact Submodule.disjoint_map (σ.apply_bijective a).injective hsplit.disjoint
  · apply top_unique
    rw [← hsplit.sup_eq_top]
    apply sup_le
    · rw [← hA]
      exact le_iSup φ A
    · rw [← hAt]
      exact le_iSup φ (translate t A)

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
