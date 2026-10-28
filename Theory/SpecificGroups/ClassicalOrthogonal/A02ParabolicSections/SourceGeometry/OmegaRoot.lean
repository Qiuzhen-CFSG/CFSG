/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The singular-root commutator adapts SplitOdd/BinaryEightObstruction/Simplicity/Perfect.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module
public import Theory.SpecificGroups.ClassicalOrthogonal.A02ParabolicSections.SourceGeometry.Root

/-!
# Singular root groups in actual orthogonal commutators

Intersect the additive Siegel root group with the actual orthogonal commutator
carrier. Its two-group property and normalization by point-fixers persist.
A spare hyperbolic pair explicitly writes each required singular root as a
commutator; no identification of elementary and commutator groups is assumed.
These facts supply the minus-family section geometry for A.2.18, printed p.40.
-/

@[expose] public noncomputable section
universe u
namespace ClassicalOrthogonal.A02ParabolicSections
open Theory.AlgebraicGroup Quadratic ReflectionGeneration Subgroup
open scoped commutatorElement
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def fullRootHom (u : V) (hu : Q u = 0) :
    Multiplicative (Q.polarBilin u).ker →* quadraticIsometrySubgroup Q :=
  (elementarySubgroup Q).subtype.comp (rootHom Q u hu)

def fullRootGroup (u : V) (hu : Q u = 0) : Subgroup (quadraticIsometrySubgroup Q) :=
  (fullRootHom Q u hu).range

theorem fullRoot_conj (g : quadraticIsometrySubgroup Q) (u v : V)
    (hu : Q u = 0) (hv : Q.polarBilin u v = 0) :
    g * siegelElement Q u v hu hv * g⁻¹ =
      siegelElement Q (g.val u) (g.val v)
        ((isometry_preserves Q g u).trans hu)
        ((isometry_polar Q (isometryCarrierEquiv Q g) u v).trans hv) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (isometryCarrierEquiv Q g) (siegel Q u v (g.val.symm x)) = _
  rw [siegel_covariant]
  exact congrArg (siegel Q (g.val u) (g.val v)) (g.val.apply_symm_apply x)

theorem fix_mem_fullRootNormalizer (u : V) (hu : Q u = 0)
    (g : quadraticIsometrySubgroup Q) (hg : g.val u = u) :
    g ∈ normalizer (fullRootGroup Q u hu : Set (quadraticIsometrySubgroup Q)) := by
  have hf (g : quadraticIsometrySubgroup Q) (hg : g.val u = u)
      {a : quadraticIsometrySubgroup Q} (ha : a ∈ fullRootGroup Q u hu) :
      g * a * g⁻¹ ∈ fullRootGroup Q u hu := by
    rcases ha with ⟨v,rfl⟩
    have hv : Q.polarBilin u (g.val v.toAdd.val) = 0 := by
      have h := (isometry_polar Q (isometryCarrierEquiv Q g) u v.toAdd.val).trans v.toAdd.prop
      change Q.polarBilin (g.val u) (g.val v.toAdd.val) = 0 at h
      simpa only [hg] using h
    refine ⟨Multiplicative.ofAdd ⟨g.val v.toAdd.val, hv⟩, ?_⟩
    change siegelElement Q u (g.val v.toAdd.val) _ _ = g * siegelElement Q u _ _ _ * g⁻¹
    convert (fullRoot_conj Q g u v.toAdd.val hu v.toAdd.prop).symm using 1
    simp only [hg]
  rw [mem_normalizer_iff]
  intro a
  refine ⟨hf g hg, fun ha => ?_⟩
  have hi : g⁻¹.val u = u := g.val.symm_apply_eq.mpr hg.symm
  have hb := hf g⁻¹ hi ha
  simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hb

def omegaRootGroup (u : V) (hu : Q u = 0) : Subgroup (Minus.Omega F V Q) :=
  (fullRootGroup Q u hu).comap (commutator (quadraticIsometrySubgroup Q)).subtype

theorem omegaRootGroup_fix (u : V) (hu : Q u = 0) {g : Minus.Omega F V Q}
    (hg : g ∈ omegaRootGroup Q u hu) : g.val.val u = u := by
  obtain ⟨v,hv⟩ := hg
  change fullRootHom Q u hu v = g.val at hv
  rw [← hv]
  exact siegel_fix Q u v.toAdd.val hu v.toAdd.prop

theorem omegaRootGroup_two [CharP F 2] (u : V) (hu : Q u = 0) :
    IsPGroup 2 (omegaRootGroup Q u hu) := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨v,hv⟩ := x.prop
  change fullRootHom Q u hu v = x.val.val at hv
  change x.val.val ^ (2^1) = 1
  rw [← hv, pow_one]
  exact congrArg (fun x : elementarySubgroup Q => x.val)
    (root_square Q u v.toAdd.val hu v.toAdd.prop)

theorem fix_mem_omegaRootNormalizer (u : V) (hu : Q u = 0)
    (g : Minus.Omega F V Q) (hg : g.val.val u = u) :
    g ∈ normalizer (omegaRootGroup Q u hu : Set (Minus.Omega F V Q)) :=
  (fullRootGroup Q u hu).le_normalizer_comap _
    (fix_mem_fullRootNormalizer Q u hu g.val hg)

/-- A spare hyperbolic pair expresses a singular Siegel root as an actual commutator. -/
theorem singular_root_mem_omega (u w a b : V)
    (hu : Q u = 0) (hw : Q w = 0) (hb : Q b = 0)
    (huw : Q.polarBilin u w = 0) (hua : Q.polarBilin u a = 0)
    (hub : Q.polarBilin u b = 0) (hwa : Q.polarBilin w a = 0)
    (hwb : Q.polarBilin w b = 0) (hab : Q.polarBilin a b = 1) :
    siegelElement Q u w hu huw ∈ commutator (quadraticIsometrySubgroup Q) := by
  have hbw : Q.polarBilin b (-w) = 0 := by
    rw [map_neg, polar_swap Q b w, hwb, neg_zero]
  let t := root Q b (-w) hb hbw
  have htu : t.val.val u = u := by
    change siegel Q b (-w) u = u
    simp only [siegel, map_neg, huw, hub, Q.map_neg, hw, neg_zero,
      zero_smul, mul_zero, sub_zero, add_zero]
  have hta : t.val.val a = a+w := by
    have haw : Q.polarBilin a (-w) = 0 := by rw [map_neg, polar_swap Q a w, hwa, neg_zero]
    change siegel Q b (-w) a = a+w
    simp only [siegel, haw, hab, Q.map_neg, hw, zero_smul, one_smul,
      zero_mul, sub_zero, add_zero, sub_neg_eq_add]
  have haw : Q.polarBilin u (a+w) = 0 := by rw [map_add, hua, huw, add_zero]
  have hc : t * root Q u a hu hua * t⁻¹ = root Q u (a+w) hu haw := by
    simpa only [htu, hta] using root_conj Q t u a hu hua
  have he : ⁅t, root Q u a hu hua⁆ = root Q u w hu huw := by
    rw [commutatorElement_def, hc]
    have hadd : root Q u (a+w) hu haw = root Q u w hu huw * root Q u a hu hua := by
      simpa only [add_comm w a] using root_add Q u w a hu huw hua
    rw [hadd]
    group
  have he' : ⁅t.val, (root Q u a hu hua).val⁆ = siegelElement Q u w hu huw :=
    congrArg (fun x : elementarySubgroup Q => x.val) he
  rw [← he']
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end ClassicalOrthogonal.A02ParabolicSections
