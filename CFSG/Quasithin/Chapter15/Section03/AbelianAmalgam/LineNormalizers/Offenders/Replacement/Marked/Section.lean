module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.PairedSection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Inheritance
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The actual binary line section

Restrict the faithful conjugation action to the ambient group and quotient
by the binary subspace of the actual subgroup `E`. The action kernel is
exactly the quotient centralizer, identified with the original section
kernel on restriction to the temporary normalizer.

The marked subspaces are images of the raw `C_U(τ)` in this literal quotient.
They consist of fixed quotient vectors; equality with the full fixed space,
complementary decomposition and centralizer invariance remain separate
geometric assertions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.MarkedSection
variable {G D : Type*} [Group G] [Group D]
  (U E : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] [E.Normal]
  (f : G →* D) (hf : Function.Surjective f)
  (hker : f.ker = centralizer (U : Set G))

/-- The invariant binary subspace of the actual denominator. -/
noncomputable def lineSubrepresentation : Subrepresentation
    ((Representation.NormalElementaryQuotient.representation U f hf hker).comp f) where
  toSubmodule := Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)
  apply_mem_toSubmodule g := by
    intro v hv
    change ((Representation.NormalElementaryQuotient.representation U f hf hker
      (f g) v).toMul : G) ∈ E
    rw [Representation.NormalElementaryQuotient.representation_apply]
    exact (inferInstance : E.Normal).conj_mem _ hv g

/-- Conjugation on the literal binary quotient by `E`. -/
noncomputable def action : Representation (ZMod 2) G
    (Additive U ⧸ Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)) :=
  (lineSubrepresentation U E f hf hker).quotientRepresentation

/-- The quotient action agrees with conjugation on representatives. -/
theorem action_mk (g : G) (v : Additive U) :
    action U E f hf hker g
      ((Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)).mkQ v) =
    (Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)).mkQ
      (Representation.NormalElementaryQuotient.representation U f hf hker (f g) v) := rfl

/-- Trivial section action is precisely the original commutator criterion. -/
theorem action_eq_one_iff (g : G) : action U E f hf hker g = 1 ↔
    ∀ u ∈ U, ⁅u, g⁆ ∈ E := by
  let N := Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)
  constructor
  · intro hg u hu
    have he := LinearMap.congr_fun hg (N.mkQ (Additive.ofMul ⟨u, hu⟩))
    change N.mkQ (Representation.NormalElementaryQuotient.representation U f hf hker
      (f g) (Additive.ofMul ⟨u, hu⟩)) = N.mkQ (Additive.ofMul ⟨u, hu⟩) at he
    have hmem := (Submodule.Quotient.eq N).mp he
    change ((Representation.NormalElementaryQuotient.representation U f hf hker
      (f g) (Additive.ofMul ⟨u, hu⟩)).toMul : G) / u ∈ E at hmem
    rw [div_eq_mul_inv, Representation.NormalElementaryQuotient.representation_apply] at hmem
    rw [← commutatorElement_inv]
    exact E.inv_mem hmem
  · intro hg
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change N.mkQ (Representation.NormalElementaryQuotient.representation U f hf hker
        (f g) v) = N.mkQ v
      apply (Submodule.Quotient.eq N).mpr
      change ((Representation.NormalElementaryQuotient.representation U f hf hker
        (f g) v).toMul : G) / (v.toMul : G) ∈ E
      rw [div_eq_mul_inv, Representation.NormalElementaryQuotient.representation_apply]
      change ⁅g, (v.toMul : G)⁆ ∈ E
      rw [← commutatorElement_inv]
      exact E.inv_mem (hg v.toMul v.toMul.property)

/-- The section action has exactly the quotient-centralizer kernel. -/
theorem action_ker : (action U E f hf hker).ker = centralizerModulo ⊤ U E := by
  ext g
  rw [MonoidHom.mem_ker, action_eq_one_iff, mem_centralizerModulo_iff]
  simp only [mem_top, true_and]

/-- The image of the raw fixed space in the actual quotient. -/
noncomputable def fixedImage (τ : G) : Submodule (ZMod 2)
    (Additive U ⧸ Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)) :=
  (Representation.NormalElementaryQuotient.subspace U
    ((centralizer ({τ} : Set G)).subgroupOf U)).map
      (Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)).mkQ

omit [U.Normal] [E.Normal] in
/-- Membership retains a literal fixed representative. -/
theorem mem_fixedImage_iff (τ : G)
    (w : Additive U ⧸ Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)) :
    w ∈ fixedImage U E τ ↔ ∃ v : Additive U,
      (v.toMul : G) ∈ centralizer ({τ} : Set G) ∧
        (Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U)).mkQ v = w := Iff.rfl

/-- A fixed representative gives a fixed quotient vector. -/
theorem fixedImage_fixed (τ : G)
    (w : Additive U ⧸ Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U))
    (hw : w ∈ fixedImage U E τ) : action U E f hf hker τ w = w := by
  obtain ⟨v, hv, rfl⟩ := (mem_fixedImage_iff U E τ w).mp hw
  rw [action_mk]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [Representation.NormalElementaryQuotient.representation_apply]
  rw [← mem_centralizer_singleton_iff.mp hv, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.MarkedSection

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G D : Type*} [Group G] [Group D]

/-- In the temporary normalizer the kernel is the restriction of the original `K`. -/
theorem temporary_section_action_ker (T V E : Subgroup G)
    [((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal]
    [IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))]
    [(E.subgroupOf (temporaryLineNormalizer T V E)).Normal]
    (hUH : lineV V E ≤ temporaryLineNormalizer T V E)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      (((lineV V E).subgroupOf (temporaryLineNormalizer T V E)) : Set (temporaryLineNormalizer T V E))) :
    (MarkedSection.action ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
      (E.subgroupOf (temporaryLineNormalizer T V E)) f hf hker).ker =
      (Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E) := by
  ext g
  rw [MonoidHom.mem_ker, MarkedSection.action_eq_one_iff]
  change (∀ u : temporaryLineNormalizer T V E, (u : G) ∈ lineV V E →
    ⁅(u : G), (g : G)⁆ ∈ E) ↔ (g : G) ∈ Descent.sectionKernel V E
  rw [Descent.mem_sectionKernel_iff V E (hUH.trans inf_le_left)]
  exact ⟨fun h => ⟨g.property.1, fun u hu => h ⟨u, hUH hu⟩ hu⟩,
    fun h u hu => h.2 u hu⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
