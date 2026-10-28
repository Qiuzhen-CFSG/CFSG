module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Basic

/-!
# Annihilators of invariant subspaces and the socle splitting obstruction

Annihilation reverses the lattice of subrepresentations. The quotient of the
dual by the annihilator of I is equivariantly I*, through restriction of
functionals. A complement to that annihilator therefore gives an actual
invariant complement to I. If I is nonzero and lies in the unique maximal
submodule, such a complement is impossible.

This is the linear algebra for the dual use of B.4.9(1) in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March
2004, 13.8.25, printed p.961 (PDF p.978). In particular the quotient used in
the dual argument is the dual of the chosen socle submodule.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

/-- The annihilator with its inherited contragredient action. -/
def annihilator (W : Subrepresentation ρ) : Subrepresentation ρ.dual where
  toSubmodule := W.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g := by
    intro f hf
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro v hv
    exact hf _ (W.apply_mem_toSubmodule g⁻¹ hv)

/-- The coannihilator is invariant for the original representation. -/
def coannihilator (K : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := K.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g := by
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have h := hv _ (K.apply_mem_toSubmodule g⁻¹ hf)
    change f (ρ (g⁻¹)⁻¹ v) = 0 at h
    simpa only [inv_inv] using h

@[simp] theorem coannihilator_annihilator (W : Subrepresentation ρ) :
    coannihilator ρ (annihilator ρ W) = W := by
  apply Subrepresentation.toSubmodule_injective
  exact Subspace.dualAnnihilator_dualCoannihilator_eq

variable [FiniteDimensional (ZMod 2) U]

@[simp] theorem annihilator_coannihilator (K : Subrepresentation ρ.dual) :
    annihilator ρ (coannihilator ρ K) = K := by
  apply Subrepresentation.toSubmodule_injective
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

/-- The actual order-reversing equivalence on invariant subspaces. -/
def annihilatorOrderIso : Subrepresentation ρ ≃o (Subrepresentation ρ.dual)ᵒᵈ where
  toFun := annihilator ρ
  invFun := coannihilator ρ
  left_inv := coannihilator_annihilator ρ
  right_inv := annihilator_coannihilator ρ
  map_rel_iff' := by
    intro W X
    exact Subspace.dualAnnihilator_le_dualAnnihilator_iff

/-- Irreducibility of I is exactly maximality of its annihilator. -/
theorem annihilator_isCoatom (I : Subrepresentation ρ) (hI : IsAtom I) :
    IsCoatom (annihilator ρ I) :=
  (annihilatorOrderIso ρ).isAtom_iff I |>.mpr hI

omit [FiniteDimensional (ZMod 2) U] in
/-- Restriction of functionals identifies the quotient with the dual of I. -/
noncomputable def annihilatorQuotientEquiv (I : Subrepresentation ρ) :
    (Module.Dual (ZMod 2) U ⧸ (annihilator ρ I).toSubmodule) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) I.toSubmodule :=
  Subspace.quotAnnihilatorEquiv I.toSubmodule

omit [FiniteDimensional (ZMod 2) U] in
theorem annihilatorQuotientEquiv_equivariant (I : Subrepresentation ρ) (g : H)
    (q : Module.Dual (ZMod 2) U ⧸ (annihilator ρ I).toSubmodule) :
    annihilatorQuotientEquiv ρ I ((annihilator ρ I).quotientRepresentation g q) =
      I.toRepresentation.dual g (annihilatorQuotientEquiv ρ I q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    change Subspace.quotAnnihilatorEquiv I.toSubmodule
      (Submodule.Quotient.mk (ρ.dual g f)) =
        I.toRepresentation.dual g
          (Subspace.quotAnnihilatorEquiv I.toSubmodule (Submodule.Quotient.mk f))
    simp only [Subspace.quotAnnihilatorEquiv_apply]
    rfl

omit [FiniteDimensional (ZMod 2) U] in
/-- The chief factor over zero is the literal action on the chosen atom. -/
theorem naturalOrDual_atom (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (I : Subrepresentation ρ) (hI : IsAtom I) : IsNaturalOrDual I.toRepresentation eH := by
  let K := sectionLower ρ ⊥ I
  have hK : K.toSubmodule = ⊥ := by
    ext v
    change (v : U) = 0 ↔ v = 0
    constructor
    · exact fun h => Subtype.ext h
    · exact fun h => congrArg Subtype.val h
  let e := (K.toSubmodule.quotEquivOfEqBot hK).symm
  apply naturalOrDual_of_equivariant I.toRepresentation (sectionRepresentation ρ ⊥ I)
    e (fun _ _ => rfl) eH
  exact (hchief ⊥ I hI.bot_covBy).1

omit [FiniteDimensional (ZMod 2) U] in
/-- The natural-or-dual quotient of the dual is identified through I*,
using the original actor equivalence. -/
theorem annihilator_quotient_naturalOrDual
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hchief : ChiefFactorsNaturalOrDual ρ eH)
    (I : Subrepresentation ρ) (hI : IsAtom I) :
    IsNaturalOrDual (annihilator ρ I).quotientRepresentation eH :=
  naturalOrDual_of_equivariant _ _ (annihilatorQuotientEquiv ρ I)
    (annihilatorQuotientEquiv_equivariant ρ I) eH
    (naturalOrDual_dual I.toRepresentation eH (naturalOrDual_atom ρ eH hchief I hI))

/-- A common center on I supplies the common axis on the actual quotient
of the ambient dual by I's annihilator. -/
theorem annihilator_quotient_commonAxis (I : Subrepresentation ρ) (A : Subgroup H)
    (h : HasCommonCenter I.toRepresentation A) :
    HasCommonAxis (annihilator ρ I).quotientRepresentation A :=
  commonAxis_of_equivariant _ _ (annihilatorQuotientEquiv ρ I)
    (annihilatorQuotientEquiv_equivariant ρ I) A h.dual

/-- Dual complements yield invariant complements in the original module. -/
theorem complement_of_annihilator_complement (I : Subrepresentation ρ)
    (K : Subrepresentation ρ.dual)
    (hi : annihilator ρ I ⊓ K = ⊥) (hs : annihilator ρ I ⊔ K = ⊤) :
    I ⊓ coannihilator ρ K = ⊥ ∧ I ⊔ coannihilator ρ K = ⊤ := by
  have he := annihilator_coannihilator ρ K
  constructor
  · apply (annihilatorOrderIso ρ).injective
    change annihilator ρ (I ⊓ coannihilator ρ K) = annihilator ρ ⊥
    have hm := (annihilatorOrderIso ρ).map_inf I (coannihilator ρ K)
    change annihilator ρ (I ⊓ coannihilator ρ K) =
      annihilator ρ I ⊔ annihilator ρ (coannihilator ρ K) at hm
    rw [hm, he, hs]
    exact ((annihilatorOrderIso ρ).map_bot).symm
  · apply (annihilatorOrderIso ρ).injective
    change annihilator ρ (I ⊔ coannihilator ρ K) = annihilator ρ ⊤
    have hm := (annihilatorOrderIso ρ).map_sup I (coannihilator ρ K)
    change annihilator ρ (I ⊔ coannihilator ρ K) =
      annihilator ρ I ⊓ annihilator ρ (coannihilator ρ K) at hm
    rw [hm, he, hi]
    exact ((annihilatorOrderIso ρ).map_top).symm

/-- A nonzero submodule lying in the unique maximal submodule cannot have
an invariant complement. This is the obstruction needed for the dual use. -/
theorem not_complement_of_le_unique_maximal (W I : Subrepresentation ρ)
    (hW : IsCoatom W) (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (hI : I ≠ ⊥) (hIW : I ≤ W) :
    ¬ ∃ C : Subrepresentation ρ, I ⊓ C = ⊥ ∧ I ⊔ C = ⊤ := by
  rintro ⟨C, hi, hs⟩
  have hC : C ≠ ⊤ := by
    intro he
    rw [he, inf_top_eq] at hi
    exact hI hi
  have hCW := proper_le_unique_maximal ρ W hunique C hC
  have ht : (⊤ : Subrepresentation ρ) ≤ W := by
    rw [← hs]
    exact sup_le hIW hCW
  exact hW.ne_top (top_le_iff.mp ht)

/-- The annihilator of a nonzero submodule of the unique maximal submodule
has no complement in the dual module. -/
theorem not_annihilator_complement_of_le_unique_maximal (W I : Subrepresentation ρ)
    (hW : IsCoatom W) (hunique : ∀ X : Subrepresentation ρ, IsCoatom X → X = W)
    (hI : I ≠ ⊥) (hIW : I ≤ W) :
    ¬ ∃ K : Subrepresentation ρ.dual,
      annihilator ρ I ⊓ K = ⊥ ∧ annihilator ρ I ⊔ K = ⊤ := by
  rintro ⟨K, hi, hs⟩
  exact not_complement_of_le_unique_maximal ρ W I hW hunique hI hIW
    ⟨coannihilator ρ K, complement_of_annihilator_complement ρ I K hi hs⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
