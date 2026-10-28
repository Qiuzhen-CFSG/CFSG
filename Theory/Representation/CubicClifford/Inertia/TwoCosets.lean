module

public import Theory.Representation.CubicClifford.Inertia.Isotypic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Projection

/-!
# Two cosets and an irreducible inertia block

Clifford's theorem (Isaacs, Theorem 6.5) and an index-two overgroup reduce an
ambient irreducible representation to two translates of an invariant block.
If the translates are disjoint, every simple submodule of the block equals
the block. Addition gives an actual intertwining equivalence to a product,
with the second action conjugated using `gkg⁻¹`.

This is the linear-algebra part of the conditional inertia construction used
for Aschbacher–Smith 13.8.21(1), printed p.956.
-/

public section

noncomputable section

open scoped MonoidAlgebra

namespace Representation.CubicClifford.Inertia

variable {F H V : Type*} [Field F] [Group H] [AddCommGroup V] [Module F V]

private lemma sup_toSubmodule (ρ : Representation F H V) (A B : Subrepresentation ρ) :
    (A ⊔ B).toSubmodule = A.toSubmodule ⊔ B.toSubmodule := by
  let e : Subrepresentation ρ ≃o Submodule F[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have he := e.map_sup A B
  have he' := congrArg (fun p : Submodule F[H] ρ.asModule => p.restrictScalars F) he
  rw [Submodule.restrictScalars_sup] at he'
  exact he'

private lemma conjugate_eq_or_eq (ρ : Representation F H V) (K I : Subgroup H) [K.Normal]
    (hindex : I.index = 2) (g : H) (hg : g ∉ I)
    (C : Subrepresentation (ρ.comp K.subtype))
    (hstable : ∀ x : I, conjugateSubrepresentationOrderIso ρ K (x : H) C = C)
    (x : H) : conjugateSubrepresentationOrderIso ρ K x C = C ∨
      conjugateSubrepresentationOrderIso ρ K x C =
        conjugateSubrepresentationOrderIso ρ K g⁻¹ C := by
  by_cases hx : x ∈ I
  · exact Or.inl (hstable ⟨x, hx⟩)
  · right
    have hmem : g * x ∈ I := (I.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hg hx)
    rw [show x = g⁻¹ * (g * x) by group, conjugateSubrepresentationOrderIso_mul,
      hstable ⟨g * x, hmem⟩]

/-- Index two reduces the Clifford summands to two translates of any
I-invariant subrepresentation containing the chosen simple constituent. -/
lemma pair_sup_top [Finite H] (ρ : Representation F H V) [IsIrreducible ρ]
    (K I : Subgroup H) [K.Normal] (hindex : I.index = 2) (g : H) (hg : g ∉ I)
    (A C : Subrepresentation (ρ.comp K.subtype)) (hA : IsIrreducible A.toRepresentation)
    (hle : A ≤ C)
    (hstable : ∀ x : I, conjugateSubrepresentationOrderIso ρ K (x : H) C = C) :
    C ⊔ conjugateSubrepresentationOrderIso ρ K g⁻¹ C = ⊤ := by
  classical
  obtain ⟨n, t, hint, _, _, _⟩ := isaacs_theorem_6_5.{_, _, _, 0} ρ K inferInstance A hA
  let e : Subrepresentation (ρ.comp K.subtype) ≃o Submodule F[K] (Representation.asModule (ρ.comp K.subtype)) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  apply e.injective
  rw [e.map_top]
  apply top_unique
  rw [← hint.submodule_iSup_eq_top]
  refine iSup_le fun i => ?_
  change e (conjugateSubrepresentation ρ K A (t i)) ≤ e _
  apply e.monotone
  have he : conjugateSubrepresentation ρ K A (t i) =
      conjugateSubrepresentationOrderIso ρ K (t i)⁻¹ A := by simp
  rw [he]
  apply ((conjugateSubrepresentationOrderIso ρ K (t i)⁻¹).monotone hle).trans
  rcases conjugate_eq_or_eq ρ K I hindex g hg C hstable (t i)⁻¹ with h | h
  · rw [h]; exact le_sup_left
  · rw [h]; exact le_sup_right

private lemma inner_conjugate (ρ : Representation F H V) (I : Subgroup H) [I.Normal]
    (B : Subrepresentation (ρ.comp I.subtype)) (x : I) :
    conjugateSubrepresentationOrderIso ρ I (x : H) B = B := by
  apply Subrepresentation.toSubmodule_injective
  rw [conjugateSubrepresentationOrderIso_toSubmodule]
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact B.apply_mem_toSubmodule x hw
  · intro v hv
    refine ⟨ρ (x : H)⁻¹ v, B.apply_mem_toSubmodule x⁻¹ hv, ?_⟩
    simp

/-- A nonzero I-subrepresentation disjoint from its other coset translate
is irreducible: a simple submodule and its translate already span the ambient module. -/
lemma block_irreducible [Finite H] [FiniteDimensional F V]
    (ρ : Representation F H V) [IsIrreducible ρ]
    (I : Subgroup H) [I.Normal] (hindex : I.index = 2) (g : H) (hg : g ∉ I)
    (S : Subrepresentation (ρ.comp I.subtype)) (hne : S ≠ ⊥)
    (hdisj : Disjoint S.toSubmodule (Submodule.map (ρ g⁻¹) S.toSubmodule)) :
    IsIrreducible S.toRepresentation := by
  obtain ⟨B, hB, hBS⟩ := (eq_bot_or_exists_atom_le S).resolve_left hne
  have hBsimple := (Subrepresentation.irreducible_iff_isAtom B).mpr hB
  have htop := pair_sup_top ρ I I hindex g hg B B hBsimple le_rfl (inner_conjugate ρ I B)
  have htop' : B.toSubmodule ⊔ Submodule.map (ρ g⁻¹) B.toSubmodule = ⊤ := by
    have he := congrArg Subrepresentation.toSubmodule htop
    rw [sup_toSubmodule, conjugateSubrepresentationOrderIso_toSubmodule] at he
    exact he
  have hSB : S ≤ B := by
    intro v hv
    have hvtop : v ∈ B.toSubmodule ⊔ Submodule.map (ρ g⁻¹) B.toSubmodule := by
      rw [htop']; trivial
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hvtop
    have hcS : c ∈ S.toSubmodule := by
      have he : c = v - b := eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hbc)
      rw [he]
      exact S.toSubmodule.sub_mem hv (hBS hb)
    have hcS' : c ∈ Submodule.map (ρ g⁻¹) S.toSubmodule := Submodule.map_mono hBS hc
    have hc0 : c = 0 := (Submodule.disjoint_def.mp hdisj) c hcS hcS'
    have hbv : b = v := by simpa [hc0] using hbc
    exact hbv ▸ hb
  have heq : S = B := le_antisymm hSB hBS
  rw [heq]
  exact hBsimple

/-- Regard an actual constituent as a subrepresentation of a larger invariant subspace. -/
def occurrence_in_larger (ρ : Representation F H V) (A C : Subrepresentation ρ)
    (_hle : A ≤ C) : Subrepresentation C.toRepresentation where
  toSubmodule := A.toSubmodule.comap C.toSubmodule.subtype
  apply_mem_toSubmodule h _v hv := A.apply_mem_toSubmodule h hv

/-- Passing an occurrence into a containing subrepresentation preserves its representation. -/
def occurrence_equiv (ρ : Representation F H V) (A C : Subrepresentation ρ) (hle : A ≤ C) :
    (occurrence_in_larger ρ A C hle).toRepresentation ≃ₗ A.toRepresentation := by
  refine RepEquiv.mk (A.toSubmodule.comapSubtypeEquivOfLe hle) ?_
  intro h
  ext v
  rfl

private def sumEquiv (ρ : Representation F H V) (A B : Subrepresentation ρ)
    (hdisj : Disjoint A.toSubmodule B.toSubmodule) (htop : A ⊔ B = ⊤) :
    Representation.Equiv (Representation.prod A.toRepresentation B.toRepresentation) ρ := by
  have htop' : A.toSubmodule ⊔ B.toSubmodule = ⊤ := by
    rw [← sup_toSubmodule, htop]; rfl
  refine Representation.Equiv.mk
    (Submodule.prodEquivOfIsCompl _ _ ⟨hdisj, codisjoint_iff.mpr htop'⟩) ?_
  intro h
  apply LinearMap.ext
  intro v
  change ρ h (v.1 : V) + ρ h (v.2 : V) = ρ h ((v.1 : V) + (v.2 : V))
  exact (map_add _ _ _).symm

/-- Addition and inverse ambient transport give the actual product equivalence.
The second factor has action `k ↦ ρ(gkg⁻¹)`, hence uses the subspace `ρ(g⁻¹)C`. -/
def productEquiv (ρ : Representation F H V) (K : Subgroup H) [K.Normal]
    (C : Subrepresentation (ρ.comp K.subtype)) (g : H)
    (hdisj : Disjoint C.toSubmodule (Submodule.map (ρ g⁻¹) C.toSubmodule))
    (htop : C ⊔ conjugateSubrepresentationOrderIso ρ K g⁻¹ C = ⊤) :
    Representation.Equiv (ρ.comp K.subtype)
      (Representation.prod C.toRepresentation (conjugateRep C.toRepresentation g)) := by
  let D := conjugateSubrepresentationOrderIso ρ K g⁻¹ C
  have hd : Disjoint C.toSubmodule D.toSubmodule := by
    simpa only [D, conjugateSubrepresentationOrderIso_toSubmodule] using hdisj
  let e := (sumEquiv (ρ.comp K.subtype) C D hd htop).symm
  let f : D.toRepresentation ≃ₗ conjugateRep C.toRepresentation g := by
    have f : D.toRepresentation ≃ₗ conjugateRep C.toRepresentation (g⁻¹)⁻¹ :=
      conjugateSubrepresentationEquiv ρ K C (g⁻¹)⁻¹
    simpa only [inv_inv] using f
  apply e.trans
  refine Representation.Equiv.mk
    (LinearEquiv.prodCongr (LinearEquiv.refl F C.toSubmodule) f.toLinearEquiv) ?_
  intro k
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · rfl
  · exact f.isIntertwining k v.2

end Representation.CubicClifford.Inertia
