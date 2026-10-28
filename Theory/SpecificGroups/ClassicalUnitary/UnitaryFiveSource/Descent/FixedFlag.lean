module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.Flags
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent.FixedSpace
public import Mathlib.FieldTheory.Fixed

/-!
# Descending coefficient-stable subspaces to the actual fixed field

A basis of fixed vectors for the restricted semilinear involution gives
coordinates over the stored fixed subfield. Hence a stable subspace has
exactly its original dimension after descent. Inclusion of subspaces is
preserved, and the Hermitian pairing becomes the symmetric dot product.
The consumer applies this to the inverse-image line and plane from a
unitary graph-cocycle descent basis.

Source: the fixed local amalgam in Aschbacher–Smith F.4.37(2), printed
p.293 of refs/quasithin.pdf. The basis argument uses the characteristic-two
semilinear descent theorem; no averaging or field-size inequality is used.
-/

@[expose] public noncomputable section
open Matrix Module BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.Descent
namespace FixedFlag
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] (J : HermitianForm 5 F)
local notation "K" => FixedBy.subfield F J.conj

/-- The actual subspace over the stored fixed field, with coordinate inclusion into F⁵. -/
def coordinates (W : Submodule F (Fin 5 → F)) : Submodule K (Fin 5 → K) where
  carrier := {x | (fun i => (x i : F)) ∈ W}
  zero_mem' := W.zero_mem
  add_mem' := fun hx hy => W.add_mem hx hy
  smul_mem' := fun a _ hx => W.smul_mem (a:F) hx

private def conjugationOn (W : Submodule F (Fin 5 → F))
    (hW : ∀ x, J.conj ∘ x ∈ W ↔ x ∈ W) : W →+ W where
  toFun x := ⟨J.conj ∘ x.val,(hW x.val).mpr x.property⟩
  map_zero' := by ext i; exact map_zero J.conj
  map_add' x y := by ext i; exact map_add J.conj _ _

private theorem conjugationOn_smul (W : Submodule F (Fin 5 → F))
    (hW : ∀ x, J.conj ∘ x ∈ W ↔ x ∈ W) (a : F) (x : W) :
    conjugationOn J W hW (a • x) = J.conj a • conjugationOn J W hW x := by
  ext i
  exact map_mul J.conj _ _

private theorem conjugationOn_square (W : Submodule F (Fin 5 → F))
    (hW : ∀ x, J.conj ∘ x ∈ W ↔ x ∈ W) (x : W) :
    conjugationOn J W hW (conjugationOn J W hW x) = x := by
  ext i
  exact J.conj_involutive _

/-- A coefficient-stable subspace descends with exactly its original dimension. -/
theorem finrank_coordinates (hσ : J.conj ≠ 1) (W : Submodule F (Fin 5 → F))
    (hW : ∀ x, J.conj ∘ x ∈ W ↔ x ∈ W) :
    Module.finrank K (coordinates J W) = Module.finrank F W := by
  let T := conjugationOn J W hW
  have hT (a : F) (x : W) : T (a • x)=J.conj a • T x := conjugationOn_smul J W hW a x
  have hTT (x : W) : T (T x)=x := conjugationOn_square J W hW x
  classical
  obtain ⟨s,b,hb⟩ := FieldDescent.exists_fixed_basis J.conj hσ T hT hTT
  let : Finite s := Module.Finite.finite_basis b
  let : Fintype s := Fintype.ofFinite s
  have hact (c : s → F) :
      T (b.equivFun.symm c)=b.equivFun.symm (fun i => J.conj (c i)) := by
    simp only [b.equivFun_symm_apply,map_sum,hT,hb]
  have hcoord (w : W) (i : s) : b.equivFun (T w) i=J.conj (b.equivFun w i) := by
    have hh := congrArg (fun w => b.equivFun w i) (hact (b.equivFun w))
    simpa only [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply] using hh
  let vec : coordinates J W → W := fun x => ⟨fun i => (x.val i:F),x.property⟩
  have hvec (x : coordinates J W) : T (vec x)=vec x := by
    ext i
    exact (x.val i).property
  let f : coordinates J W →ₗ[K] (s → K) :=
    { toFun := fun x i => ⟨b.equivFun (vec x) i,by
        change J.conj (b.equivFun (vec x) i)=b.equivFun (vec x) i
        rw [←hcoord,hvec]⟩
      map_add' := fun x y => by
        ext i
        exact congrFun (b.equivFun.map_add (vec x) (vec y)) i
      map_smul' := fun a x => by
        ext i
        exact congrFun (b.equivFun.map_smul (a:F) (vec x)) i }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hh : vec x=vec y := b.equivFun.injective (funext fun i =>
        congrArg Subtype.val (congrFun h i))
      ext j
      exact congrArg (fun w : W => w.val j) hh
    · intro c
      let w := b.equivFun.symm (fun i => (c i:F))
      have hw : T w=w := by
        rw [hact]
        congr 1
        funext i
        exact (c i).property
      let x : coordinates J W := ⟨fun j => ⟨w.val j,
        congrArg (fun w : W => w.val j) hw⟩,w.property⟩
      refine ⟨x,?_⟩
      ext i
      exact congrFun (b.equivFun.apply_symm_apply (fun i => (c i:F))) i
  rw [(LinearEquiv.ofBijective f hf).finrank_eq,Module.finrank_eq_card_basis b]
  simp

theorem coordinates_mono {W V : Submodule F (Fin 5 → F)} (h : W ≤ V) :
    coordinates J W ≤ coordinates J V := by
  intro x hx
  exact h hx

/-- Scalar extension uses the literal coordinate inclusion of the stored subfield. -/
def scalarSpan (V : Submodule K (Fin 5 → K)) : Submodule F (Fin 5 → F) :=
  Submodule.span F ((fun x : Fin 5 → K => fun i => (x i:F)) '' (V : Set (Fin 5 → K)))

/-- Descending and then extending scalars recovers the original invariant subspace. -/
theorem scalarSpan_coordinates (hσ : J.conj≠1) (W : Submodule F (Fin 5 → F))
    (hW : ∀ x, J.conj ∘ x ∈ W ↔ x ∈ W) : scalarSpan J (coordinates J W)=W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact hx
  · let T := conjugationOn J W hW
    have hT (a : F) (x : W) : T (a • x)=J.conj a • T x := conjugationOn_smul J W hW a x
    have hTT (x : W) : T (T x)=x := conjugationOn_square J W hW x
    have hs : Submodule.span F {x : W | T x=x} ≤
        (scalarSpan J (coordinates J W)).comap W.subtype := by
      apply Submodule.span_le.mpr
      intro x hx
      let y : Fin 5 → K := fun i => ⟨x.val i,congrArg (fun x : W => x.val i) hx⟩
      exact Submodule.subset_span ⟨y,x.property,rfl⟩
    rw [FieldDescent.span_fixed J.conj hσ T hT hTT] at hs
    intro x hx
    exact hs (Submodule.mem_top : (⟨x,hx⟩ : W)∈⊤)

/-- The Hermitian pairing becomes the symmetric dot product on fixed coordinates. -/
theorem dot_zero (W : Submodule F (Fin 5 → F))
    (hW : ∀ x ∈ W, ∀ y ∈ W, IsotropicGeometry.pairing J x y=0)
    (x y : coordinates J W) : dotProduct x.val y.val=0 := by
  apply Subtype.ext
  have hh := hW (fun i => (x.val i:F)) x.property (fun i => (y.val i:F)) y.property
  change (∑ i, ((x.val i:F)*(y.val i:F)))=0
  change (∑ i, J.conj (x.val i:F)*(y.val i:F))=0 at hh
  have hx (i) : J.conj (x.val i:F)=(x.val i:F) := (x.val i).property
  simpa only [hx] using hh

end FixedFlag
end Theory.SpecificGroups.UnitaryFive.Descent
