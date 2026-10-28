module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.Sections

/-!
# Entrywise descent of the native symplectic field centralizer

Every entry of a matrix in the literal fixed subgroup belongs to the base
field. Descending those entries preserves the symplectic equation through
the injective algebra map, giving an injective homomorphism to Sp₄(k).
Coefficient Frobenius after descent is also injective and is the actor
seen on diagonal coordinates of the Hermitian middle section.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, with the method
of H.4.4(6), printed p.381.
-/

@[expose] public section

open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F)

lemma centralizer_entry (g : centralizer σ) (i j : Index) :
    σ (g.val.val i j) = g.val.val i j :=
  congrArg (fun a : Sp F => a.val i j) ((MulAut.mem_fixedSubgroup _ _).mp g.property)

lemma centralizer_map (g : centralizer σ) : g.val.val.map σ = g.val.val := by
  ext i j
  exact centralizer_entry σ g i j

variable [FiniteDimensional k F] (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl)

def descentMatrix (g : centralizer σ) : Matrix Index Index k :=
  fun i j => (coefficientEquiv σ hdeg hne).symm
    ⟨g.val.val i j, (mem_fixedCoefficients σ _).mpr (centralizer_entry σ g i j)⟩

lemma descentMatrix_map (g : centralizer σ) :
    (descentMatrix σ hdeg hne g).map (algebraMap k F) = g.val.val := by
  ext i j
  exact congrArg Subtype.val ((coefficientEquiv σ hdeg hne).apply_symm_apply _)

lemma descentMatrix_mem (g : centralizer σ) :
    descentMatrix σ hdeg hne g ∈ Matrix.symplecticGroup (Fin 2) k := by
  rw [SymplecticGroup.mem_iff]
  apply Matrix.map_injective (algebraMap k F).injective
  simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_J, descentMatrix_map]
    using SymplecticGroup.mem_iff.mp g.val.property

/-- Entrywise descent of the actual fixed subgroup to the base-field symplectic group. -/
def centralizerDescent : centralizer σ →* Sp k where
  toFun g := ⟨descentMatrix σ hdeg hne g, descentMatrix_mem σ hdeg hne g⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.map_injective (algebraMap k F).injective
    change (descentMatrix σ hdeg hne 1).map (algebraMap k F) = (1 : Matrix Index Index k).map _
    rw [descentMatrix_map]
    exact (map_one (algebraMap k F).mapMatrix).symm
  map_mul' g h := by
    apply Subtype.ext
    apply Matrix.map_injective (algebraMap k F).injective
    change (descentMatrix σ hdeg hne (g * h)).map (algebraMap k F) =
      (descentMatrix σ hdeg hne g * descentMatrix σ hdeg hne h).map _
    rw [Matrix.map_mul, descentMatrix_map, descentMatrix_map, descentMatrix_map]
    rfl

lemma centralizerDescent_entry (g : centralizer σ) (i j : Index) :
    algebraMap k F ((centralizerDescent σ hdeg hne g).val i j) = g.val.val i j :=
  congrFun (congrFun (descentMatrix_map σ hdeg hne g) i) j

lemma centralizerDescent_injective : Function.Injective (centralizerDescent σ hdeg hne) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  simpa only [centralizerDescent_entry] using
    congrArg (fun a : Sp k => algebraMap k F (a.val i j)) he

/-- Coefficient Frobenius after the actual base-field descent. -/
def frobeniusDescent [CharP k 2] : centralizer σ →* Sp k where
  toFun g := ⟨(centralizerDescent σ hdeg hne g).val.map (frobenius k 2),
    SymplecticGroup.map_mem (centralizerDescent σ hdeg hne g).property (frobenius k 2)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change ((centralizerDescent σ hdeg hne (g * h)).val.map (frobenius k 2)) = _
    rw [map_mul]
    exact Matrix.map_mul

lemma frobeniusDescent_entry [CharP k 2] (g : centralizer σ) (i j : Index) :
    (frobeniusDescent σ hdeg hne g).val i j = (centralizerDescent σ hdeg hne g).val i j ^ 2 := rfl

lemma frobeniusDescent_injective [CharP k 2] : Function.Injective (frobeniusDescent σ hdeg hne) := by
  intro g h he
  apply centralizerDescent_injective σ hdeg hne
  apply Subtype.ext
  ext i j
  apply frobenius_inj k 2
  exact congrArg (fun a : Sp k => a.val i j) he
end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
