module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Marked
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Sylow marking for the Hermitian tensor overgroup

The standard unitriangular subgroup of SL₃ is Sylow. Its surjective image
in the actual inner actor remains Sylow, even when the cover has a scalar
kernel. Extending this inner Sylow to the overgroup gives the literal
intersection required by the marking. Relative normality of the inner
actor then transports any elementary inner actor into the marked subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467; the H.4.2 marked flag, printed p.380.
-/

@[expose] public section

open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.LinearThree
open Matrix.PSL3.CartanActions.BorelQuotient
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

/-- The cover maps onto the actual inner actor, with its scalar kernel retained. -/
def coverToInner : Cover n →* innerActor n M :=
  (coverToOvergroup n M hM).codRestrict (innerActor n M) (fun g => ⟨g,rfl⟩)

theorem coverToInner_surjective : Function.Surjective (coverToInner n M hM) := by
  intro x
  obtain ⟨g,hg⟩ := x.property
  exact ⟨g, Subtype.ext (Subtype.ext hg)⟩

/-- The image of the literal upper unitriangular Sylow of SL₃. -/
def innerSylow : Sylow 2 (innerActor n M) :=
  (unipotentSLSylow (E n) (by have := Nat.pos_of_ne_zero (NeZero.ne n); omega)
    (card_E n)).mapSurjective (coverToInner_surjective n M hM)

theorem innerSylow_map :
    (innerSylow n M hM : Subgroup (innerActor n M)).map (innerActor n M).subtype =
      unipotentActor n M hM := by
  change ((unipotentSL (E n)).map (coverToInner n M hM)).map _ = _
  rw [Subgroup.map_map, ← specialLinear_range, ← MonoidHom.range_comp]
  rfl

/-- A genuine Sylow witness for the minimizing-actor marking. -/
theorem exists_markedSylow : ∃ T : Sylow 2 M, IsMarkedSylow n M hM T := by
  obtain ⟨T,hT⟩ := (innerSylow n M hM).exists_comap_subtype_eq
  refine ⟨T, ?_⟩
  have he := congrArg (fun P : Subgroup (innerActor n M) =>
    P.map (innerActor n M).subtype) hT
  rw [innerSylow_map] at he
  change (T : Subgroup M) ⊓ innerActor n M = _
  rw [← he]
  ext x
  constructor
  · rintro ⟨hx,hi⟩
    exact ⟨⟨x,hi⟩,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,x.property⟩

/-- Conjugate an elementary inner actor into the marked unitriangular image. -/
theorem elementary_conjugate_le_unipotent (A : Subgroup M)
    (hA : IsElementaryTwo A) (hAI : A ≤ innerActor n M) :
    ∃ g : M, A.map (MulAut.conj g).toMonoidHom ≤ unipotentActor n M hM := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let _ : (innerActor n M).Normal := by
    rw [innerActor_eq_residual n M hM]
    infer_instance
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨T,hT⟩ := exists_markedSylow n M hM
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M S T
  refine ⟨g, ?_⟩
  rw [← hT]
  apply le_inf
  · have hST : (S : Subgroup M).map (MulAut.conj g).toMonoidHom = T :=
      congrArg Sylow.toSubgroup hg
    exact (Subgroup.map_mono hS).trans_eq hST
  · rintro _ ⟨a,ha,rfl⟩
    exact Subgroup.Normal.conj_mem (inferInstance : (innerActor n M).Normal) a (hAI ha) g

end CFSG.Quasithin.ChapterK.Linear.Tensor
