module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Faithfulness
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryException

/-!
# Recognition from the proved G₂ presentation

The inverse of the proved presentation evaluation constructs a homomorphism
from the concrete octonion model into any group with the stated generators
and equations. Target generation makes it surjective. For fields larger than
two, simplicity of the concrete model and the surviving A(1) marker exclude
its kernel. For the binary field the full group is not simple: instead every
nontrivial normal subgroup contains the long-root normal closure and A(1).
Field transport gives the same separate argument for every field of order two.

The result retains the full model, all six roots, the full split torus, and
both Weyl generators. No simplicity or centerlessness of the target is used.
Source: DGS, Groups and Graphs, Theorem D, p.224, finite split G₂ row.
-/

@[expose] public noncomputable section
namespace Atlas.G2.RootPresentationRecognition
open Subgroup
variable {F G : Type*} [Field F] [CharP F 2] [_root_.Group G]

namespace BorelWeylData
variable (d : BorelWeylData F G) (R : d.Relations)

/-- The proved presentation constructs the previously missing model map. -/
def modelHom : Model F →* G := (Presentation.lift d R).comp Presentation.equivalence.symm.toMonoidHom

@[simp] theorem modelHom_root (i : Fin 6) (a : F) :
    d.modelHom R ((modelData (F := F)).x i a) = d.x i a := by
  have he : Presentation.equivalence ((Presentation.data (F := F)).x i a) =
      (modelData (F := F)).x i a := Presentation.lift_root modelData model_relations i a
  rw [← he]
  change Presentation.lift d R (Presentation.equivalence.symm
    (Presentation.equivalence ((Presentation.data (F := F)).x i a))) = _
  rw [MulEquiv.symm_apply_apply,Presentation.lift_root]

@[simp] theorem modelHom_torus (p : Fˣ × Fˣ) :
    d.modelHom R (torusHom p) = d.torus p := by
  rw [← Presentation.evaluation_torus p, ← Presentation.equivalence_apply]
  change Presentation.lift d R (Presentation.equivalence.symm
    (Presentation.equivalence ((Presentation.data (F := F)).torus p))) = _
  rw [MulEquiv.symm_apply_apply,Presentation.lift_torus]

@[simp] theorem modelHom_r : d.modelHom R weylR = d.r := by
  have he : Presentation.equivalence (Presentation.data (F := F)).r = weylR :=
    Presentation.lift_r modelData model_relations
  rw [← he]
  change Presentation.lift d R (Presentation.equivalence.symm
    (Presentation.equivalence (Presentation.data (F := F)).r)) = _
  rw [MulEquiv.symm_apply_apply,Presentation.lift_r]

@[simp] theorem modelHom_s : d.modelHom R weylS = d.s := by
  have he : Presentation.equivalence (Presentation.data (F := F)).s = weylS :=
    Presentation.lift_s modelData model_relations
  rw [← he]
  change Presentation.lift d R (Presentation.equivalence.symm
    (Presentation.equivalence (Presentation.data (F := F)).s)) = _
  rw [MulEquiv.symm_apply_apply,Presentation.lift_s]

include R in
/-- Generation of this same target gives surjectivity, with no simplicity input. -/
theorem modelHom_surjective (hgen : d.whole = ⊤) : Function.Surjective (d.modelHom R) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with hg | hg
  · obtain ⟨t,p,rfl⟩ := (mem_borel_iff d R g).mp hg
    apply Subgroup.mul_mem
    · unfold PositiveRoots.product
      have hx (i : Fin 6) : d.x i (t i) ∈ (d.modelHom R).range :=
        ⟨modelData.x i (t i),modelHom_root d R i (t i)⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hx 0) (hx 1)) (hx 2)) (hx 3)) (hx 4)) (hx 5)
    · exact ⟨torusHom p,modelHom_torus d R p⟩
  · rcases hg with rfl | rfl
    · exact ⟨weylR,modelHom_r d R⟩
    · exact ⟨weylS,modelHom_s d R⟩

end BorelWeylData

/-- The full binary group is not simple. Its least nontrivial normal subgroup
contains A(1), which is exactly the marker needed to exclude a kernel. -/
theorem binary_hom_injective (f : Model (ZMod 2) →* G) (hA : f (rootA 1) ≠ 1) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hne
  exact hA ((BinaryException.H_le_normal f.ker hne) (BinaryException.rootA_in_H 1))

variable [Finite F]

omit [CharP F 2] in
/-- The binary branch is transported through the actual field equivalence;
for larger fields only simplicity of the known concrete model is used. -/
theorem hom_injective_of_highest_root (f : Model F →* G) (hA : f (rootA 1) ≠ 1) :
    Function.Injective f := by
  by_cases hq : 2 < Nat.card F
  · let : IsSimpleGroup (Model F) := isSimple hq
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hA (show rootA 1 ∈ f.ker by rw [h]; trivial)).elim
  · have hcard : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    let e : Model (ZMod 2) ≃* Model F := fieldEquiv (binaryFieldEquiv hcard).symm
    have he : e (rootA 1) = rootA 1 := by
      dsimp only [e]
      rw [fieldEquiv_rootA,map_one]
    have hf : Function.Injective (f.comp e.toMonoidHom) :=
      binary_hom_injective _ (by simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,he] using hA)
    intro x y h
    obtain ⟨a,rfl⟩ := e.surjective x
    obtain ⟨b,rfl⟩ := e.surjective y
    exact congrArg e (hf h)

namespace BorelWeylData
variable (d : BorelWeylData F G) (R : d.Relations)
  (hgen : d.whole = ⊤) (hA : d.x 0 1 ≠ 1)

/-- Recognition of the full model, with a separate binary kernel argument. -/
def equivalence : G ≃* Model F :=
  (MulEquiv.ofBijective (d.modelHom R)
    ⟨hom_injective_of_highest_root _ (by
        change d.modelHom R ((modelData (F := F)).x 0 1) ≠ 1
        rw [modelHom_root]
        exact hA), modelHom_surjective d R hgen⟩).symm

@[simp] theorem equivalence_root (i : Fin 6) (a : F) :
    d.equivalence R hgen hA (d.x i a) = (modelData (F := F)).x i a := by
  apply (d.equivalence R hgen hA).symm.injective
  change _ = d.modelHom R ((modelData (F := F)).x i a)
  rw [MulEquiv.symm_apply_apply,modelHom_root]

@[simp] theorem equivalence_torus (p : Fˣ × Fˣ) :
    d.equivalence R hgen hA (d.torus p) = torusHom p := by
  apply (d.equivalence R hgen hA).symm.injective
  change _ = d.modelHom R (torusHom p)
  rw [MulEquiv.symm_apply_apply,modelHom_torus]

@[simp] theorem equivalence_r : d.equivalence R hgen hA d.r = weylR := by
  apply (d.equivalence R hgen hA).symm.injective
  change _ = d.modelHom R weylR
  rw [MulEquiv.symm_apply_apply,modelHom_r]

@[simp] theorem equivalence_s : d.equivalence R hgen hA d.s = weylS := by
  apply (d.equivalence R hgen hA).symm.injective
  change _ = d.modelHom R weylS
  rw [MulEquiv.symm_apply_apply,modelHom_s]

end BorelWeylData
omit [CharP F 2] [Finite F] in
/-- The generator closure is precisely the roots, the torus range and R,S. -/
theorem BorelWeylData.whole_eq_generator_closure (d : BorelWeylData F G) :
    d.whole = Subgroup.closure
      ((Set.range (fun p : Fin 6 × F => d.x p.1 p.2) ∪ Set.range d.torus) ∪ {d.r,d.s}) := by
  simp only [BorelWeylData.whole,Subgroup.closure_union,Subgroup.closure_eq,
    BorelWeylData.borel,PositiveRoots.generated,← MonoidHom.coe_range,Subgroup.closure_eq]

namespace Presentation

/-- Finiteness follows from the proved faithful model evaluation. -/
instance finite : Finite (Group F) := Finite.of_injective evaluation evaluation_injective

/-- The exact finite order follows after, rather than as a premise of, faithfulness. -/
theorem card_presentation : Nat.card (Group F) =
    Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr equivalence.toEquiv,card_Model]

end Presentation

end Atlas.G2.RootPresentationRecognition
