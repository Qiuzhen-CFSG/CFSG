module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Presentation
public import Theory.SpecificGroups.G2.RootPresentationRecognition.BruhatCollection
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.WeylAction
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry

/-!
# Faithfulness of the full characteristic-two G₂ presentation

The internal Bruhat collector puts every presented word in an alternating
Borel double cell. Concrete Weyl geometry excludes every nonidentity cell
from the evaluation kernel. Positive coordinate injectivity and the disjoint
split torus then kill the remaining Borel kernel. Concrete root/Weyl generation
makes evaluation surjective, giving the specified full-model equivalence.

This proves presentation faithfulness without an order bound, simplicity,
or an assumed homomorphism from the model to the unknown source group.
It holds over every field of characteristic two. The two geometric exclusion
calculations adapt the licensed ATLAS port's SolvableSylowPlacement proofs.
Source: DGS, Groups and Graphs, Theorem D, p.224; GLS III, §2.3.
-/

@[expose] public noncomputable section
namespace Atlas.G2.RootPresentationRecognition
open Subgroup Atlas.SplitOctonion Explicit LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- The positive part of the model data is the entire actual unipotent group. -/
theorem model_positive : (modelData (F := F)).toPositiveRoots.generated = unipotent := by
  ext g
  change g ∈ (modelRoots (F := F)).generated ↔ g ∈ unipotent
  rw [PositiveRoots.mem_generated_iff _ model_collectionRelations, unipotent_eq_range]
  rfl

omit [CharP F 2] in
/-- The generated Borel in the model is the full Borel, including its torus. -/
theorem model_borel : (modelData (F := F)).borel = borel := by
  change (modelData (F := F)).toPositiveRoots.generated ⊔ torusHom.range = borel
  rw [model_positive]
  rfl

omit [CharP F 2] in
private theorem negative_long_not_mem_borel :
    weylR * rootE (1 : F) * weylR⁻¹ ∉ borel := by
  intro h
  have hp := borel_le_shortPlaneStabilizer h
  have hz := hp.1 (basisVector 1) (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  simp [weylR, weylREquiv, weylRLinear, weylRApply,
    rootE, rootEEquiv, rootELinear, rootEApply, basisVector] at hz

omit [CharP F 2] in
private theorem negative_short_not_mem_borel :
    weylS * rootF (1 : F) * weylS⁻¹ ∉ borel := by
  intro h
  have hp := parabolic_le_pointStabilizer (borel_le_parabolic₂ h)
  obtain ⟨a, ha⟩ := (mem_pointStabilizer_iff _).mp hp
  have hz := congrArg (fun x : Carrier F => x 1) ha
  simp [weylS, weylSEquiv, weylSLinear, weylSApply,
    rootF, rootFEquiv, rootFLinear, rootFApply, basisVector] at hz

/-- None of the eleven nonidentity Weyl representatives belongs to the Borel. -/
theorem model_weyl_not_borel (i : Fin 12) (hi : i ≠ 0) :
    SolvableSylowPlacement.weylRep (F := F) i ∉ borel := by
  intro hw
  obtain ⟨x,hx,h⟩ := SolvableSylowPlacement.exists_negative_simple_conjugate (F := F) i hi
  have hc := borel.mul_mem (borel.mul_mem hw (mem_sup_left hx)) (borel.inv_mem hw)
  rcases h with h | h
  · rw [h] at hc
    exact negative_long_not_mem_borel hc
  · rw [h] at hc
    exact negative_short_not_mem_borel hc

/-- A nonempty alternating word of length at most six cannot enter the Borel. -/
theorem model_alternating_not_borel (short : Bool) (n : ℕ) (hn : n ≤ 6) (hpos : 0 < n) :
    (modelData (F := F)).alternating short n ∉ borel := by
  cases short
  · interval_cases n
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 1 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 3 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 5 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 7 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 9 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 11 (by decide)
  · interval_cases n
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 2 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 4 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 6 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 8 (by decide)
    · simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 10 (by decide)
    · rw [← BorelWeylData.alternating_longest modelData model_relations]
      simpa [BorelWeylData.alternating, BorelWeylData.reflection, modelData,
        SolvableSylowPlacement.weylRep, mul_assoc] using model_weyl_not_borel (F := F) 11 (by decide)

namespace Presentation

omit [CharP F 2] in
theorem whole_eq_top : (data (F := F)).whole = ⊤ := by
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by relators data.whole _ g
  intro z
  cases z with
  | root i a =>
      exact subset_closure (Or.inl (BorelWeylData.root_mem_borel data i a))
  | torus p => exact subset_closure (Or.inl (BorelWeylData.torus_mem_borel data p))
  | r => exact subset_closure (Or.inr (by simp [data]))
  | s => exact subset_closure (Or.inr (by simp [data]))

@[simp] theorem evaluation_product (t : Fin 6 → F) :
    evaluation ((data (F := F)).product t) = unipotentProduct t :=
  lift_product modelData model_relations t

@[simp] theorem evaluation_torus (p : Fˣ × Fˣ) :
    evaluation ((data (F := F)).torus p) = torusHom p := lift_torus modelData model_relations p

@[simp] theorem evaluation_reflection (short : Bool) :
    evaluation ((data (F := F)).reflection short) = (modelData (F := F)).reflection short := by
  cases short
  · exact lift_r modelData model_relations
  · exact lift_s modelData model_relations

@[simp] theorem evaluation_alternating (short : Bool) (n : ℕ) :
    evaluation ((data (F := F)).alternating short n) = (modelData (F := F)).alternating short n := by
  induction n generalizing short with
  | zero => exact evaluation.map_one
  | succ n ih => simp only [BorelWeylData.alternating, map_mul, evaluation_reflection, ih]

/-- The evaluation sends the entire abstract Borel into the actual full Borel. -/
theorem evaluation_borel_mem {b : Group F} (hb : b ∈ data.borel) :
    evaluation b ∈ borel := by
  obtain ⟨t,p,rfl⟩ := (BorelWeylData.mem_borel_iff data relations b).mp hb
  rw [map_mul,evaluation_product,evaluation_torus]
  exact Subgroup.mul_mem _ (mem_sup_left (unipotentProduct_mem t)) (mem_sup_right ⟨p,rfl⟩)

/-- Positive coordinate faithfulness and disjointness from the split torus
prove faithfulness on the abstract Borel. -/
theorem borel_kernel_trivial (b : Group F) (hb : b ∈ data.borel) (h : evaluation b = 1) : b = 1 := by
  obtain ⟨t,p,rfl⟩ := (BorelWeylData.mem_borel_iff data relations b).mp hb
  rw [map_mul,evaluation_product,evaluation_torus] at h
  have he : unipotentProduct t = (torusHom p)⁻¹ := eq_inv_of_mul_eq_one_left h
  have ht : unipotentProduct t ∈ splitTorus := by
    rw [he]
    exact Subgroup.inv_mem _ ⟨p,rfl⟩
  have hu : unipotentProduct t = 1 :=
    Subgroup.disjoint_def.mp unipotent_disjoint_torus (unipotentProduct_mem t) ht
  have ht0 : t = 0 := unipotentProduct_injective (hu.trans unipotentProduct_zero.symm)
  have hp : p = 1 := torusHom_injective (by simpa only [hu,one_mul,map_one] using h)
  rw [ht0,hp,PositiveRoots.product_zero,map_one,mul_one]

/-- Internal Bruhat collection puts the kernel in the Borel. This is the
missing kernel inclusion, rather than an assumed presentation isomorphism. -/
theorem evaluation_injective : Function.Injective (evaluation (F := F)) := by
  apply (injective_iff_map_eq_one evaluation).mpr
  intro g hg
  have hc := BorelWeylData.bruhat_collection data relations
    (g := g) (show g ∈ data.whole by rw [whole_eq_top]; trivial)
  obtain ⟨a,b,short,n,ha,hb,hn,rfl⟩ := hc
  have hw : (modelData (F := F)).alternating short n ∈ borel := by
    have he : (modelData (F := F)).alternating short n =
        (evaluation a)⁻¹ * (evaluation b)⁻¹ := by
      rw [map_mul,map_mul,evaluation_alternating] at hg
      calc
        _ = (evaluation a)⁻¹ *
            (evaluation a * (modelData (F := F)).alternating short n * evaluation b) *
              (evaluation b)⁻¹ := by group
        _ = _ := by rw [hg,mul_one]
    rw [he]
    exact borel.mul_mem (borel.inv_mem (evaluation_borel_mem ha))
      (borel.inv_mem (evaluation_borel_mem hb))
  have hn0 : n = 0 := by
    by_contra hne
    exact model_alternating_not_borel short n hn (Nat.pos_of_ne_zero hne) hw
  simp only [hn0,BorelWeylData.alternating_zero,mul_one] at hg ⊢
  exact borel_kernel_trivial _ (Subgroup.mul_mem _ ha hb) hg

/-- The full displayed generators cover every concrete octonion automorphism. -/
theorem evaluation_surjective : Function.Surjective (evaluation (F := F)) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← generated_eq_top (F := F)]
  apply sup_le
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with hg | hg
    · rw [unipotent_eq_range] at hg
      obtain ⟨t,rfl⟩ := hg
      exact ⟨data.product t,evaluation_product t⟩
    · rcases hg with rfl | rfl
      · exact ⟨data.r,lift_r modelData model_relations⟩
      · exact ⟨data.s,lift_s modelData model_relations⟩
  · rintro g ⟨p,rfl⟩
    exact ⟨data.torus p,evaluation_torus p⟩

/-- The proved full G₂ Borel–Weyl presentation, including characteristic two
fields of orders two and four. -/
def equivalence : Group F ≃* Model F :=
  MulEquiv.ofBijective evaluation ⟨evaluation_injective,evaluation_surjective⟩

@[simp] theorem equivalence_apply (g : Group F) : equivalence g = evaluation g := rfl

end Presentation
end Atlas.G2.RootPresentationRecognition
