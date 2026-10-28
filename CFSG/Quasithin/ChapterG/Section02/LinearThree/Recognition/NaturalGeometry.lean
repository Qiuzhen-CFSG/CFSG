module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry.RootAction
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry.MarkedModel

/-!
# Natural projective geometry on the literal upper G.2.5 quotient

The canonical action on S/S₃ admits a projective point map satisfying
every G.1.3 criterion clause. Its marked values are precisely the images
of W and its right conjugates under the original quotient projection.
The binary subspaces are obtained from those images; S₃≤W is never assumed.

The earlier structural and radical-identification conclusions remain
explicit inputs from qt-g025-structure. Full I-normalization of S₃ comes
from the dual geometry and is discharged by qt-g025-recognition. That
owner also discharges the universal G.1.3 recognition implication.

The proved projective criterion, followed by that universal implication,
constructs actual homogeneous natural coordinates. Root rigidity identifies
the three marked images with copies of the three source lines, proving their
internal direct sum and their orders. The conjugation equation agrees with
the literal quotient map and the chief-factor interfaces. Multiplicity zero
is retained throughout.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(7), printed pp.335–336, PDF pp.346–347.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Subgroup
open scoped IsMulCommutative Pointwise

/-- The actual image in S/S₃, regarded as a binary subspace. -/
def upperSubspace {G : Type*} [Group G] (D : Setup G) (g h : G)
    [((S₃ D g h).subgroupOf (S D g h)).Normal]
    [IsElementaryAbelian 2 (UpperQuotient D g h)] (A : Subgroup G) :
    Submodule (ZMod 2) (Additive (UpperQuotient D g h)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (upperImage D g h A))

namespace Hypothesis
open Projective Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

include d in
theorem core_eq_marked_join_of_product (hLI : D.L ≤ I D g h)
    (hprod : (S D g h : Set G) = (W D g h : Set G) *
      (conjugate (W D g h) g : Set G) * (conjugate (W D g h) h : Set G)) :
    S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h := by
  have hWg : conjugate (W D g h) g ≤ S D g h := by
    rw [conjugate_W D g h g (hLI d.g_mem)]; exact inf_le_right
  have hWh : conjugate (W D g h) h ≤ S D g h := by
    rw [conjugate_W D g h h (hLI d.h_mem)]; exact inf_le_right
  apply le_antisymm _ (sup_le (sup_le inf_le_right hWg) hWh)
  intro x hx
  have hx' : x ∈ (W D g h : Set G) * (conjugate (W D g h) g : Set G) *
      (conjugate (W D g h) h : Set G) := hprod ▸ hx
  obtain ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hx'
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left ha)) (mem_sup_left (mem_sup_right hb)))
    (mem_sup_right hc)

omit d [Field F] [Finite F] [Finite G] in
theorem canonical_image_eq_upperSubspace
    [((S₃ D g h).subgroupOf (S D g h)).Normal]
    [IsElementaryAbelian 2 (UpperQuotient D g h)]
    {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI)
    (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g h)))
    (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
      (σ.comp e.projection))
    (hq : ∀ a : S D g h, (s.coordinates a).toAdd =
      Additive.ofMul (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a))
    (A : Subgroup G) : SectionGeometry.image s A = upperSubspace D g h A := by
  ext v
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, ?_⟩
    change (s.coordinates a).toAdd = v at he
    rw [hq] at he
    exact he
  · rintro ⟨a, ha, he⟩
    apply (SectionGeometry.mem_image s A v).mpr
    exact ⟨a, ha, (hq a).trans he⟩

/-- The actual upper quotient admits the G.1.3 point map, with every
criterion clause and all three right-conjugate marks. The radical input
is precisely the earlier G.2.5(1) identification, not a recognition premise. -/
theorem upper_projective_geometry (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hprod : (S D g h : Set G) = (W D g h : Set G) *
      (conjugate (W D g h) g : Set G) * (conjugate (W D g h) h : Set G))
    (hN : I D g h ≤ normalizer (S₃ D g h : Set G))
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) :
    letI : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
      normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
    letI := upper_elementary d hUT hf hLI hU hUg hUh hprod
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g h)))
      (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
        (σ.comp e.projection))
      (φ : Point F (Fin 3 → F) → Submodule (ZMod 2) (Additive (UpperQuotient D g h))),
      (∀ a : S D g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a)) ∧
      Criterion (naturalAction d) σ φ ∧
      φ (naturalPoint d) = upperSubspace D g h (W D g h) ∧
      (∀ l : D.L, φ (conjugatePoint d l) = upperSubspace D g h (conjugate (W D g h) l)) := by
  let : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
    normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
  let := upper_elementary d hUT hf hLI hU hUg hUh hprod
  obtain ⟨σ, s, hq⟩ := upper_action d hUT hf hLI hU hUg hUh hprod hN e
  refine ⟨σ, s, naturalPointMap d e σ s, hq, ?_, ?_, ?_⟩
  · exact naturalPointMap_criterion d e σ s hUT hf hU
      (core_eq_marked_join_of_product d hLI hprod) hrad
  · rw [naturalPointMap_mark, canonical_image_eq_upperSubspace e σ s hq]
  · intro l
    rw [naturalPointMap_conjugate, canonical_image_eq_upperSubspace e σ s hq]

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition

universe uG uF
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Subgroup Setup Projective
open scoped IsMulCommutative Pointwise
attribute [local instance] ZMod.algebra
variable {G : Type uG} [Group G] [Finite G] {D : Setup G}
  {F : Type uF} [Field F] [Finite F] [CharP F 2]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

/-- Apply the genuine universal G.1.3 implication to the constructed upper
point map. The resulting coordinates identify all three marked images and
prove their literal direct sum. The earlier structural premises and G.1.3
remain explicit for their source assembly owners. -/
theorem upper_marked_decomposition (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hprod : (S D g h : Set G) = (W D g h : Set G) *
      (conjugate (W D g h) g : Set G) * (conjugate (W D g h) h : Set G))
    (hN : I D g h ≤ normalizer (S₃ D g h : Set G))
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e)
    (recognize : RecognitionImplication.{uF, uG, uF, uG} F) :
    letI : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
      normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
    letI := upper_elementary d hUT hf hLI hU hUg hUh hprod
    ∃ (r : ℕ) (_m : NaturalGeometry.Model d e r),
      let A := upperImage D g h (W D g h)
      let B := upperImage D g h (conjugate (W D g h) g)
      let C := upperImage D g h (conjugate (W D g h) h)
      Disjoint A B ∧ IsCompl (A ⊔ B) C := by
  let : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
    normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
  let := upper_elementary d hUT hf hLI hU hUg hUh hprod
  obtain ⟨σ, s, hq⟩ := upper_action d hUT hf hLI hU hUg hUh hprod hN e
  have hgen := core_eq_marked_join_of_product d hLI hprod
  have hc := naturalPointMap_criterion d e σ s hUT hf hU hgen hrad
  obtain ⟨r, c, he⟩ := recognize (D.star D.L) (Fin 3 → F) (naturalAction d)
    (naturalMarking d) (Additive (UpperQuotient D g h)) σ (naturalPointMap d e σ s) hc
  let m : NaturalGeometry.Model d e r := ⟨σ, s, hq, c, he⟩
  exact ⟨r, m, m.marked_direct hUT hf hU hgen hrad⟩

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
