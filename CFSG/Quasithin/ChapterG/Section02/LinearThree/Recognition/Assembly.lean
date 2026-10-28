module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry

/-!
# Recognition of both literal G.2.5 layers

The six frame roots prove I-invariance of S₃. The dual and natural orbit
maps satisfy every G.1.3 clause on the canonical quotient actions, so the
universal earlier recognition theorem supplies homogeneous coordinates.
The marked-model arguments identify all six summands, including multiplicity
zero. Their ambient-conjugation equations also construct the existing
counting and L₁-restriction interface with its original actors and maps.

Only the earlier G.2.2 and G.2.5(1–3) structural conclusions and the universal
G.1.3 implication remain inputs. The source assembly owners discharge these;
no I-invariance, point-map criterion, marked order, or module decomposition
is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.3 and G.2.5(4,6–7), printed pp.327–328,335–336.
-/

@[expose] public section
noncomputable section
universe uG uF
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Subgroup Setup Projective
open scoped Pointwise IsMulCommutative
attribute [local instance] ZMod.algebra

namespace Hypothesis
variable {G : Type uG} [Group G] [Finite G] {D : Setup G}
  {F : Type uF} [Field F] [Finite F] {n : ℕ} {g h : G}
  (d : LinearThree.Hypothesis D F n g h)

/-- The source series consists of relatively I-normal subgroups, and its
third term is the literal product printed in G.2.5(4). -/
theorem invariant_series (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) :
    (D.V ≤ S₂ D g h ∧ S₂ D g h ≤ S₃ D g h ∧ S₃ D g h ≤ S D g h) ∧
    D.V ≤ centralizer (S D g h : Set G) ∧
    (D.V.subgroupOf (I D g h)).Normal ∧
    ((S₂ D g h).subgroupOf (I D g h)).Normal ∧
    ((S₃ D g h).subgroupOf (I D g h)).Normal ∧
    ((S D g h).subgroupOf (I D g h)).Normal ∧
    (S₃ D g h : Set G) =
      ((W D g h ⊓ conjugate (W D g h) g : Subgroup G) : Set G) *
      ((W D g h ⊓ conjugate (W D g h) h : Subgroup G) : Set G) *
      ((conjugate (W D g h) g ⊓ conjugate (W D g h) h : Subgroup G) : Set G) := by
  exact ⟨d.series_inclusions hUT hf hLI, (d.central_first hUT hLI).trans inf_le_right,
    normal_subgroupOf_of_le_normalizer (d.I_normalizes hUT),
    (d.intersection hUT hf).2.2.1,
    normal_subgroupOf_of_le_normalizer
      (DualGeometry.I_normalizes_third d hUT hf hLI hU hUg hUh e hrad),
    normal_subgroupOf_of_le_normalizer (I_normalizes_core D g h),
    d.S₃_product hUT hf hLI⟩

variable [CharP F 2]

/-- Apply the genuine universal G.1.3 implication to the constructed dual
point map. The output retains the exact quotient projection and L* action. -/
theorem lower_recognition (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e)
    (recognize : RecognitionImplication.{uF, uG, uF, uG} F) :
    letI := lower_normal d hUT hf hLI
    letI := lower_elementary d hUT hf hLI
    ∃ s : ℕ, Nonempty (DualGeometry.MarkedModel.Model d e s) := by
  let := lower_normal d hUT hf hLI
  let := lower_elementary d hUT hf hLI
  obtain ⟨_, σ, a, φ, hq, hc, _⟩ :=
    DualGeometry.lower_projective_geometry d hUT hf hLI hU hUg hUh hgen e hrad
  obtain ⟨s, c, he⟩ := recognize (D.star D.L) (Module.Dual F (Fin 3 → F))
    (dualAction d) (DualGeometry.dualMarking d) (Additive (LowerQuotient D g h)) σ φ hc
  exact ⟨s, ⟨⟨σ, a, hq, c, he⟩⟩⟩

section Marked
variable [((S₂ D g h).subgroupOf (S₃ D g h)).Normal]
  [((S₃ D g h).subgroupOf (S D g h)).Normal]
  [IsElementaryAbelian 2 (LowerQuotient D g h)]
  [IsElementaryAbelian 2 (UpperQuotient D g h)]
  {hLI : D.L ≤ I D g h} {e : StarComparison D g h hLI} {r s : ℕ}

/-- Combine the proved dual and natural marks in the exact interface consumed
by the order and local-residual restriction proofs. -/
def markedLayers (lower : DualGeometry.MarkedModel.Model d e s)
    (upper : NaturalGeometry.Model d e r)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
    (hrad : UpperRadicalIdentification d e) : ChiefFactors.MarkedLayers d hLI r s :=
  lower.toMarkedLayers hUT hf (DualGeometry.marked_model_bridges d e hrad)
    upper.coordinates upper.coordinates_equivariant
    (upper.marked_coordinates hUT hf hU hgen hrad).1

end Marked

omit [CharP F 2] in
/-- G.2.5(6–7) with both canonical quotient actions, homogeneous models,
literal internal direct sums, and the actual marked counting/restriction
interface. Full I-invariance is a conclusion, discharged by the frame roots.
The two multiplicities range over all natural numbers, including zero. -/
theorem recognized_layers (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hprod : (S D g h : Set G) = (W D g h : Set G) *
      (conjugate (W D g h) g : Set G) * (conjugate (W D g h) h : Set G))
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e)
    (recognize : letI := field_char_two d; RecognitionImplication.{uF, uG, uF, uG} F) :
    letI := field_char_two d
    I D g h ≤ normalizer (S₃ D g h : Set G) ∧
    letI := lower_normal d hUT hf hLI
    letI : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
      normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
    letI := lower_elementary d hUT hf hLI
    letI := upper_elementary d hUT hf hLI hU hUg hUh hprod
    ∃ (r s : ℕ) (_lower : DualGeometry.MarkedModel.Model d e s)
      (_upper : NaturalGeometry.Model d e r),
      (let A := lowerImage D g h (W D g h ⊓ conjugate (W D g h) g)
       let B := lowerImage D g h (W D g h ⊓ conjugate (W D g h) h)
       let C := lowerImage D g h (conjugate (W D g h) g ⊓ conjugate (W D g h) h)
       Disjoint A B ∧ IsCompl (A ⊔ B) C) ∧
      (let A := upperImage D g h (W D g h)
       let B := upperImage D g h (conjugate (W D g h) g)
       let C := upperImage D g h (conjugate (W D g h) h)
       Disjoint A B ∧ IsCompl (A ⊔ B) C) ∧
      Nonempty (ChiefFactors.MarkedLayers d hLI r s) := by
  let := field_char_two d
  have hN := DualGeometry.I_normalizes_third d hUT hf hLI hU hUg hUh e hrad
  refine ⟨hN, ?_⟩
  let := lower_normal d hUT hf hLI
  let : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
    normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
  let := lower_elementary d hUT hf hLI
  let := upper_elementary d hUT hf hLI hU hUg hUh hprod
  have hgen := core_eq_marked_join_of_product d hLI hprod
  obtain ⟨s, ⟨lower⟩⟩ := lower_recognition d hUT hf hLI hU hUg hUh hgen e hrad recognize
  obtain ⟨r, upper, hd⟩ :=
    upper_marked_decomposition d hUT hf hLI hU hUg hUh hprod hN e hrad recognize
  exact ⟨r, s, lower, upper, lower_marked_direct d hUT hf hLI, hd,
    ⟨markedLayers d lower upper hUT hf hU hgen hrad⟩⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
