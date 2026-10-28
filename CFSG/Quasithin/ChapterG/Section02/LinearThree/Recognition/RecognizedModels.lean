module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Assembly
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.ProjectiveTheorem

/-!
# The recognized natural and contragredient G.2.5 layers

The proved three-dimensional G.1.3 theorem discharges the universal
recognition parameter of `Hypothesis.recognized_layers`. Thus the two
literal quotients have their homogeneous natural and dual models, their
marked internal direct sums, and the existing counting/restriction data.
The canonical quotient projections, actors, and relative normality
instances are exactly those of the conditional assembly.

Only the genuine earlier structural inputs remain: the source product
for S, the star comparison, and the identification of U* with its point
radical. Their producer and the subsequent Cartan calculations remain
with the original layer-generation assembly owner. This theorem has no
recognition callback and allows both multiplicities to be zero.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.2.5(4,6–7),
printed pp.335–336, PDF pp.346–347; G.1.3, printed p.327.
-/

public section
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

/-- Original G.2.5 layer recognition with the genuine G.1.3 premise discharged. -/
theorem recognized_layers_from_projective (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hprod : (S D g h : Set G) = (W D g h : Set G) *
      (conjugate (W D g h) g : Set G) * (conjugate (W D g h) h : Set G))
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) :
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
  apply recognized_layers d hUT hf hLI hU hUg hUh hprod e hrad
  let := field_char_two d
  exact Projective.recognitionImplication

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
