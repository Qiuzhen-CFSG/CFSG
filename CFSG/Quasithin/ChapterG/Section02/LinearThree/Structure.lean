module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Reduction
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel

/-!
# The structural branch of G.2.5

The point-parabolic calculation identifies U* with the elementary abelian
radical of order 2^(2n), and its three original marked conjugates generate
L*. The normalizing two-core supplement lifts that generation to I=LU.
The central-kernel theorem then gives S=WWᵍWʰ, with no generation, radical,
root-lift or kernel-triviality premise left to discharge, including when n=1.

The quotient comparison comes from the literal star projection and preserves
the natural conjugation action. The proved containment L≤I also supplies the
missing input to the central first layer and the ordered pair-intersection
product. `Structure.RecognitionApplications` applies these outputs to the
independent recognition branch without changing that branch's interfaces.

Only the earlier G.2.2 conclusions U≤T and Φ(U)≤V₁ remain explicit, as
permitted by this branch's contract. Their producer is `qt-g02-central-closure`
under `qt-g-02`; the parent `qt-g02-linear-three` retains full G.2.5 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5, printed pp.335–336, and G.2.3, printed pp.333–334.
-/

public section
open Subgroup Matrix
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

include d

/-- Starred generation places the original L, and hence the original g,h, in I. -/
theorem L_le_I (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : D.L ≤ I D g h :=
  d.L_le_I_of_star (d.star_I_eq_star_L hUT hf).ge

/-- G.2.5(2), with the actual three marked generators of I. -/
theorem I_eq_LU (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : I D g h = D.L ⊔ D.U :=
  d.I_eq_LU_of_star (d.star_I_eq_star_L hUT hf).ge

/-- The literal set product LU in G.2.5(2). -/
theorem I_product (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (I D g h : Set G) = (D.L : Set G) * (D.U : Set G) :=
  d.I_product_of_star hUT (d.star_I_eq_star_L hUT hf).ge

/-- G.2.5(3), discharging every input to central-kernel elimination. -/
theorem S_eq_WProduct (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : S D g h = WProduct D g h :=
  d.S_eq_WProduct_of_star hUT (d.star_I_eq_star_L hUT hf)
    (d.starUEquiv hUT hf) (d.commutator_V_U_eq_point hUT hf)

/-- The ordered three-factor set product in G.2.5(3), with the original g,h. -/
theorem S_eq_product (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (S D g h : Set G) = (W D g h : Set G) * (conjugate (W D g h) g : Set G) *
      (conjugate (W D g h) h : Set G) := by
  rw [d.S_eq_WProduct hUT hf]
  exact d.WProduct_eq_product hUT (d.star_I_eq_star_L hUT hf).ge

/-- The two-core normalizes U, as required by both recognition layers. -/
theorem S_normalizes_U (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    S D g h ≤ normalizer (D.U : Set G) :=
  d.S_normalizes_U_of_star hUT (d.star_I_eq_star_L hUT hf).ge

/-- The same normalization holds for each original marked conjugate. -/
theorem S_normalizes_marked (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (x : G) (hx : x ∈ D.L) :
    S D g h ≤ normalizer (conjugate D.U x : Set G) :=
  d.S_normalizes_marked_of_star hUT (d.star_I_eq_star_L hUT hf).ge x hx

/-- The kernel of the star map on I is its own two-core, by relative normality. -/
theorem S_eq_star_kernel (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    S D g h = I D g h ⊓ D.LT.pCoreIn 2 :=
  d.S_eq_star_kernel_of_star hUT (d.star_I_eq_star_L hUT hf).ge

/-- The actual I/O₂(I) model, with starred generation proved from the source data. -/
noncomputable def sourceCoreQuotientEquiv (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (I D g h ⧸ pCore 2 (I D g h)) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
  d.coreQuotientEquiv hUT (d.star_I_eq_star_L hUT hf)

/-- Compatibility with the literal restricted star projection, on every i∈I. -/
theorem sourceCoreQuotientEquiv_mk (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (i : I D g h) :
    d.sourceCoreQuotientEquiv hUT hf (QuotientGroup.mk' (pCore 2 (I D g h)) i) =
      d.model (d.IStarProjection hUT (d.star_I_eq_star_L hUT hf) i) :=
  d.coreQuotientEquiv_mk hUT (d.star_I_eq_star_L hUT hf) i

/-- On the original L this is the originally supplied star/model map. -/
theorem sourceCoreQuotientEquiv_on_L (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (l : D.L) :
    d.sourceCoreQuotientEquiv hUT hf (QuotientGroup.mk' (pCore 2 (I D g h))
      (inclusion (d.L_le_I hUT hf) l)) = d.model (starProjection D l) :=
  d.coreQuotientEquiv_on_L hUT (d.star_I_eq_star_L hUT hf) l

/-- The constructed quotient model acts by the actual ambient conjugation on V. -/
theorem sourceCoreQuotientEquiv_equivariant (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (i : I D g h) (v : D.V) :
    (d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩).toAdd =
      (d.sourceCoreQuotientEquiv hUT hf
        (QuotientGroup.mk' (pCore 2 (I D g h)) i)).val *ᵥ (d.coordinates v).toAdd :=
  d.coreQuotientEquiv_equivariant hUT (d.star_I_eq_star_L hUT hf) i v

/-- Apply L≤I to the parent's central first-layer theorem. -/
theorem central_first_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.V ≤ S D g h ⊓ centralizer (S D g h : Set G) :=
  d.central_first hUT (d.L_le_I hUT hf)

/-- Apply L≤I to the parent's literal ordered product defining the third layer. -/
theorem S₃_product_of_source (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (S₃ D g h : Set G) =
      ((W D g h ⊓ conjugate (W D g h) g : Subgroup G) : Set G) *
        ((W D g h ⊓ conjugate (W D g h) h : Subgroup G) : Set G) *
        ((conjugate (W D g h) g ⊓ conjugate (W D g h) h : Subgroup G) : Set G) :=
  d.S₃_product hUT hf (d.L_le_I hUT hf)

/-- G.2.5(1–3) from the genuine source hypothesis and precisely the two earlier
G.2.2 outputs. The first commutator uses the actual induced starred action. -/
theorem structural (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.star D.U = (D.star (D.L ⊓ D.G₁)).pCoreIn 2 ∧
    Nonempty (D.star D.U ≃* Multiplicative (Fin 2 → F)) ∧
    IsElementaryAbelian 2 (D.star D.U) ∧
    Nat.card (D.star D.U) = 2 ^ (2 * n) ∧
    D.V₁ = Subgroup.closure {x : G | ∃ u : D.star D.U, ∃ v : D.V,
      (d.coordinates.symm (d.starAction u (d.coordinates v)) : G) * (v : G)⁻¹ = x} ∧
    I D g h = D.L ⊔ D.U ∧
    (I D g h : Set G) = (D.L : Set G) * (D.U : Set G) ∧
    (S D g h : Set G) = (W D g h : Set G) * (conjugate (W D g h) g : Set G) *
      (conjugate (W D g h) h : Set G) :=
  ⟨d.star_U_eq_point_core hUT hf, ⟨d.starUEquiv hUT hf⟩,
    d.star_U_elementary hUT hf, d.card_star_U hUT hf,
    (d.starAction_commutator_eq_point hUT hf).symm, d.I_eq_LU hUT hf,
    d.I_product hUT hf, d.S_eq_product hUT hf⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
