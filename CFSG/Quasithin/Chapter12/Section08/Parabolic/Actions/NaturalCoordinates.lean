module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalCoordinates.Marking
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalCoordinates.TensorModel
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.Assembly

/-!
# Literal natural coordinates and the parabolic action clauses

Starting with exactly the earlier source inputs of `binary_source_natural_quotient`,
we first mark the two conjugate order-two images in the S₃ quotient. We then
instantiate the natural tensor theorem with that marked equivalence, choose a
finite basis of its multiplicity space, and construct `ParabolicNaturalModule`
for the original g. Zero multiplicity is allowed.

The final application proves all three literal action clauses of 12.8.9(4–6).
Its sole additional input is the earlier center-intersection identity
V ∩ Z(U) = V₁ from 12.8.8(3). The setup/preliminary producers and the parent
12.8.9–10 assembly retain the discharge of these genuine earlier-source inputs.
No model, marking, coordinate or relative-normality premise remains.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.9, printed pp.852–853 (PDF pp.869–870), refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise TensorProduct
open InvertedCubicTensor
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Construct the literal marked natural module from the earlier 12.8.3–8
source inputs. No coordinate, representation, nonzero multiplicity or
internality assumption on the original g is needed. -/
theorem binary_source_parabolic_natural_module (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ m : ℕ, Nonempty (F.ParabolicNaturalModule L g (Fin m)) := by
  obtain ⟨e, _, hgen, _, _, _, _, _, hfactor, hPH, hcore, hindex, _⟩ :=
    F.binary_generation hn L hL hfull hkernel hcomm hsquare hspan hne g hgP hgH
  obtain ⟨e', u, h, hu, huw, hX, hmarkU, hmarkX⟩ :=
    F.binary_marked_quotient L g hgP hgH hfactor hPH hgen.symm e hcore hindex
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e' hcore hindex
  have hEcomm := F.binary_intersection_commutator hn L hL g hgP hgH hgen.symm hcomm hindex
  let := F.binary_source_E_normal_in_core L hL g hgP hgen.symm hcomm
  let := F.binary_source_quotient_elementary L hL g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  obtain ⟨σ, d, _, hfinite, ⟨j, hj⟩, hfixed⟩ :=
    F.binary_natural_quotient L hL g hgP hfactor hPH hgen.symm e' hcore hindex hcomm hsquare
  let := hfinite
  exact F.parabolic_natural_module_of_tensor L g hgen.symm hsplit hEcomm e' u h hu huw
    hX hmarkU hmarkX σ d j hj (hfixed u hu huw).1

/-- Actual application to 12.8.9(4–6), discharging all natural-model and
relative-normality premises of the action assembly. The center-intersection
input is the genuine earlier 12.8.8(3), retained for the parent source assembly. -/
theorem binary_source_parabolic_action_clauses (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (hcenter : V ⊓ F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (∀ y : F.X g, (y : G) ∉ F.W →
      F.tilde F.U ⊓ centralizer ({F.tildeProjection
        ⟨y, F.X_le_H g (F.P_le_G₂ hn L hL hgP) y.property⟩} : Set F.G₁tilde) ≤
          F.tilde F.W) ∧
    (F.xHatKernel g (F.P_le_G₂ hn L hL hgP) = F.E g ∧
      F.xTildeKernel g (F.P_le_G₂ hn L hL hgP) = F.E g) ∧
    (∀ u : F.U, (u : G) ∉ F.W →
      (F.xHatStabilizer g (F.P_le_G₂ hn L hL hgP)
        (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
          (conjugate F.ZU g : Set G) * (F.E g : Set G)) := by
  obtain ⟨m, ⟨M⟩⟩ := F.binary_source_parabolic_natural_module hn L hL hfull hkernel
    hcomm hsquare hspan hne g hgP hgH
  obtain ⟨_, _, hgen, _, _, hIN, _, _, hfactor, hPH, hcore, _, _⟩ :=
    F.binary_generation hn L hL hfull hkernel hcomm hsquare hspan hne g hgP hgH
  let := hIN
  let : ((F.E g).subgroupOf (F.I₂ L)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (F.binary_source_E_normalized L hL g hgP hgen.symm hcomm)
  exact F.parabolic_action_clauses L hL hn g hgP hgH M hcomm hcenter hspan hne
    hfactor hPH hcore
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
