module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Standard
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Ambient
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Alignment

/-!
# Swapping centralizer geometry

The standard matrix calculation proves the fixed Sylow intersection and
generation with the standard unipotent subgroup. The ambient transfer retains
the original Sylow and the actual socle marking. Fixed-Sylow alignment, proved
by descent of cocycles in the actual Borel normalizer, connects these calculations
at the supplied Sylow subgroup. Their assembly below proves the exact
`hgeometry` input of the external-member construction.

The earlier conditional interfaces are retained. The final theorems discharge
their alignment premise. Marked conjugacy and the involution supplement remain
the explicit inputs supplied by the external-member assembly; no additional
premise about its quotient is used. These geometry theorems do not assert the
completed source E.1.14(1) branch.

Source: Aschbacher--Smith E.1.1--2, E.1.5 and E.1.14(1), printed
pp.209--210,214; fixed-group realization 16.1.4(7), printed p.1171.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry
open DiagramAutomorphisms GraphFieldFixedResidual
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Conditional discharge of the source centralizer geometry. The remaining
premise is transitivity of the fixed Suzuki group on graph-field-stable
symplectic Sylow subgroups. The original ambient `T` is retained. -/
theorem centralizer_geometry_of_fixed_sylow_alignment
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (T : Sylow 2 G) {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 < f) (hodd : Odd f)
    (halign : ∀ S : Sylow 2 (Sp F),
      (S : Subgroup (Sp F)).map (graphFieldAut (f / 2)).toMonoidHom = S →
      ∃ k : Sp F, k ∈ (graphFieldAut (f / 2)).fixedSubgroup ∧
        unipotent.map (MulAut.conj k).toMonoidHom = (S : Subgroup (Sp F)))
    (t : G) (htT : t ∈ T) (h : Sp F)
    (hnorm : extensionAction L e t =
      MulAut.conj h * ExceptionalGraph.graphAut ^ f * (MulAut.conj h)⁻¹)
    (hsplit : L ⊔ zpowers t = ⊤) :
    let D := centralizer ({t} : Set G)
    (∃ R : Sylow 2 D, (R : Subgroup D) = (T : Subgroup G).subgroupOf D) ∧
      D ⊔ (T : Subgroup G) = ⊤ := by
  have hdeg : 2 * (f / 2) + 1 = f := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hm : 0 < f / 2 := by omega
  have hF' : Nat.card F = 2 ^ (2 * (f / 2) + 1) := by rwa [hdeg]
  let e' := (MulAut.conj h).trans e
  have ha : extensionAction L e' t = graphFieldAut (f / 2) := by
    apply normalized_marking_action L e t h (f / 2)
    simpa only [graphFieldAut, hdeg] using hnorm
  obtain ⟨S, hS, hstable⟩ := exists_marked_sylow L e' T t htT
  rw [ha] at hstable
  obtain ⟨k, hk, hSk⟩ := halign S hstable
  obtain ⟨hfixed, hgen⟩ := Standard.geometry_at_aligned_sylow (f / 2) hm hF' S k hk hSk
  exact geometry_of_marked_model L e' T t htT hsplit (f / 2) ha S hS hfixed hgen

/-- The literal `hgeometry` input of the external-member assembly follows
from fixed-Sylow alignment. Its cocycle and involution-supplement assumptions
remain exactly the explicit assumptions of that consumer. -/
theorem normalized_hgeometry_of_fixed_sylow_alignment
    (e : Sp F ≃* generalizedFitting G) (T : Sylow 2 G)
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f) (hodd : Odd f)
    (hq : 2 < Nat.card F) (A : Subgroup G) (hAT : A ≤ (T : Subgroup G))
    (halign : ∀ S : Sylow 2 (Sp F),
      (S : Subgroup (Sp F)).map (graphFieldAut (f / 2)).toMonoidHom = S →
      ∃ k : Sp F, k ∈ (graphFieldAut (f / 2)).fixedSubgroup ∧
        unipotent.map (MulAut.conj k).toMonoidHom = (S : Subgroup (Sp F))) :
    ∀ t ∈ A, t ∉ diagramKernel (generalizedFitting G) e hq → orderOf t = 2 →
      ∀ h : Sp F, extensionAction (generalizedFitting G) e t =
        MulAut.conj h * ExceptionalGraph.graphAut ^ f * (MulAut.conj h)⁻¹ →
      generalizedFitting G ⊔ zpowers t = ⊤ →
      let D := centralizer ({t} : Set G)
      (∃ R : Sylow 2 D, (R : Subgroup D) = (T : Subgroup G).subgroupOf D) ∧
        D ⊔ (T : Subgroup G) = ⊤ := by
  intro t htA _ _ h hnorm hsplit
  exact centralizer_geometry_of_fixed_sylow_alignment (generalizedFitting G) e T
    hF hf hodd halign t (hAT htA) h hnorm hsplit

/-- The centralizer of a marked swapping element intersects the original Sylow
in a Sylow and generates the ambient group with it. Fixed-Sylow alignment is
discharged by the concrete Borel cocycle calculation. -/
theorem centralizer_geometry
    (L : Subgroup G) [L.Normal] (e : Sp F ≃* L)
    (T : Sylow 2 G) {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 < f) (hodd : Odd f)
    (t : G) (htT : t ∈ T) (h : Sp F)
    (hnorm : extensionAction L e t =
      MulAut.conj h * ExceptionalGraph.graphAut ^ f * (MulAut.conj h)⁻¹)
    (hsplit : L ⊔ zpowers t = ⊤) :
    let D := centralizer ({t} : Set G)
    (∃ R : Sylow 2 D, (R : Subgroup D) = (T : Subgroup G).subgroupOf D) ∧
      D ⊔ (T : Subgroup G) = ⊤ := by
  apply centralizer_geometry_of_fixed_sylow_alignment L e T hF hf hodd ?_
    t htT h hnorm hsplit
  have hdeg : 2 * (f / 2) + 1 = f := by
    obtain ⟨m, hm⟩ := hodd
    omega
  exact Alignment.exists_fixed_conjugator (f / 2) (by rwa [hdeg])

/-- Discharge the literal `hgeometry` input of
`exists_external_member_of_normalized_calculations`, retaining its marked
conjugacy and involution-supplement inputs and the original ambient Sylow. -/
theorem normalized_hgeometry
    (e : Sp F ≃* generalizedFitting G) (T : Sylow 2 G)
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f) (hodd : Odd f)
    (hq : 2 < Nat.card F) (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    ∀ t ∈ A, t ∉ diagramKernel (generalizedFitting G) e hq → orderOf t = 2 →
      ∀ h : Sp F, extensionAction (generalizedFitting G) e t =
        MulAut.conj h * ExceptionalGraph.graphAut ^ f * (MulAut.conj h)⁻¹ →
      generalizedFitting G ⊔ zpowers t = ⊤ →
      let D := centralizer ({t} : Set G)
      (∃ R : Sylow 2 D, (R : Subgroup D) = (T : Subgroup G).subgroupOf D) ∧
        D ⊔ (T : Subgroup G) = ⊤ := by
  intro t htA _ _ h hnorm hsplit
  exact centralizer_geometry (generalizedFitting G) e T hF hf hodd
    t (hAT htA) h hnorm hsplit

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry
