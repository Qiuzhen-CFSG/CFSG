module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ResidualGeneration
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.InnerAction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.ThompsonProduct
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Higher-field symplectic Borel geometry

The root-torus commutators put the specified Sylow subgroup inside the
Borel two-residual, so the Sylow supplement proves that the whole Borel
is two-perfect. The full semilinear classification discharges the model
Borel-fixer premise. The Thompson product makes this Borel normalize J(S)
for a normal symplectic component.

Source: Aschbacher--Smith 15.1.21(i), pp.1097--1098; the matrix inputs are
the Borel calculations of 13.8.20 and the Thompson product of 2.5.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.OrdinaryBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem normalizer_twoPerfect {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (P : Sylow 2 (Sp F)) : IsPPerfect 2 (normalizer (P : Set (Sp F))) := by
  let Q := P.subtype (P : Subgroup (Sp F)).le_normalizer
  have hR : (Q : Subgroup (normalizer (P : Set (Sp F)))) ≤
      pResidual 2 (normalizer (P : Set (Sp F))) := by
    intro x hx
    have hm := EvenBorelTorus.sylow_le_residualAt hF hn P hx
    obtain ⟨z,hz,he⟩ := hm
    exact (Subtype.ext he : z=x) ▸ hz
  have hsup := pResidual_sup_sylow_eq_top Q
  change pResidual 2 (normalizer (P : Set (Sp F))) ⊔ (Q : Subgroup _) = ⊤ at hsup
  rw [sup_of_le_left hR] at hsup
  exact (pResidual_eq_top_iff 2 _).mp hsup

theorem normalizer_fixer {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n)
    (P : Sylow 2 (Sp F)) (α : MulAut (Sp F))
    (hfix : ∀ x ∈ normalizer (P : Set (Sp F)), α x=x) : α=1 :=
  BorelActionGeometry.aut_fixing_sylow_normalizer_eq_one hF hn
    DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram P α hfix

variable {G : Type*} [Group G] [Finite G]
theorem normalizer_thompson (K : Subgroup G) [K.Normal]
    (e : K ≃* Sp F) {n : ℕ} (hn : 1<n) (hF : Nat.card F=2^n) (S : Sylow 2 G) :
    (normalizer ((S : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
  let J := Stellmacher.elementaryAbelianMaxJ (S : Subgroup G)
  have he : J = ((S : Subgroup G) ⊓ K) ⊔ (J ⊓ centralizer (K:Set G)) :=
    ThompsonInner.thompson_eq_sylow_component_sup_centralizer K e hn hF S
  rw [show Stellmacher.elementaryAbelianMaxJ (S : Subgroup G)=J from rfl,he]
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_inf
  · have hh := le_normalizer_map (H := (S : Subgroup G).subgroupOf K) K.subtype
    rwa [subgroupOf_map_subtype] at hh
  · apply le_trans (map_subtype_le _) ?_
    apply le_trans (le_centralizer_iff.mpr (show J ⊓ centralizer (K:Set G) ≤
      centralizer (K:Set G) from inf_le_right))
    exact Subgroup.centralizer_le_normalizer _
end Theory.SpecificGroups.SymplecticFour.OrdinaryBorel
