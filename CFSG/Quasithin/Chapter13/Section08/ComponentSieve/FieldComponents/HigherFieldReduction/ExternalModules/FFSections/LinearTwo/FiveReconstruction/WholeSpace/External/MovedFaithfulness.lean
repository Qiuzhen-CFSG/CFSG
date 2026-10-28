module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.FullAction
public import Theory.GroupTheory.Fitting.Subgroup

/-!+# Faithfulness from the marked moved coordinates and the Fitting bound

Let N be the kernel of the ambient coordinate homomorphism. Its pointwise
A₅ and S₃ markings make N meet both K and the marked cubic X trivially.
Thus N embeds in D/K and is solvable when that quotient is solvable.
Normality gives F(N) ≤ F(D); the bound F(D) ≤ X then makes F(N) trivial.
The finite-solvable Fitting theorem forces N = 1. Coordinate uniqueness
transfers injectivity back to the original action on the given carrier.

The component marking alone also proves injectivity of the actual action
on every subgroup of K, without either structural hypothesis. This retains
the subgroup itself when applying an endpoint bound to its action image.

These results apply to the actual moved subrepresentation W. They do not
identify it with the ambient module U or eliminate a K-central complement.
The source adapter in `SourceFaithfulness` derives the two structural inputs
from the earlier solvable supplement and selected 13.8.14 alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the exceptional
external L₂(4) argument in 13.8.20, printed p.954, with 13.8.14 and
F.9.18(6a). The latter identifies W = [U,K], not W = U.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.FactorCoordinates

variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {K : Subgroup D} {s : Equiv.Perm (Fin 3) →* D}
  (c : FactorCoordinates ρ K s) [K.Normal]

/-- The actual component embeds in the coordinate group by its given A₅ marking. -/
theorem ambientHom_component_injective :
    Function.Injective (c.ambientHom.comp K.subtype) := by
  intro k l h
  apply c.component.injective
  apply Subtype.ext
  have h' := congrArg Prod.fst h
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, c.ambientHom_component] using h'

/-- Equal actions have equal ambient coordinates, by tensor-coordinate uniqueness. -/
theorem ambientHom_eq_of_action_eq {d e : D} (h : ρ d = ρ e) :
    c.ambientHom d = c.ambientHom e := by
  apply BinaryPermutation.FiveTensorNormalizer.tensor_coordinates_unique
  intro z
  obtain ⟨v, rfl⟩ := c.moduleEquiv.surjective z
  exact (c.ambientHom_intertwines d v).symm.trans
    ((congrArg (fun f : Module.End (ZMod 2) U => c.moduleEquiv (f v)) h).trans
      (c.ambientHom_intertwines e v))

include c in
/-- Every literal subgroup of K acts injectively on the coordinate module.
No ambient faithfulness, quotient solvability or Fitting bound is required. -/
theorem action_injective_on_component_subgroup (A : Subgroup D) (hA : A ≤ K) :
    Function.Injective (ρ.comp A.subtype) := by
  intro a b h
  have hf := c.ambientHom_eq_of_action_eq h
  have he : (⟨a.val, hA a.property⟩ : K) = ⟨b.val, hA b.property⟩ :=
    c.ambientHom_component_injective hf
  exact Subtype.ext (congrArg (fun k : K => (k : D)) he)

/-- Injective ambient coordinates make the action on the same carrier faithful. -/
theorem action_injective_of_ambientHom_injective (hf : Function.Injective c.ambientHom) :
    Function.Injective ρ := by
  intro d e h
  exact hf (c.ambientHom_eq_of_action_eq h)

/-- The solvable quotient and small Fitting subgroup kill the coordinate kernel.
Neither the given action nor its coordinate homomorphism is assumed injective. -/
theorem ambientHom_injective_of_small_fitting [Finite D] [Group.IsSolvable (D ⧸ K)]
    (X : Subgroup D) (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hfit : fittingSubgroup D ≤ X) : Function.Injective c.ambientHom := by
  let N := c.ambientHom.ker
  have hNK (d : D) (hn : d ∈ N) (hk : d ∈ K) : d = 1 := by
    change c.ambientHom d = 1 at hn
    have he : (⟨d, hk⟩ : K) = 1 :=
      c.ambientHom_component_injective (by simpa only [map_one, MonoidHom.comp_apply,
        Subgroup.subtype_apply] using hn)
    exact congrArg Subtype.val he
  have hNX (d : D) (hn : d ∈ N) (hx : d ∈ X) : d = 1 := by
    obtain ⟨g, _, rfl⟩ := hmark.symm ▸ hx
    have hg : g = 1 := by
      have hh := congrArg Prod.snd (show c.ambientHom (s g) = 1 from hn)
      simpa only [c.ambientHom_symmetricThree, Prod.snd_one] using hh
    simp only [hg, map_one]
  let q := (QuotientGroup.mk' K).comp N.subtype
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_one q).mpr
    intro n hn
    apply Subtype.ext
    exact hNK n n.property ((QuotientGroup.eq_one_iff n.val).mp hn)
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective hq
  have hFN : fittingSubgroupOf N ≤ fittingSubgroup D :=
    le_sSup ⟨fittingSubgroupOf_normal N inferInstance, fittingSubgroupOf_isNilpotent N⟩
  have hF : fittingSubgroup N = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro n hn
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact hNX n n.property (hfit (hFN ⟨n, hn, rfl⟩))
  apply c.ambientHom.ker_eq_bot_iff.mp
  exact Subgroup.card_eq_one.mp
    ((fitting_eq_bot_iff_card_eq_one_of_solvable N).mp hF)

include c in
/-- Faithfulness on the coordinate module follows from the earlier structural data. -/
theorem action_injective_of_small_fitting [Finite D] [Group.IsSolvable (D ⧸ K)]
    (X : Subgroup D) (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hfit : fittingSubgroup D ≤ X) : Function.Injective ρ :=
  c.action_injective_of_ambientHom_injective
    (c.ambientHom_injective_of_small_fitting X hmark hfit)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.FactorCoordinates

end
