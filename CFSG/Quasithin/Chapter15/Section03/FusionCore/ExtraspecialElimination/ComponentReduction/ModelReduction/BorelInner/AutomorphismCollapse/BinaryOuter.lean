module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.BinaryModels
public import Theory.SpecificGroups.PSL3Two.OuterThreeFree
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# Outer orders for every binary component

The actual SL₃ outer quotient has order two. Full-group conjugation on
G₂(2)′ is surjective, so its outer quotient is a quotient of the order-two
abelianization of G₂(2). Entrywise field transport, restricted to the
commutator subgroup, retains this conclusion for every two-element field.
Together with the binary linear and symplectic calculations, these facts
give outer order prime to three for every binary `LieComponentModel`.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, B.4.2 and B.5.6,
printed pp.86, 105, and the inner-action step of 15.3.49(k), p.1144.
The imported G₂ model and field transport retain the ATLAS attribution
in `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.BinaryModels

/-- The outer order of the actual binary derived G₂ model is prime to three,
independently of the chosen two-element field. -/
theorem binary_g2_outer_three_free {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    ¬ 3 ∣ Nat.card (MulAut.Outer (commutator (Atlas.G2.Model F))) := by
  let _ := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let f := Atlas.G2.fieldEquiv e
  have hf : (commutator (Atlas.G2.Model F)).map f.toMonoidHom =
      commutator (Atlas.G2.Model (ZMod 2)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective]
    rfl
  let g := (f.subgroupMap (commutator (Atlas.G2.Model F))).trans
    (MulEquiv.subgroupCongr hf)
  rw [Nat.card_congr (MulAut.outerCongr g).toEquiv]
  exact binary_g2_outer_three_free_of_coverage
    Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective

/-- Every binary alternative has outer order prime to three through its
specified concrete model equivalence. -/
theorem binary_model_outer_three_free {D : Type*} [Group D]
    (hmodel : LieComponentModel D 1) : ¬ 3 ∣ Nat.card (MulAut.Outer D) := by
  cases hmodel with
  | linear_two he F hF m => omega
  | linear_three he F hF m =>
      obtain ⟨f⟩ := m
      rw [Nat.card_congr (MulAut.outerCongr f).toEquiv]
      exact Matrix.PSL3Two.outer_three_free_of_card_two (by simpa using hF)
  | symplectic he F hF m =>
      obtain ⟨f⟩ := m
      rw [Nat.card_congr (MulAut.outerCongr f).toEquiv]
      exact binary_symplectic_outer_three_free (by simpa using hF)
  | g2 he F hF m =>
      obtain ⟨f⟩ := m
      rw [Nat.card_congr (MulAut.outerCongr f).toEquiv]
      exact binary_g2_outer_three_free (by simpa using hF)
  | binary_linear he n hn m =>
      obtain ⟨f⟩ := m
      rw [Nat.card_congr (MulAut.outerCongr f).toEquiv]
      exact binary_linear_outer_three_free hn

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.BinaryModels
