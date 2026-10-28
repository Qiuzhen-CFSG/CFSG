module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.LinePlacement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic.PointActor

/-!
# Point-parabolic bounds for the actual critical pair

The marked parabolic identifies the star image of Uγ with the long-root
four-group. Its displacement lifts through the actual natural projection.
Mutual normalization places [Uγ,U_H] in both subgroups; U_H≤O₂(H) and the
faithful central-section action then put it in the literal Dγ∩U_H. This
supplies the first and bottom contributions to the source filtration.

The required marking is for this same star image and natural projection.
The core-comparison and faithful V_H/U_H arguments are separate inputs.
Source: Aschbacher–Smith, 13.8.27, final paragraph, printed p.963.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry
open Atlas.G2

variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) W}

/-- The point-parabolic calculation supplies both numerical bounds on the
same critical actor and the literal bottom intersection. -/
theorem source_actor_and_bottom_bounds
    (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hfaith : Function.Injective ρ)
    (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hUQ : Source.UH H V₃ ≤ Source.QH H)
    (f : Source.Hstar H →* Model (ZMod 2)) (hf : Function.Injective f)
    (p : W →ₗ[ZMod 2] Natural.Space (ZMod 2)) (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v))
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hr : rank (Source.starImage H (c.Ugamma V₃)) < 3)
    (hAu : (Source.starImage H (c.Ugamma V₃)).map f ≤ unipotent)
    (hn : BinaryParabolicPair.derivedSecondAmbient ≤
      normalizer ((Source.starImage H (c.Ugamma V₃)).map f : Set _)) :
    rank (Source.starImage H (c.Ugamma V₃)) = 2 ∧
      3 ≤ rank (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃) := by
  let A := Source.starImage H (c.Ugamma V₃)
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hne : A.map f ≠ ⊥ := by
    intro hb
    exact hA.1 (Subgroup.map_injective hf (hb.trans (map_bot f).symm))
  have hrmap : rank (A.map f) < 3 := by rwa [rank_map_injective f hf]
  have hrank := (point_actor_eq_natural (A.map f) hAu hn hne hrmap).2
  rw [rank_map_injective f hf] at hrank
  refine ⟨hrank, ?_⟩
  have hlow := displacement_ge_three_of_natural_projection ρ f p hp he A hAu hn hne
  have hnUg : Source.UH H V₃ ≤ normalizer (c.Ugamma V₃ : Set G) := by
    have hm := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) s.normalizes
    rw [map_equiv_normalizer_eq] at hm
    exact hreverse.trans hm
  have hcommU : ⁅c.Ugamma V₃, Source.UH H V₃⁆ ≤ Source.UH H V₃ :=
    le_normalizer_iff_commutator_le_right.mp (hUg.trans s.normalizes)
  have hcomm : ⁅c.Ugamma V₃, Source.UH H V₃⁆ ≤
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃ := by
    rw [s.Dgamma_eq_inf_core _ hUg hfaith]
    exact le_inf (le_inf (le_normalizer_iff_commutator_le_left.mp hnUg)
      (hcommU.trans hUQ)) hcommU
  have hdispl : subspaceCommutator ρ ⊤ A ≤
      s.image (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
    apply s.displacement_mem _ _ _ hcomm a ha v
    exact ⟨u, u.property, congrArg Multiplicative.toAdd hu⟩
  exact hlow.trans ((Submodule.finrank_mono hdispl).trans (s.image_finrank_le _))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
