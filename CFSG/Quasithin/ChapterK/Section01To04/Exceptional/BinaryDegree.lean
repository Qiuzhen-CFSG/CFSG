module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2LowDegree
public import Theory.Representation.NonsplitFour

/-!
# The degree sieve at G₂(2)′

The verified unipotent-coset filtration of the actual binary derived group
has only degrees one, six and greater than eight. Faithfulness excludes
degree one by the order 6048 of that group. Thus an irreducible action of
degree at most eight has degree six, and the concrete factor intertwiners
identify it with the octonion-quotient natural action.

This supplies the r=1 representation endpoint of K.3.5 once its cubic
degree bound is proved. Source: Aschbacher--Smith, printed p.457; the
permutation filtration and its maps are the same certified ones used in
G.7.2(3) and G.9.3(10).
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional
open Representation G2DerivedPermutationFiltration
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
attribute [local instance] BinarySix.scalars

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The source binary derived carrier has no other faithful irreducible
degree at most eight. -/
theorem g2_binary_degree_six
    (ρ : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) V)
    [IsIrreducible ρ] (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 8) : Module.finrank (ZMod 2) V = 6 := by
  have h := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    flagPerm baseFlag flagStabilizer flagStabilizer_isPGroup
    mem_flagStabilizer_iff flagTransitive flag_factorDegreeFiltration ρ
  change Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 6 ∨
    8 < Module.finrank (ZMod 2) V at h
  have hcard : Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
    rw [show commutator (Atlas.G2.Model (ZMod 2)) = Atlas.G2.BinaryException.H from
      Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.card_H
  have hne : Module.finrank (ZMod 2) V ≠ 1 := by
    intro h1
    have hdiv := card_dvd_card_GL_of_injective ρ hf
    rw [hcard, h1, Matrix.card_GL_field] at hdiv
    norm_num [Fin.prod_univ_succ] at hdiv
  omega

/-- Actual component application of the binary degree sieve, with the
derived-group marking and the natural-module intertwiner retained. -/
theorem g2_binary_marked_natural_of_degree_le_eight
    {G : Type*} [Group G] (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [IsIrreducible (ρ.comp L.subtype)]
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 8) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary (ZMod 2) (e' g) (f v) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp L.subtype)).mpr inferInstance
  exact g2_binary_marked_natural_of_degree_six ρ L e
    (g2_binary_degree_six σ (hf.comp (L.subtype_injective.comp e.symm.injective)) hd)

end CFSG.Quasithin.ChapterK.Exceptional
