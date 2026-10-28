module

public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.Triality.Model.QTKE
/-!
# Inner normalization of triality automorphisms

Conjugacy of Sylow two-subgroups makes an arbitrary automorphism preserve the
actual positive subgroup after multiplication by an inner automorphism. Its
normalizer is the actual Borel, so the same adjustment preserves the Borel.
This establishes the first normalization in Steinberg's automorphism proof,
without assuming simplicity, perfectness, or automorphism coverage.

Source: Steinberg, Theorem 30, step (1), and Theorem 36
(`refs/KGroup/GLS3/Chapter2St1.tex`); GLS3 2.5.1
(`refs/KGroup/GLS3/chapter2.tex`). The remaining opposite-root alignment is
not asserted here.
-/

public section
noncomputable section
namespace Triality.Standard.OuterOdd.Coverage
open Parabolics ConcreteBruhat
open scoped Pointwise

theorem exists_inner_unipotent_invariant (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) :
    ∃ g : Carrier P,
      (unipotent P).map (MulAut.conj g * a).toMonoidHom = unipotent P := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier P)
    (a • unipotentSylow P hp) (unipotentSylow P hp)
  refine ⟨g, ?_⟩
  have hs := congrArg (fun S : Sylow 2 (Carrier P) => (S : Subgroup (Carrier P))) hg
  change ((unipotent P).map a.toMonoidHom).map (MulAut.conj g).toMonoidHom =
    unipotent P at hs
  rw [Subgroup.map_map] at hs
  exact hs

theorem map_borel_eq_of_unipotent_invariant (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P))
    (h : (unipotent P).map a.toMonoidHom = unipotent P) :
    (borel P).map a.toMonoidHom = borel P := by
  rw [← normalizer_unipotent_eq_borel P hp,
    Subgroup.map_equiv_normalizer_eq, h]

theorem exists_inner_unipotent_borel_invariant (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) :
    ∃ g : Carrier P,
      (unipotent P).map (MulAut.conj g * a).toMonoidHom = unipotent P ∧
      (borel P).map (MulAut.conj g * a).toMonoidHom = borel P := by
  obtain ⟨g, hg⟩ := exists_inner_unipotent_invariant P hp a
  exact ⟨g, hg, map_borel_eq_of_unipotent_invariant P hp _ hg⟩
end Triality.Standard.OuterOdd.Coverage
