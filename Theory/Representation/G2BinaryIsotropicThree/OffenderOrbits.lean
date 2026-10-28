module

public import Theory.Representation.G2BinaryIsotropicThree.OffenderSpaces
public import Theory.Representation.G2BinaryNaturalOffenders


/-!
# Offender fixed three-spaces form a derived-group orbit

The full natural offender classification gives an ABC conjugator. The odd
coset can be removed by C(1), which fixes the standard three-space pointwise.
Thus the same fixed-space orbit is already realized by actual G₂(2)′ elements,
as needed for lifting the conjugator through the original local subgroup.

Source: Aschbacher–Smith 13.3.12(4), printed p.890.
-/

public section

open Subgroup Module Submodule Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates

theorem offender_fixed_space_derived_orbit (A : Subgroup (Model K))
    (hA : IsOffender rho A) :
    ∃d : commutator (Model K),fixedSpace rho A=(target false).map (rho d.val) := by
  obtain ⟨g,rfl⟩ := NaturalOffenders.offender_conjugate_elementary
    (F:=K) (n:=1) (by norm_num) (by decide) A hA
  have hfixed : fixedSpace rho ((EvenTwoRank.elementary K).map (MulAut.conj g).toMonoidHom)=
      (target false).map (rho g) := by
    rw [←fixed_elementary_eq_target]
    let E := LinearEquiv.ofBijective (rho g) (rho.apply_bijective g)
    symm
    apply fixedSpace_map_equivariant rho rho (MulAut.conj g).toMonoidHom E
    intro a v
    change rho g (rho a v)=rho (g*a*g⁻¹) (rho g v)
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  rw [hfixed]
  by_cases hd : g∈commutator (Model K)
  · exact ⟨⟨g,hd⟩,rfl⟩
  · have hi : (commutator (Model K)).index=2 := by
      rw [BinaryParabolicPair.commutator_eq_longRootClosure,BinaryException.index_H]
    have hC : rootC (1:K)∉commutator (Model K) := BinaryNormalizer.rootC_not_mem_derived
    have hgd : g*rootC (1:K)∈commutator (Model K) :=
      ((commutator (Model K)).mul_mem_iff_of_index_two hi).mpr (iff_of_false hd hC)
    refine ⟨⟨g*rootC 1,hgd⟩,?_⟩
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      refine ⟨v,hv,?_⟩
      simp only [map_mul,Module.End.mul_apply]
      rw [NaturalOffenders.rootC_fix_upper 1 hv]
    · rintro _ ⟨v,hv,rfl⟩
      refine ⟨v,hv,?_⟩
      simp only [map_mul,Module.End.mul_apply]
      rw [NaturalOffenders.rootC_fix_upper 1 hv]
end Atlas.G2.Natural.BinaryIsotropicThree
