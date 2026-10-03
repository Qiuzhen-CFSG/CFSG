module

public import Theory.GroupTheory.SylowCentralizerConjugacy
public import Mathlib.Algebra.Group.Conj

/-!
# Transporting fixed subgroups through an injective homomorphism

Suppose an injective homomorphism has image containing a normal subgroup.
Conjugate elements in the codomain have isomorphic fixed subgroups in the
preimage of that normal subgroup. First identify each fixed subgroup with
the corresponding centralizer intersection in the codomain, then restrict
conjugation to the normal subgroup.

This is the fixed-core transport used in Janko–Thompson, Math. Z. 113
(1970), §4, case (c), printed p.392, on choosing a fully centralized
representative in the central-involution normalizer.
-/

namespace Subgroup

/-- An injective map onto a subgroup containing `H` identifies the fixed
subgroup in its preimage with the fixed subgroup in `H`. -/
public theorem map_comap_inf_centralizer_singleton
    {P Q : Type*} [Group P] [Group Q]
    (f : P →* Q) (hf : Function.Injective f)
    (H : Subgroup Q) (hH : H ≤ f.range) (x : P) :
    (H.comap f ⊓ centralizer ({x} : Set P)).map f =
      H ⊓ centralizer ({f x} : Set Q) := by
  ext y
  constructor
  · rintro ⟨u, ⟨huH, huc⟩, rfl⟩
    refine ⟨huH, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp huc)
  · rintro ⟨hyH, hyc⟩
    obtain ⟨u, rfl⟩ := hH hyH
    refine ⟨u, ⟨hyH, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    apply hf
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hyc

/-- Conjugacy in the codomain preserves the isomorphism type of the fixed
subgroup in the preimage of a normal subgroup contained in the image. -/
public theorem nonempty_fixed_equiv_of_isConj_map
    {P Q : Type*} [Group P] [Group Q]
    (f : P →* Q) (hf : Function.Injective f)
    (H : Subgroup Q) [H.Normal] (hH : H ≤ f.range)
    (x y : P) (hxy : IsConj (f x) (f y)) :
    Nonempty ((H.comap f ⊓ centralizer ({x} : Set P) : Subgroup P) ≃*
      (H.comap f ⊓ centralizer ({y} : Set P) : Subgroup P)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let a := MulAut.conj g
  have ha : a (f x) = f y := hg
  have hm : (H ⊓ centralizer ({f x} : Set Q)).map a.toMonoidHom =
      H ⊓ centralizer ({f y} : Set Q) := by
    ext v
    constructor
    · rintro ⟨u, ⟨huH, huc⟩, rfl⟩
      refine ⟨(inferInstance : H.Normal).conj_mem u huH g,
        mem_centralizer_singleton_iff.mpr ?_⟩
      change a u * f y = f y * a u
      simpa only [map_mul, ha] using congrArg a (mem_centralizer_singleton_iff.mp huc)
    · rintro ⟨hvH, hvc⟩
      refine ⟨a.symm v, ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩,
        a.apply_symm_apply v⟩
      · simpa [a, MulAut.conj_apply] using
          (inferInstance : H.Normal).conj_mem v hvH g⁻¹
      · apply a.injective
        simpa only [map_mul, a.apply_symm_apply, ha] using
          mem_centralizer_singleton_iff.mp hvc
  let e (u : P) := ((H.comap f ⊓ centralizer ({u} : Set P)).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr (map_comap_inf_centralizer_singleton f hf H hH u))
  exact ⟨(e x).trans ((a.subgroupMap _).trans
    ((MulEquiv.subgroupCongr hm).trans (e y).symm))⟩

end Subgroup
