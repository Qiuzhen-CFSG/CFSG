module

public import Theory.GroupTheory.LocalCoreFromPrimeCentralizers
public import Theory.Mathieu.M11.Properties.Centralizer
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.SpecificGroups.GL2.ThreeCharacteristicTwo

/-!
# Characteristic two in every nontrivial two-local normalizer of M11

The unique involution class transports the concrete GL2(3) centralizer to
every involution. All these centralizers have characteristic two, so the
prime-centralizer criterion applies to every nontrivial two-subgroup.
This is the M11 local assertion in Aschbacher--Smith 2.5.3(4), printed p.553.
-/

namespace Sporadic.Mathieu
open Subgroup

/-- Each involution centralizer in M11 has self-centralizing two-core. -/
public theorem m11_involutionCentralizer_twoCore_selfCentralizing
    (z : M11) (hz : orderOf z = 2) :
    centralizer (pCore 2 (centralizer ({z} : Set M11)) :
      Set (centralizer ({z} : Set M11))) ≤ pCore 2 (centralizer ({z} : Set M11)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA z hz)
  let f := MulAut.conj g
  have hf : f z = m11GeneratorAInM11 := hg
  have hmap : (centralizer ({z} : Set M11)).map f.toMonoidHom =
      m11InvolutionCentralizer := by
    apply le_antisymm
    · simpa [hf, m11InvolutionCentralizer] using
        map_centralizer_le_centralizer_image ({z} : Set M11) f.toMonoidHom
    · intro x hx
      refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
      rw [m11InvolutionCentralizer, mem_centralizer_singleton_iff] at hx
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul, hf, f.apply_symm_apply] using hx
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    ((f.subgroupMap (centralizer ({z} : Set M11))).trans
      (MulEquiv.subgroupCongr hmap))).mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2
      m11InvolutionCentralizer_mulEquiv_gl2).mpr
      Matrix.GeneralLinearGroup.three_centralizer_twoCore_le)

/-- Every nontrivial two-subgroup has a characteristic-two normalizer. -/
public theorem m11_normalizer_twoCore_selfCentralizing
    (R : Subgroup M11) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    centralizer (pCore 2 (normalizer (R : Set M11)) : Set (normalizer (R : Set M11))) ≤
      pCore 2 (normalizer (R : Set M11)) :=
  normalizer_core_selfCentralizing_of_prime_centralizers
    m11_involutionCentralizer_twoCore_selfCentralizing R hp hne

end Sporadic.Mathieu
