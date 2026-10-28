module

public import CFSG.Quasithin.MainConverse.Transport
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.SpecificGroups.GL2.ThreeCharacteristicTwo
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.Mathieu.M11.Properties.InvolutionClasses

/-!
# Even characteristic of the concrete Mathieu group M11

Fix the semidihedral Sylow subgroup of order sixteen constructed through
C_M11(z) ≃ GL₂(3). Every maximal two-local containing it is the normalizer
of a nontrivial normal elementary subgroup of that Sylow subgroup. The
semidihedral calculation makes this subgroup the central involution line,
whose normalizer is its involution centralizer. All involutions of M11
are conjugate, and GL₂(3) has self-centralizing two-core. Thus every local
required by condition E has self-centralizing two-core. Sylow conjugacy
then gives the condition for every choice of Sylow subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(5), printed pp.3–4, repeated on pp.481–482. This proves E
only; the quasithin and proper-section conditions are separate assertions.
-/

namespace CFSG.Quasithin.MainConverse
open Subgroup Sporadic.Mathieu

private theorem involutionCentralizer_characteristicTwo
    (z : M11) (hz : orderOf z = 2) :
    HasCharacteristicTwo (centralizer ({z} : Set M11)) := by
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

/-- M11 satisfies condition E: every maximal two-local containing a Sylow
has self-centralizing two-core. -/
public theorem m11_evenCharacteristic : IsEvenCharacteristic M11 := by
  obtain ⟨T, a, b, ha, hb, hc, hg⟩ := m11_exists_semidihedral_sylow
  apply IsEvenCharacteristicAt.all (T := T)
  intro M hM hTM
  obtain ⟨R, hR, hn, he, hMR⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  let : R.Normal := hn
  let : IsElementaryAbelian 2 R := he
  rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg R hR,
    MonoidHom.map_zpowers] at hMR
  have hz : orderOf (((a ^ 4 : T) : M11)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_pow, ha]
    norm_num
  change M = normalizer (zpowers (((a ^ 4 : T) : M11)) : Set M11) at hMR
  rw [normalizer_zpowers_eq_centralizer_of_order_two _ hz] at hMR
  rw [hMR]
  exact involutionCentralizer_characteristicTwo _ hz
end CFSG.Quasithin.MainConverse
