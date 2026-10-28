module
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage.TripleLocal
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.KernelNormalizer
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.Quasithin.EvenCharacteristic

/-!
# Exhaustive coverage of Sylow-containing maximal two-locals in M23

A maximal two-local containing a Sylow subgroup is the normalizer of a
nontrivial elementary subgroup normal in that Sylow subgroup. The certified
Sylow calculation treats all possible orders: its fixed points are exactly
a heptad or a triple, so the normalizer lies in the corresponding stabilizer.
Both stabilizers are actual two-locals. Maximality among two-locals therefore
gives equality. Conjugacy of heptads, triples and Sylow subgroups supplies the
multiplicative equivalences with the two published concrete candidates.

Source: the native M23 local inspection in Aschbacher--Smith 15.3.41--42,
printed p.1138, and GLS3 Table 5.3d, printed p.265. The proof requires no
ordinary subgroup maximality or classification of all maximal subgroups.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals

private theorem heptad_isTwoLocal : IsTwoLocal heptadStabilizer := by
  refine ⟨heptadKernelAmbient, ?_, heptadKernel_isTwoGroup.map heptadStabilizer.subtype,
    heptadKernelAmbient_normalizer.symm⟩
  intro h
  have hc : Nat.card heptadKernelAmbient = 16 := by
    rw [heptadKernelAmbient, Subgroup.card_map_of_injective heptadStabilizer.subtype_injective,
      heptadKernel_card]
  rw [h, Subgroup.card_bot] at hc
  contradiction

private theorem fixed_sylow_maximal_twoLocal_coverage (N : Subgroup M23)
    (hN : IsMaximalTwoLocal N) (hSN : FusionCertificate.subgroup ≤ N) :
    ∃ i : Fin 2, Nonempty (N ≃* candidate i) := by
  obtain ⟨R,hR,_hn,he,hNR⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le
      FusionCertificate.sylow hN hSN
  let A := R.map (FusionCertificate.sylow : Subgroup M23).subtype
  have hAS : A ≤ FusionCertificate.subgroup := Subgroup.map_subtype_le R
  have hAN : FusionCertificate.subgroup ≤ normalizer (A : Set M23) := hNR ▸ hSN
  have hA : A ≠ ⊥ := fun h => hR ((Subgroup.map_eq_bot_iff_of_injective R
    (FusionCertificate.sylow : Subgroup M23).subtype_injective).mp h)
  let _ := he
  have hEA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  rcases Coverage.normal_elementary_normalizer_coverage A hAS hAN hA hEA with hh | ht
  · obtain ⟨g,hg⟩ := exists_smul_omega_eq FourNormalizers.fixedSet_mem
    have hc : MulAction.stabilizer M23 FourNormalizers.fixedSet =
        (candidate 0).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      rfl
    have hl : IsTwoLocal (MulAction.stabilizer M23 FourNormalizers.fixedSet) := by
      rw [hc]
      exact Theory.Quasithin.isTwoLocal_map (MulAut.conj g) heptad_isTwoLocal
    have heq := hN.eq_of_le hl (hNR.symm ▸ hh)
    exact ⟨0, ⟨(MulEquiv.subgroupCongr (heq.trans hc)).trans
      ((MulAut.conj g).subgroupMap (candidate 0)).symm⟩⟩
  · have hl := Coverage.triple_stabilizer_isTwoLocal Coverage.fixedTriple (by decide +kernel)
    have heq := hN.eq_of_le hl (hNR.symm ▸ ht)
    obtain ⟨g,hg⟩ := Coverage.triple_stabilizer_conjugate Coverage.fixedTriple (by decide +kernel)
    exact ⟨1, ⟨(MulEquiv.subgroupCongr (heq.trans hg)).trans
      ((MulAut.conj g).subgroupMap (candidate 1)).symm⟩⟩

/-- The Sylow-containing maximal two-locals of native M23 are isomorphic to
its concrete heptad or triple stabilizer. Maximality is among two-locals. -/
theorem sylow_maximal_twoLocal_coverage (T : Sylow 2 M23) (N : Subgroup M23)
    (hN : IsMaximalTwoLocal N) (hTN : (T : Subgroup M23) ≤ N) :
    ∃ i : Fin 2, Nonempty (N ≃* candidate i) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23 T FusionCertificate.sylow
  let e := MulAut.conj g
  have hTS : (T : Subgroup M23).map e.toMonoidHom = FusionCertificate.subgroup :=
    congrArg Sylow.toSubgroup hg
  have hSN : FusionCertificate.subgroup ≤ N.map e.toMonoidHom :=
    hTS ▸ Subgroup.map_mono hTN
  obtain ⟨i,⟨hi⟩⟩ := fixed_sylow_maximal_twoLocal_coverage (N.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hN) hSN
  exact ⟨i,⟨(e.subgroupMap N).trans hi⟩⟩

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals
