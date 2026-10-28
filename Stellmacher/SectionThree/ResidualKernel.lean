module
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# A residual commutator criterion for containment in the 2-core

A 2-subgroup of a finite group lies in its 2-core whenever its commutator
with the 2-residual lies in that core. This supplies the kernel implication
used at the end of Stellmacher (7.7), Journal of Algebra 190 (1997), p. 36.
No solvability or Sylow-normality assumption on the given subgroup is needed.

Inside the containing group, choose a Sylow 2-subgroup containing the given
subgroup. It also contains the 2-core and supplements the 2-residual. Every
conjugate of the given subgroup therefore remains in this Sylow subgroup:
conjugation by a residual element changes an element only by a core element.
Its normal closure is consequently a normal 2-subgroup, hence lies in the
2-core. The final step transports this inclusion to the ambient group.
-/

open scoped commutatorElement

namespace Stellmacher.SectionThree

private theorem normalClosure_le_of_residual_supplement
    {G : Type*} [Group G]
    (E S T Q : Subgroup G) [E.Normal]
    (hgen : S ⊔ E = ⊤) (hTS : T ≤ S) (hQS : Q ≤ S)
    (hcomm : ⁅E, T⁆ ≤ Q) :
    Subgroup.normalClosure (T : Set G) ≤ S := by
  apply (Subgroup.closure_le (K := S)).mpr
  intro x hx
  obtain ⟨t, ht, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  have hg : g ∈ S ⊔ E := by rw [hgen]; trivial
  obtain ⟨s, hs, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have het : e * t * e⁻¹ ∈ S := by
    have hct : ⁅e, t⁆ ∈ S := hQS (hcomm (Subgroup.commutator_mem_commutator he ht))
    have heq : e * t * e⁻¹ = ⁅e, t⁆ * t := by
      simp [commutatorElement_def, mul_assoc]
    rw [heq]
    exact S.mul_mem hct (hTS ht)
  have hres := S.mul_mem (S.mul_mem hs het) (S.inv_mem hs)
  change (s * e) * t * (s * e)⁻¹ ∈ S
  simpa only [mul_inv_rev, mul_assoc] using hres

public theorem two_subgroup_le_core_of_commutator_residual_le_core
    {G : Type*} [Group G] [Finite G]
    (T P : Subgroup G) (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hcomm : ⁅T, twoResidualAmbient P⁆ ≤ twoCoreAmbient P) :
    T ≤ twoCoreAmbient P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U := T.subgroupOf P
  have hUp : IsPGroup 2 U := hT.comap_subtype
  obtain ⟨S, hUS⟩ := hUp.exists_le_sylow
  let E := twoResidualSubgroup P
  have hn : E.Normal := by
    unfold E twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal (fun N => Subgroup.normal_iInf_normal (fun hN => hN.1))
  let _ : E.Normal := hn
  have hgen : (S : Subgroup P) ⊔ E = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map]
    have hS : IsSylowSubgroupIn ((S : Subgroup P).map P.subtype) P := ⟨S, rfl⟩
    have hh := twoResidual_sup_sylowImage hS
    simpa only [E, twoResidualAmbient, sup_comm, Subgroup.range_subtype] using hh
  have hQS : pCore 2 P ≤ (S : Subgroup P) := (pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal S
  have hcomm' : ⁅E, U⁆ ≤ pCore 2 P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTP]
    simpa only [E, twoResidualAmbient, twoCoreAmbient, Subgroup.commutator_comm] using hcomm
  let N := Subgroup.normalClosure (U : Set P)
  have hNS : N ≤ (S : Subgroup P) :=
    normalClosure_le_of_residual_supplement E S U (pCore 2 P) hgen hUS hQS hcomm'
  have hNp : IsPGroup 2 N := S.isPGroup'.to_le hNS
  have hNcore : N ≤ pCore 2 P := le_sSup ⟨inferInstance, hNp⟩
  have hUcore : U ≤ pCore 2 P := Subgroup.le_normalClosure.trans hNcore
  have hm := Subgroup.map_mono (f := P.subtype) hUcore
  simpa only [U, Subgroup.map_subgroupOf_eq_of_le hTP, twoCoreAmbient] using hm

end Stellmacher.SectionThree
