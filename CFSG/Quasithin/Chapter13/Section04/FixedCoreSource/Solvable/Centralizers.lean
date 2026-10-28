module

public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.FusionControlledNormalizer

/-!
# The full-centralizer argument in the solvable branch of 13.4.9

Suppose E contains an ambient Sylow subgroup T, contains C_G(d), and
controls fusion of d, where d centralizes T. For a Sylow-central involution
j, condition (E) gives characteristic two in C_G(j). Its two-core lies in T,
and d centralizes that core, so d belongs to it. Fusion now puts the whole
normalizer of this two-core in E, hence C_G(j)≤E.

An E-conjugate of j may be used to arrange Sylow centrality. Thus the
symplectic calculation that a product of distinct commuting transvections
is two-central supplies the full ambient centralizer bound; that bound is
not assumed. Source: Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
variable {G : Type*} [Group G] [Finite G]

/-- The source characteristic-two and unique-fixed-point argument. -/
theorem centralizer_le_of_sylow_central (E : Subgroup G) (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) (hTE : (T : Subgroup G) ≤ E) (d : G)
    (hdT : d ∈ T) (hdC : d ∈ centralizer (T : Set G))
    (hf : ∀ b ∈ E, IsConj d b → ∃ c ∈ E, MulAut.conj c d = b)
    (hc : centralizer ({d} : Set G) ≤ E)
    {j : G} (hj : orderOf j = 2) (hTj : (T : Subgroup G) ≤ centralizer ({j} : Set G)) :
    centralizer ({j} : Set G) ≤ E := by
  have hchar := Chapter1.mem_He_iff.mp
    (Chapter1.twoLocal_mem_He_of_sylow_le T hE
      (Theory.GroupTheory.isTwoLocal_involution_centralizer hj) hTj)
  apply le_of_characteristic_p_of_element_fusion E (centralizer ({j} : Set G))
    (T.subtype hTj) d hf hc hchar
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTj] using hTE
  · exact hTj hdT
  · rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTj]
    exact hdC

/-- Transport the actual ambient centralizer, using a conjugator inside E. -/
theorem centralizer_le_of_conjugate_sylow_central (E : Subgroup G) (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) (hTE : (T : Subgroup G) ≤ E) (d : G)
    (hdT : d ∈ T) (hdC : d ∈ centralizer (T : Set G))
    (hf : ∀ b ∈ E, IsConj d b → ∃ c ∈ E, MulAut.conj c d = b)
    (hc : centralizer ({d} : Set G) ≤ E)
    {j : G} (hj : orderOf j = 2)
    (hlocal : ∃ c ∈ E, (T : Subgroup G) ≤ centralizer ({MulAut.conj c j} : Set G)) :
    centralizer ({j} : Set G) ≤ E := by
  obtain ⟨c, hcE, hTj⟩ := hlocal
  have horder : orderOf (MulAut.conj c j) = 2 := by
    rw [MulEquiv.orderOf_eq, hj]
  have hcent := centralizer_le_of_sylow_central E T hE hTE d hdT hdC hf hc horder hTj
  intro a ha
  have hca : MulAut.conj c a ∈ E := by
    apply hcent
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using
      congrArg (MulAut.conj c) (mem_centralizer_singleton_iff.mp ha)
  have hh := E.mul_mem (E.mul_mem (E.inv_mem hcE) hca) hcE
  simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
    mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
