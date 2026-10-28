module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The genuine local span in the degree-eight branch

The central involutions lie in the common Sylow subgroup. Its two-core
centralizes all their `I`-conjugates. Self-centralization of the generalized
Fitting subgroup then puts the actual span `U_I = ⟨Zᴵ⟩` in that two-core.
Consequently the span is abelian, and its involution generators make it
elementary abelian. The component commutator inherits this property.

Relative normality of `L` gives invariance of `U_L`. Factoring conjugators
through `I = LS`, with `S` centralizing `Z`, also proves `U_I = Z U_L`.
These steps precede any module recognition; no coordinates for `U_I` or
`U_L`, fixed-plane equality, or central-summand decomposition are assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.14 and
the proof of 15.3.32, printed pp.78 and 1132–1133.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- The actual conjugate span stays inside its local overgroup. -/
theorem span_le (d : LocalData G) {I : Subgroup G} (hSI : d.S ≤ I) : d.UI I ≤ I := by
  apply conjugateSpanBy_le_self
  exact ((le_conjugateSpanBy d.Z d.M).trans
    (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1)).trans hSI

omit [Finite G] in
/-- Centrality on the Sylow seed propagates to its local conjugate span. -/
theorem span_centralizes_core (d : LocalData G) {I : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    d.UI I ≤ centralizer (I.pCoreIn 2 : Set G) := by
  apply le_centralizer_iff.mp
  have h := core_le_star_kernel d P hP
  rw [show (d.starMap I).ker = localActionKernel d.Z I from QuotientGroup.ker_mk' _,
    localActionKernel, subgroupOf_map_subtype] at h
  exact h.trans inf_le_left

/-- Characteristic two places the genuine span in the local two-core. -/
theorem span_le_core (d : LocalData G) {I : Subgroup G}
    (hchar : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    d.UI I ≤ I.pCoreIn 2 := by
  have hself : centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
    rw [← hchar]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hUI := span_le d (show d.S ≤ I from hP ▸ map_subtype_le _)
  intro u hu
  have huc := span_centralizes_core d P hP hu
  have hup : (⟨u, hUI hu⟩ : I) ∈ pCore 2 I := hself (by
    intro q hq
    exact Subtype.ext (huc q (mem_map_of_mem I.subtype hq)))
  exact mem_map_of_mem I.subtype hup

/-- The actual span is elementary abelian, before recognition of its action. -/
theorem span_elementary (d : LocalData G) {I : Subgroup G}
    (hchar : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    IsElementaryAbelian 2 (d.UI I) := by
  have hcc : d.UI I ≤ centralizer (d.UI I : Set G) :=
    (span_centralizes_core d P hP).trans (centralizer_le (span_le_core d hchar P hP))
  let _ : IsMulCommutative (d.UI I) := le_centralizer_iff_isMulCommutative.mp hcc
  let _ : IsElementaryAbelian 2 d.Z := d.action.elementary_of_le (le_conjugateSpanBy d.Z d.M)
  let _ : IsMulCommutative (Subgroup.closure {x | ∃ i ∈ I, ∃ z ∈ d.Z, i * z * i⁻¹ = x}) :=
    inferInstanceAs (IsMulCommutative (d.UI I))
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨i, hi, z, hz, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian z hz, mul_one, mul_inv_cancel]

/-- The actual component commutator is a binary internal module. -/
theorem componentModule_elementary (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hchar : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    IsElementaryAbelian 2 (d.componentModule I c.L) := by
  let _ := span_elementary d hchar P hP
  exact IsElementaryAbelian.of_le (componentModule_le_span d c)

omit [Finite G] in
/-- Relative normality of the component makes its commutator `I`-invariant. -/
theorem componentModule_normalizes (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal) :
    I ≤ normalizer (d.componentModule I c.L : Set G) := by
  have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal
  intro i hi
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅d.UI I, c.L⁆).map (MulAut.conj i).toMonoidHom = ⁅d.UI I, c.L⁆
  rw [map_commutator]
  exact congrArg₂ (fun A B : Subgroup G => ⁅A, B⁆)
    (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy d.Z I hi))
    (mem_normalizer_iff_map_conj_eq.mp (hIL hi))


omit [Finite G] in
/-- The Sylow-central seed supplements the component commutator in `U_I`. -/
theorem span_eq_seed_sup_componentModule (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (hI : I = c.L ⊔ d.S) :
    d.UI I = d.Z ⊔ d.componentModule I c.L := by
  let _ := hnormal
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hLS : c.L.subgroupOf I ⊔ d.S.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (component_le c),
      map_subgroupOf_eq_of_le hSI, ← MonoidHom.range_eq_map, range_subtype]
    exact hI.symm
  apply le_antisymm ?_ (sup_le (le_conjugateSpanBy d.Z I) (componentModule_le_span d c))
  apply (closure_le _).mpr
  rintro x ⟨i, hi, z, hz, rfl⟩
  obtain ⟨l, hl, s, hs, hls⟩ := mem_sup_of_normal_left.mp
    (show (⟨i, hi⟩ : I) ∈ c.L.subgroupOf I ⊔ d.S.subgroupOf I from hLS ▸ mem_top _)
  have his : (l : G) * (s : G) = i := congrArg Subtype.val hls
  have hsz : (s : G) * z = z * (s : G) :=
    centralInvolutions_le_centralizer_sylow d.T hz s (show (s : G) ∈ (d.T : Subgroup G) from hs.1)
  have hc : ⁅(l : G), z⁆ ∈ d.componentModule I c.L := by
    rw [LocalData.componentModule, commutator_comm]
    exact commutator_mem_commutator hl (le_conjugateSpanBy d.Z I hz)
  have hprod := (d.Z ⊔ d.componentModule I c.L).mul_mem (mem_sup_right hc) (mem_sup_left hz)
  have heq : i * z * i⁻¹ = ⁅(l : G), z⁆ * z := by
    rw [← his]
    simp only [mul_inv_rev, commutatorElement_def]
    calc
      (l : G) * (s : G) * z * ((s : G)⁻¹ * (l : G)⁻¹) =
          (l : G) * ((s : G) * z) * ((s : G)⁻¹ * (l : G)⁻¹) := by group
      _ = (l : G) * (z * (s : G)) * ((s : G)⁻¹ * (l : G)⁻¹) := by rw [hsz]
      _ = _ := by group
  exact heq ▸ hprod

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule

end
