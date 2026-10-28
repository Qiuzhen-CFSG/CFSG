module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.ResidualSpan
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Frattini

/-!
# Trivial core action on the original line section

The relative quotient is formed inside `G_E = N_G(E)`. Normality of its
intrinsic two-core makes the inverse image of the quotient centralizer
normal in `G_E`. The relation `[V,S_E] ≤ E` puts `V` in this inverse image;
its invariance then puts the entire `C_E`-span there. Thus `[U,Q_E] ≤ E`.
This proves the first module step before the temporary replacement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
variable {G : Type*} [Group G]

/-- The original two-core acts trivially on the relative section `U/E`. -/
theorem core_commutator_le_line (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (hspan : lineV V E = conjugateSpanBy V (lineC E))
    (hQS : lineQ E ≤ T ⊓ centralizer (E : Set G))
    (hVS : ⁅V, T ⊓ centralizer (E : Set G)⁆ ≤ E) :
    ⁅lineV V E, lineQ E⁆ ≤ E := by
  let N := lineNormalizer E
  let L := E.subgroupOf N
  let Q := pCore 2 N
  let q := QuotientGroup.mk' L
  let K := centralizerModulo ⊤ Q L
  have hVN : V ≤ N := (le_conjugateSpanBy V N).trans (lineV_le_lineNormalizer V E hEV)
  let : (Q.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective L)
  let : K.Normal := by dsimp only [K, centralizerModulo]; infer_instance
  have hK : N ≤ normalizer (K.map N.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    change ((K.map N.subtype).comap N.subtype).Normal
    rw [comap_map_eq_self_of_injective N.subtype_injective]
    infer_instance
  have hVK : V ≤ K.map N.subtype := by
    intro v hv
    refine ⟨⟨v, hVN hv⟩, mem_centralizerModulo_iff.mpr ⟨mem_top _, ?_⟩, rfl⟩
    intro a ha
    change ⁅(a : G), v⁆ ∈ E
    have haQ : (a : G) ∈ lineQ E := mem_map_of_mem N.subtype ha
    have hh : ⁅lineQ E, V⁆ ≤ E := by
      rw [commutator_comm]
      exact (commutator_mono le_rfl hQS).trans hVS
    exact hh (commutator_mem_commutator haQ hv)
  have hUK : lineV V E ≤ K.map N.subtype := by
    rw [hspan]
    exact conjugateSpanBy_le hVK ((centralizer_le_normalizer (E : Set G)).trans hK)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha u hu
  obtain ⟨aN, haN, rfl⟩ := ha
  obtain ⟨uN, huN, rfl⟩ := hUK hu
  exact (mem_centralizerModulo_iff.mp huN).2 aN haN

/-- The centralization is in `G_E/E`, without assuming ambient normality of `E`. -/
theorem core_le_sectionKernel (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (hspan : lineV V E = conjugateSpanBy V (lineC E))
    (hQS : lineQ E ≤ T ⊓ centralizer (E : Set G))
    (hVS : ⁅V, T ⊓ centralizer (E : Set G)⁆ ≤ E) :
    lineQ E ≤ Descent.sectionKernel V E := by
  intro a ha
  apply (Descent.mem_sectionKernel_iff V E (lineV_le_lineNormalizer V E hEV) a).mpr
  exact ⟨map_subtype_le _ ha, fun u hu =>
    core_commutator_le_line T V E hEV hspan hQS hVS (commutator_mem_commutator hu ha)⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
