module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroModuleOrder
public import CFSG.Quasithin.Chapter10.SourceA5ZeroNormalizerKernel
public import Theory.GroupTheory.DihedralFourElementaryChoices
public import Theory.SpecificGroups.DihedralProduct.AmbientCentralEnlargements

/-!
# Elementary geometry in the original zero-center four-factor marking

The original module has order 256 in the recognized Baumann subgroup. Its
intersections with the four canonical central enlargements consequently have
order 32 and generate it. These literal ambient intersections discharge the
size and spanning premises of the source normalizer-kernel argument.

Source: Aschbacher--Smith, quasithin 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher DihedralProductCanonical
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The geometric intersection and spanning assertions for the actual module. -/
theorem source_a5_zero_module_gamma_geometry
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (eR : ChapterB.baumann (T : Subgroup G) ≃* (Fin 4 → DihedralGroup 4)) :
    let R := ChapterB.baumann (T : Subgroup G)
    let F := fun i => (transportedGamma eR i).map R.subtype
    (∀ i, Nat.card (D.moduleSubgroup ⊓ F i : Subgroup G) = 32) ∧
      (⨆ i, D.moduleSubgroup ⊓ F i) = D.moduleSubgroup := by
  let R := ChapterB.baumann (T : Subgroup G)
  let V := D.moduleSubgroup.subgroupOf R
  have hVR := source_a5_zero_module_le_baumann D e hn hout hz
  have hVm : V.map R.subtype = D.moduleSubgroup := map_subgroupOf_eq_of_le hVR
  let := D.module_elementary
  have hVe : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVR
  have hVc : Nat.card V = 256 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv,source_a5_zero_module_card D e hn hout hz]
  constructor
  · intro i
    have hc := DihedralFourChoices.card_inf_transportedGamma eR V hVe hVc i
    rw [←hVm,←map_inf _ _ _ R.subtype_injective,card_map_of_injective R.subtype_injective]
    exact hc
  · have hs := congrArg (Subgroup.map R.subtype)
      (DihedralFourChoices.iSup_inf_transportedGamma eR V hVe hVc)
    rw [Subgroup.map_iSup] at hs
    simp_rw [map_inf _ _ R.subtype R.subtype_injective,hVm] at hs
    exact hs

/-- The already-established source kernel assertion now needs only the
literal permutation marking; its geometric size and span are discharged. -/
theorem source_a5_zero_canonical_gamma_kernel_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (eR : ChapterB.baumann (T : Subgroup G) ≃* (Fin 4 → DihedralGroup 4))
    (hTF : ∀ t ∈ (T : Subgroup G), ∀ i, ∃ j,
      ((transportedGamma eR i).map (ChapterB.baumann (T : Subgroup G)).subtype).map
        (MulAut.conj t).toMonoidHom =
      (transportedGamma eR j).map (ChapterB.baumann (T : Subgroup G)).subtype) :
    (⨅ i, normalizer (((transportedGamma eR i).map
      (ChapterB.baumann (T : Subgroup G)).subtype : Subgroup G) : Set G)) ≤ D.maximalLocal := by
  let R := ChapterB.baumann (T : Subgroup G)
  let F := fun i => (transportedGamma eR i).map R.subtype
  let eF (i : Fin 4) : F i ≃* DihedralGroup 4 × Remainder i :=
    ((transportedGamma eR i).equivMapOfInjective R.subtype R.subtype_injective).symm.trans
      (transportedGammaEquiv eR i)
  obtain ⟨hc,hs⟩ := source_a5_zero_module_gamma_geometry D e hn hout hz eR
  apply source_a5_zero_normalizer_kernel_le D e hn hout hz F Remainder eF hTF ?_ hs
  intro i
  rw [remainder_card]
  exact hc i

/-- The actual canonical enlargement kernel lies in M; no geometric or
permutation premise remains beyond the chosen four-dihedral recognition. -/
theorem source_a5_zero_canonical_gamma_kernel
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (eR : ChapterB.baumann (T : Subgroup G) ≃* (Fin 4 → DihedralGroup 4)) :
    (⨅ i, normalizer (ambientGamma (ChapterB.baumann (T : Subgroup G)) eR i : Set G)) ≤
      D.maximalLocal := by
  apply source_a5_zero_canonical_gamma_kernel_le D e hn hout hz eR
  intro t ht i
  have htN : t ∈ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) :=
    normalizer_le_normalizer_baumann (T : Subgroup G) ((T : Subgroup G).le_normalizer ht)
  exact ⟨normalizerFactorAction _ eR ⟨t,htN⟩ i,map_ambientGamma _ eR ⟨t,htN⟩ i⟩

end CFSG.Quasithin.Chapter10
