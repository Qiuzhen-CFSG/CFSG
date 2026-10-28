module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryMaximal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalNoncentralExclusion

/-!
# Maximality of the original Chapter12 binary-triality container

The complete same-residual container reduction excludes every proper local
enlargement of the surviving binary-triality component. On the literal chosen
whole module, source 1.2.7 now gives its actual maximal two-local normalizer.
The same component is normal in the whole omega centralizer, and normalizers
of all nonzero subgroups of the original omega center normalize it.

This retains both original Hall subgroups, the full original Sylow, the
PSL₂(8) residual and all quotient kernels. It does not exclude binary triality
or supply SourceLocalCartanEscape; the ambient exclusion remains required.
Source: Aschbacher--Smith 1.2.4, 1.2.7 and 5.1.13, printed pp.505--506,
635--638, with the literal 12.2.2 application, printed p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The original selected binary component is maximal and has the stated
normalizer control, while the whole chosen module and residual are unchanged. -/
theorem rankOne_local_cartan_binary_component_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype
    n = 2 ∧ IsOneOrTwoA5Modules L (layer L (RankOneModule.wholeReduced T L)) ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
      X ∈ Chapter1.LStar G (T : Subgroup G) ∧
      IsMaximalTwoLocal (normalizer (X : Set G)) ∧
      normalizer (X : Set G) ≠ ⊤ ∧
      residual H ≤ X ∧ X ≤ omegaCentralizer T ∧
      (X.subgroupOf (omegaCentralizer T)).IsCComponent ∧
      (X.subgroupOf (omegaCentralizer T)).Normal ∧
      Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X) ∧
      ∀ Z₀ : Subgroup G, Z₀ ≤ omegaOneCenterAmbient (T : Subgroup G) → Z₀ ≠ ⊥ →
        normalizer (Z₀ : Set G) ≤ normalizer (X : Set G) := by
  let hi := a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  let X := C.map Y.subtype
  obtain ⟨hn2,_,_,_,hw,_,_⟩ := BinaryOmega.original_binary_triality_module_and_hall
    hi hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,hCn,hr⟩ := LocalSieve.binaryTriality_residual_section hi.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm
  have hmax := BinaryOmega.original_binary_triality_maximal
    hi hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hu,_⟩ := BinaryOmega.original_binary_triality_overgroup_control
    hi hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hCnY : (X.subgroupOf Y).Normal := by
    simpa only [X,subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hTN : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (hH.1.1.2.trans hY.2).trans
      ((normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp hCnY)
  have he : componentOrbit X (T : Subgroup G) = X :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer X T X le_rfl hTN)
      (le_componentOrbit X T)
  have hNM := hu.normalizer_maximal
  have hNP := hu.normalizer_proper
  rw [he] at hNM hNP
  exact ⟨hn2,hw,hr,hmax,hNM,hNP,BinaryOmega.original_binary_triality_omega_normalizers
    hi hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
