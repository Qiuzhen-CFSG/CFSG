module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityDefs
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityParabolic

/-!
# Elimination of the central factor in the higher-dimensional rigidity argument

Let R=C_T(U) and Y=O²(N_L(U∩V)). The cyclic pair normalizes R. If Y is
normal in N_G(R) and C_R(Y)=C_T(L), then that pair normalizes C_T(L).
This subgroup is central in LT, so source uniqueness and escape force it
to vanish. The two centralizer splittings then put T inside L and identify
O₂(L) with the original V. Characteristic two in the actual normalizers
and centralizers upgrades the Sylow equalities to C_G(V)=V and C_G(U)=U.

The component-normalizer and fixed-space assertions remain explicit inputs.
This file does not prove the component classification, dimension cutoff,
tensor identification, or parabolic factorization.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, 12.2.25,
printed pp.805--806, the uniqueness argument after the A₇ exclusion.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G} {d : ℕ}

theorem higher_pair_normalizes_sylow_centralizer (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    cyclicPairJoin P U V ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
  let := C.elementary
  have hT : (T : Subgroup G) ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hP : P ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [C.sylow_centralizer_core_commutator (by have := A.dimension.1; omega)]
    exact le_inf C.core_le_sylow (le_centralizer U)
  exact sup_le (sup_le hP (C.core_le_sylow.trans hT)) (D.le_sylow.trans hT)

theorem higher_component_centralizer_eq_bot_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G))
    (hf : ((T : Subgroup G) ⊓ centralizer (U : Set G)) ⊓
      centralizer (rigidityHyperplaneResidual L U V : Set G) =
        (T : Subgroup G) ⊓ centralizer (L : Set G)) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  apply chosen_common_normal_subgroup_eq_bot h D C
    (inf_le_left.trans le_sup_right)
  · apply (sup_le ?_ ?_).trans (Subgroup.centralizer_le_normalizer _)
    · exact le_centralizer_iff.mp inf_le_right
    · exact le_centralizer_iff.mp B.component_centralizer_central
  · rw [← hf]
    exact (higher_pair_normalizes_sylow_centralizer D A C).trans
      ((le_inf le_rfl (hn.trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf)

omit [Finite G] in
theorem higher_kernel_vanishing_consequences (D : ChosenModule T L V)
    (B : LocalRigidityCentralizers T L V U P)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    (T : Subgroup G) ≤ L ∧ L.pCoreIn 2 = V ∧
      (T : Subgroup G) ⊓ centralizer (V : Set G) = V ∧
      (T : Subgroup G) ⊓ centralizer (U : Set G) = U := by
  have hT : (T : Subgroup G) ≤ L := by
    have he := B.sylow_split
    rw [hzero, sup_bot_eq] at he
    exact he.le.trans inf_le_right
  have he : L ⊔ (T : Subgroup G) = L := sup_eq_left.mpr hT
  have hQ : (T : Subgroup G) ⊓ centralizer (V : Set G) = V := by
    simpa only [hzero, sup_bot_eq] using B.kernel_split
  have hcoreT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT] using
      pCoreIn_le_sylow L (T.subtype hT)
  have hcoreV : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
    simpa only [he] using D.core_centralizes
  refine ⟨hT, le_antisymm ?_ D.le_componentCore, hQ, ?_⟩
  · exact (le_inf hcoreT hcoreV).trans hQ.le
  · simpa only [hzero, sup_bot_eq] using B.centralizer_split

private theorem centralizer_eq_of_sylow_centralizer
    (hE : IsEvenCharacteristicAt T) {W : Subgroup G}
    (hne : W ≠ ⊥) (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (he : (T : Subgroup G) ⊓ centralizer (W : Set G) = W) :
    centralizer (W : Set G) = W := by
  have hWT : W ≤ (T : Subgroup G) := he.symm.le.trans inf_le_left
  have hWC : W ≤ centralizer (W : Set G) := he.symm.le.trans inf_le_right
  have hN : normalizer (W : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T hE
      ⟨W, hne, T.isPGroup'.to_le hWT, rfl⟩ hTW
  have hCN : centralizer (W : Set G) ≤ normalizer (W : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hC : centralizer (W : Set G) ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hN (ne_bot_of_le_ne_bot hne hWC) hCN
      (normal_subgroupOf_centralizer_normalizer (W : Set G)).isSubnormal
  have hcoreT : (normalizer (W : Set G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTW] using
      pCoreIn_le_sylow (normalizer (W : Set G)) (T.subtype hTW)
  have hcoreW : (centralizer (W : Set G)).pCoreIn 2 ≤ W := by
    apply (le_inf ?_ (pCoreIn_le 2 _)).trans he.le
    exact (pCoreIn_mono_of_normalizes hCN (normalizer_le_normalizer_centralizer W)).trans hcoreT
  apply le_antisymm ?_ hWC
  exact (le_inf le_rfl (centralizer_le hcoreW)).trans (hC.trans hcoreW)

theorem higher_selfCentralizing_of_kernel_vanishing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (B : LocalRigidityCentralizers T L V U P)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥) :
    centralizer (V : Set G) = V ∧ centralizer (U : Set G) = U := by
  have hs := higher_kernel_vanishing_consequences D B hzero
  exact ⟨centralizer_eq_of_sylow_centralizer (h.simpleQTKE.evenCharacteristic T)
      D.ne_bot (((structural G T L h).2.2 V D).1) hs.2.2.1,
    centralizer_eq_of_sylow_centralizer (h.simpleQTKE.evenCharacteristic T)
      (C.core_ne_bot (by have := A.dimension.1; omega)) C.sylow_normalizes_core hs.2.2.2⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
