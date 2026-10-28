module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupComponent
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupCharacteristic
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSCentralOrbit

/-!
# Source overgroup Sylow promotion in the symplectic MS construction

The source 9.3.3 nontrivial two-core conclusion supplies source 9.3.4,
discharging the Sylow premise of the actual central-orbit construction.
The original tensor pair then supplies the actual residual component and
its product with T₁. The final specialization uses the source central
involution and tensor core geometry to discharge characteristic two.
The literal symplectic quotient is the remaining source 9.3.7–9 input.
No natural-module recognition or core reconstruction is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemmas 9.3.3–10, printed pp.733–734.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC.MSCentralOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The source overgroup's nontrivial two-core discharges the actual MS Sylow input. -/
theorem source_tensor_sp4_msCentralOrbit_of_local_outside
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k * r = g) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    IsElementaryAbelian 2 (omegaOrbit R) ∧
      centralizer (omegaOrbit R : Set H) = pCore 2 H ∧
      ¬ K ≤ centralizer (omegaOrbit R : Set H) :=
  source_tensor_sp4_msCentralOrbit D hn H hRH hLH hout
    (source_a5_local_outside_overgroup_sylow D e hn hcore hLH hRH hout)
    K hK hF eK hfit hprod

/-- The original tensor pair supplies the actual residual component and product for MS. -/
theorem source_tensor_sp4_msCentralOrbit_of_original_pair
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H B U : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hgen : H = (L ⊔ B) ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hout : ¬ H ≤ D.maximalLocal)
    (hB : B ∈ Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hQ : L.pCoreIn 2 ≤ centralizer (componentOrbit U L : Set G))
    (hBU : B ≤ centralizer (U : Set G))
    (hmove : ¬ B ≤ centralizer (componentOrbit U L : Set G))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    IsElementaryAbelian 2 (omegaOrbit R) ∧
      centralizer (omegaOrbit R : Set H) = pCore 2 H ∧
      ¬ (pResidual 2 H) ≤ centralizer (omegaOrbit R : Set H) := by
  obtain ⟨hK, _, _, hprod⟩ := source_a5_tensor_pair_component_product D e hn H B U
    hcore hgen hout hB hQ hBU hmove
  exact source_tensor_sp4_msCentralOrbit_of_local_outside D e hn H hcore
    (hgen ▸ le_sup_right) (hgen ▸ le_sup_of_le_left le_sup_left) hout
    (pResidual 2 H) hK hF eK hfit hprod

/-- Source central-involution and tensor geometry also discharge the Fitting premise. -/
theorem source_tensor_sp4_msCentralOrbit_of_tensor_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H B U : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hgen : H = (L ⊔ B) ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hout : ¬ H ≤ D.maximalLocal)
    (hB : B ∈ Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hQ : L.pCoreIn 2 ≤ centralizer (componentOrbit U L : Set G))
    (hBU : B ≤ centralizer (U : Set G))
    (hmove : ¬ B ≤ centralizer (componentOrbit U L : Set G))
    (hU : U ≤ H.pCoreIn 2)
    (hCT : (T : Subgroup G) ⊓ centralizer (componentOrbit U L : Set G) ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G))
    (z : G) (hz : orderOf z = 2) (hzU : z ∈ U)
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      Matrix.symplecticGroup (Fin 2) F) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    IsElementaryAbelian 2 (omegaOrbit R) ∧
      centralizer (omegaOrbit R : Set H) = pCore 2 H ∧
      ¬ (pResidual 2 H) ≤ centralizer (omegaOrbit R : Set H) := by
  have hfit := (source_a5_outside_characteristicTwo_of_tensor_core D e hn H U hcore
    (hgen ▸ le_sup_of_le_left le_sup_left) (hgen ▸ le_sup_right) hout
    hU hCT z hz hzU hzc).2
  exact source_tensor_sp4_msCentralOrbit_of_original_pair D e hn H B U hcore
    hgen hout hB hQ hBU hmove hF eK hfit

end CFSG.Quasithin.Chapter10
