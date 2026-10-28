module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingCharacteristicCoreSource
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FullActionOvergroup
/-!
# The full original centralizer in the trivial block-centralizer case

When C_T(L)=1, the earlier source argument identifies O2(M) with the
quaternion central product P and M with C_G(Z(P)). Characteristic two makes
P self-centralizing in M. The generated group F=O²(M∩L)T already realizes
the full square action on P/Z(P); the inner-action kernel therefore forces
M=F. The two-group kernel and solvable orthogonal image make M solvable.

All premises are the original minimal block setup and C_T(L)=1.
Source: Aschbacher--Smith, 2.4.29, printed p.545.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_full_centralizer_of_centralizer_bot
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    M = K ⊔ (T : Subgroup G) ∧
      M = centralizer ((center P).map P.subtype : Set G) ∧ Group.IsSolvable M := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let E := P ⊔ D
  let F := K ⊔ (T : Subgroup G)
  have hEP : E = P := by change P ⊔ D=P; rw [show D=⊥ from hD,sup_bot_eq]
  obtain ⟨hcore,hcenter⟩ := d.single_alternating_maximal_core_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD
  change M.pCoreIn 2 = P at hcore
  have hFM : F≤M := sup_le ((map_subtype_le _).trans inf_le_left) hTM
  have hEF : E≤F := hEP.symm ▸ ((pCoreIn_le 2 K).trans le_sup_left)
  have hMN : M≤normalizer (E : Set G) := by
    rw [hEP,←hcore]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hcent : M ⊓ centralizer (E : Set G) ≤ E := by
    rw [hEP,←hcore]
    exact Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  obtain ⟨hd,hp,eE,hn,hfull⟩ := d.single_alternating_whole_square_action hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 D := hd
  have : Subsingleton D := by rw [show D=⊥ from hD]; infer_instance
  obtain ⟨heq,hs⟩ := hp.eq_and_isSolvable_of_full_centralFactor_action E F M eE
    hEF hFM hMN hcent hfull
  exact ⟨heq.symm,hcenter,hs⟩
theorem MinimalBlockSetup.single_alternating_maximal_card_of_centralizer_bot
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥) :
    Nat.card M = 2304 := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let E := P ⊔ D
  let F := K ⊔ (T : Subgroup G)
  have hEP : E = P := by change P ⊔ D=P; rw [show D=⊥ from hD,sup_bot_eq]
  obtain ⟨hcore,_⟩ := d.single_alternating_maximal_core_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD
  change M.pCoreIn 2 = P at hcore
  have hFM : F≤M := sup_le ((map_subtype_le _).trans inf_le_left) hTM
  have hEF : E≤F := hEP.symm ▸ ((pCoreIn_le 2 K).trans le_sup_left)
  have hMN : M≤normalizer (E : Set G) := by
    rw [hEP,←hcore]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hcent : M ⊓ centralizer (E : Set G) ≤ E := by
    rw [hEP,←hcore]
    exact Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  obtain ⟨hd,hp,eE,hn,hfull⟩ := d.single_alternating_whole_square_action hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 D := hd
  have : Subsingleton D := by rw [show D=⊥ from hD]; infer_instance
  exact hp.card_eq_of_full_centralFactor_action E F M eE hEF hFM hMN hcent hfull
end CFSG.Quasithin.Chapter2
