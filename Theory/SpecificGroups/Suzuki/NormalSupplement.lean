module
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Normal Suzuki supplements in groups with trivial two-core

A normal Suzuki subgroup with a Sylow two-supplement is the whole group.
Its centralizer embeds in the two-group quotient and is killed by O₂(H)=1.
The quotient then embeds in the Suzuki outer automorphism group, whose order
is odd. Every elementary subgroup of the prescribed Sylow consequently
lies in the normal Suzuki subgroup and in the center of its Sylow intersection.

Source: Aschbacher–Smith E.2.7, printed p.218, the normal Bender branch.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups
variable {H : Type*} [Group H] [Finite H]

theorem suzuki_normal_sylow_supplement_eq_top (K : Subgroup H) [K.Normal] (T : Sylow 2 H)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {m : ℕ} (hm : 0 < m) (e : K ≃* SuzukiMatrixGroup m) : K = ⊤ := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup K := e.isSimpleGroup
  have ha : ¬ IsMulCommutative K := by
    intro hc
    let := hc
    let : Group.IsSolvable K := Group.isSolvable_of_comm (fun a b : K => mul_comm a b)
    exact External.suzukiMatrixGroup_not_isSolvable m hm
      (Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective)
  have hquot : IsPGroup 2 (H ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen
  have hC := Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient K ha hquot hcore
  have hodd : Odd (Nat.card (MulAut.Outer K)) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact suzuki_odd_outer_index m (by omega)
  have hd := Subgroup.card_dvd_of_injective (MulAut.outerAction K)
    (MulAut.outerAction_injective K hC)
  obtain ⟨r, hr⟩ := hquot.exists_card_eq
  apply Subgroup.index_eq_one.mp
  change Nat.card (H ⧸ K) = 1
  exact Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right r) hd (dvd_of_eq hr)

theorem suzuki_normal_sylow_supplement_placement (K : Subgroup H) [K.Normal] (T : Sylow 2 H)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {m : ℕ} (hm : 0 < m) (e : K ≃* SuzukiMatrixGroup m)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T) :
    V ≤ K ∧ ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup H).subgroupOf K ∧
      V.subgroupOf K ≤ (center S).map (S : Subgroup K).subtype := by
  have hVK : V ≤ K := by rw [suzuki_normal_sylow_supplement_eq_top K T hgen hcore hm e]; exact le_top
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  refine ⟨hVK, S, hS, ?_⟩
  let : IsElementaryAbelian 2 (V.subgroupOf K) := IsElementaryAbelian.subgroupOf hVK
  rw [← suzukiSylow_omega_eq_center hm e S, ← omegaOneAmbient_eq_self (V.subgroupOf K)]
  apply omegaOneAmbient_mono
  rw [hS]
  exact comap_mono hVT
end BenderSuzuki.MatrixGroups
