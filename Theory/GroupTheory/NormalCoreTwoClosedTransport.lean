module
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.Hall.TwoClosedTransport
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Normal cores and two-closedness through source quotients

Normal cores commute with pullback through a surjection. A group mapping
onto a two-group has a normal Sylow two-subgroup when its kernel becomes
central modulo a normal two-subgroup: apply central-kernel transport in
the quotient and then lift through the two-group kernel.

Source application: the normal-core lift in Aschbacher–Smith E.2.9.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem normalCore_comap_of_surjective (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup H) : (M.comap f).normalCore = M.normalCore.comap f := by
  apply le_antisymm ?_ (normal_le_normalCore.mpr (comap_mono M.normalCore_le))
  apply map_le_iff_le_comap.mp
  let : ((M.comap f).normalCore.map f).Normal := Normal.map inferInstance f hf
  apply normal_le_normalCore.mpr
  exact (map_mono (M.comap f).normalCore_le).trans (map_comap_le _ _)

noncomputable def normalCoreQuotientEquiv (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup H) : G ⧸ (M.comap f).normalCore ≃* H ⧸ M.normalCore :=
  QuotientGroup.equivOfSurjectiveComap f hf _ _ (normalCore_comap_of_surjective f hf M).symm

variable [Finite G] [Finite H]
theorem odd_pCore_index_of_surjective_two_kernel (f : G →* H)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hi : Odd (pCore 2 H).index) : Odd (pCore 2 G).index := by
  rw [index_eq_card,Nat.card_congr (f.pCoreQuotientEquiv hf hk).toEquiv,← index_eq_card]
  exact hi

omit [Finite G] [Finite H] in
theorem normalSylowTwo_of_odd_pCore_index (hi : Odd (pCore 2 G).index) :
    ∃ S : Sylow 2 G, (S : Subgroup G).Normal := by
  refine ⟨(pCore_isPGroup (p := 2) (G := G)).toSylow hi.not_two_dvd_nat,?_⟩
  change (pCore 2 G).Normal
  infer_instance

omit [Finite H] in
theorem odd_pCore_index_of_central_kernel_mod_two (f : G →* H)
    (hf : Function.Surjective f) (hH : IsPGroup 2 H)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hNker : N ≤ f.ker) (hcomm : ⁅f.ker,⊤⁆ ≤ N) :
    Odd (pCore 2 G).index := by
  let q := QuotientGroup.mk' N
  let b := QuotientGroup.lift N f hNker
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨q x,rfl⟩
  have hk : b.ker ≤ center (G ⧸ N) := by
    rw [QuotientGroup.ker_lift,← centralizer_univ,← coe_top]
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective N),← map_commutator]
    apply (map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact hcomm
  have hHcore : pCore 2 H = ⊤ := top_unique (le_sSup ⟨inferInstance,hH.to_subgroup ⊤⟩)
  have hbidx : Odd (pCore 2 (G ⧸ N)).index :=
    OddHall.odd_pCore_index_of_surjective_central_kernel b hb hk (by rw [hHcore,index_top]; decide)
  apply odd_pCore_index_of_surjective_two_kernel q (QuotientGroup.mk'_surjective N) _ hbidx
  rw [show q.ker = N from QuotientGroup.ker_mk' N]
  exact hN
end Subgroup
