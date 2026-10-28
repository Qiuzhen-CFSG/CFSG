module
public import Theory.GroupTheory.SymmetricThreeResidualKernel
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Characteristic two in a symmetric-three orbit action

Let H normalize a two-group U and a subgroup K with K/O₂(K) ≃ S₃.
Suppose a marked subgroup S generates U under H, K centralizes Z(U),
and C_K(U) is a two-group. Every surjective K-action whose kernel fixes S
has characteristic two.

If the image fails characteristic two, its cubic residual centralizes its
two-core. Thus [O₂(K),O²(K)] fixes S, and H-normality makes it fix U.
Coprime commutator idempotence puts [U,O²(K)] in Z(U), which K fixes;
a second application makes O²(K) fix U. The two-group kernel would then
make K a two-group, contradicting its S₃ quotient.

Source application: Aschbacher--Smith, 14.3.31, printed p.1003, applied to
the actual image K⁺ in Ke/C_Ke(Ue). All normality is relative to H.
-/

public section
open Subgroup Theory.GroupTheory
namespace SymmetricThreeTwoCore
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- The literal action image has F* = O₂; its kernel need only fix the marked seed. -/
theorem orbit_action_structure
    (H U S K : Subgroup G) (hUH : U ≤ H) (hKH : K ≤ H)
    (hUN : H ≤ normalizer (U : Set G)) (hKN : H ≤ normalizer (K : Set G))
    (hU : IsPGroup 2 U) (hspan : U = conjugateSpanBy S H)
    (hcenter : K ≤ centralizer ((center U).map U.subtype : Set G))
    (hfaith : IsPGroup 2 ((centralizer (U : Set G)).subgroupOf K))
    (model : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))
    (f : K →* D) (hf : Function.Surjective f)
    (hfix : f.ker ≤ (centralizer (S : Set G)).subgroupOf K) :
    IsPGroup 2 f.ker ∧ generalizedFitting D = pCore 2 D ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 3)) := by
  let Q := (pCore 2 K).map K.subtype
  let R := (pResidual 2 K).map K.subtype
  let C := ⁅Q,R⁆
  let M := ⁅U,R⁆
  have hQN : H ≤ normalizer (Q : Set G) :=
    hKN.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hRN : H ≤ normalizer (R : Set G) :=
    hKN.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hCN : H ≤ normalizer (C : Set G) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hQN hh),
      mem_normalizer_iff_map_conj_eq.mp (hRN hh)]
  have hMN : K ≤ normalizer (M : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hUN (hKH hk)),
      mem_normalizer_iff_map_conj_eq.mp (hRN (hKH hk))]
  have hcontr (hRU : R ≤ centralizer (U : Set G)) : False := by
    have hRp : IsPGroup 2 (pResidual 2 K) := hfaith.to_le (by
      intro r hr
      exact hRU (mem_map_of_mem K.subtype hr))
    have hKp := isPGroup_of_residual_isPGroup 2 hRp
    have htop : pCore 2 K = ⊤ := top_unique (le_sSup ⟨inferInstance,hKp.to_subgroup ⊤⟩)
    have hc := core_index model
    rw [htop,index_top] at hc
    omega
  have hk : IsPGroup 2 f.ker := by
    rcases normal_twoGroup_or_residual_le model f.ker with hp | hr
    · exact hp
    · exfalso
      apply hcontr
      rw [hspan]
      apply le_centralizer_conjugateSpanBy_of_normalizes R S H hRN
      rintro r ⟨k,hk,rfl⟩
      exact hfix (hr hk)
  let ed := (f.pCoreQuotientEquiv hf hk).symm.trans model
  refine ⟨hk, ?_, ⟨ed⟩⟩
  by_contra hbad
  have hcomm : ⁅pCore 2 K,pResidual 2 K⁆ ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    apply le_bot_iff.mp
    have hp : (pCore 2 K).map f ≤ pCore 2 D :=
      le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
    apply (commutator_mono hp (map_pResidual_le 2 f)).trans
    exact (commutator_eq_bot_iff_le_centralizer.mpr (core_centralizes_residual ed hbad)).le
  have hCS : C ≤ centralizer (S : Set G) := by
    change ⁅(pCore 2 K).map K.subtype,(pResidual 2 K).map K.subtype⁆ ≤ _
    rw [←map_commutator]
    rintro x ⟨k,hk,rfl⟩
    exact hfix (hcomm hk)
  have hCU : C ≤ centralizer (U : Set G) := by
    rw [hspan]
    exact le_centralizer_conjugateSpanBy_of_normalizes C S H hCN hCS
  have hMU : M ≤ U := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (hKH.trans hUN))
  have hMK : M ≤ K := (commutator_mono le_rfl (map_subtype_le _)).trans (le_normalizer_iff_commutator_le_right.mp (hUH.trans hKN))
  have hMQ : M ≤ Q := isPGroup_le_pCoreAmbient_of_isSubnormalIn K M 2 hMK
    (normal_subgroupOf_of_le_normalizer hMN).isSubnormal (hU.to_le hMU)
  have hid : ⁅M,R⁆ = M := commutator_isPPerfect_idempotent R U
    (isPPerfect_embedded_pResidual 2 K) hU ((map_subtype_le _).trans (hKH.trans hUN))
  have hMC : M ≤ C := hid.symm.le.trans (commutator_mono hMQ le_rfl)
  have hMZ : M ≤ (center U).map U.subtype := by
    intro m hm
    refine ⟨⟨m,hMU hm⟩,mem_center_iff.mpr ?_,rfl⟩
    intro u
    exact Subtype.ext (hCU (hMC hm) u u.property)
  have hMR : M ≤ centralizer (R : Set G) :=
    hMZ.trans (le_centralizer_iff.mp ((map_subtype_le _).trans hcenter))
  have hMbot : M = ⊥ := hid ▸ commutator_eq_bot_iff_le_centralizer.mpr hMR
  have hRU : R ≤ centralizer (U : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hMbot)
  exact hcontr hRU

end SymmetricThreeTwoCore
