module
public import Theory.GroupAction.FixedIndexTwoResidual
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CentralizerModulo

/-!
# A normal quotient-seed kernel at index two

A two-perfect actor fixing an index-two seed of a two-group fixes the
whole group. Applied to the residual of the normal point-quotient kernel,
this puts that residual in the module centralizer. The faithful local
component and uniqueness over its Sylow extension then kill the residual.
Thus the actual normal kernel lies in the local two-core.

This is the kernel step of F.9.1(a) in Aschbacher–Smith 13.5.7. It uses
only the index-two seed needed by the original ordinary A₆ application.
-/
public section
namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

private theorem twoPerfect_seed_kernel_centralizes
    (V U Z Y : Subgroup G) (hV : IsPGroup 2 V)
    (hUV : U ≤ V) (hi : U.relIndex V = 2) (hp : IsPPerfect 2 Y)
    (hYU : Y ≤ normalizer (U : Set G)) (hYV : Y ≤ normalizer (V : Set G))
    (hc : ⁅U,Y⁆ ≤ Z) (hYZ : Y ≤ centralizer (Z : Set G)) :
    Y ≤ centralizer (V : Set G) := by
  have hUC : ⁅U,Y⁆ = ⊥ := by
    rw [←commutator_isPPerfect_idempotent Y U hp (hV.to_le hUV) hYU]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (le_centralizer_iff.mp hYZ))
  have hYS : Y ≤ centralizer (U : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hUC)
  let ρ : Y →* MulAut V := V.normalizerMonoidHom.comp (inclusion hYV)
  have hfix (y : Y) : ρ y = 1 := by
    apply MulAut.eq_one_of_pPerfect_of_fixed_index_le_two ρ hp hV (U.subgroupOf V)
      (by change U.relIndex V ≤ 2; omega)
    intro y x hx
    apply Subtype.ext
    change y.val*x.val*y.val⁻¹=x.val
    rw [←hYS y.property x.val hx,mul_inv_cancel_right]
  intro y hy v hv
  have he := congrArg (fun f : MulAut V => (f ⟨v,hv⟩ : G)) (hfix ⟨y,hy⟩)
  change y*v*y⁻¹=v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The normal point-quotient kernel is a two-group under the original
unique-local hypothesis and the actual index-two seed. -/
theorem point_kernel_le_twoCore_of_index_two
    (T : Sylow 2 G) (L H M V U Z K : Subgroup G)
    (hV : IsPGroup 2 V) (hUV : U ≤ V) (hi : U.relIndex V = 2)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hKN : K ≤ normalizer (V : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hc : ⁅U,K⁆ ≤ Z) (hHZ : H ≤ centralizer (Z : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLN : L ≤ normalizer (V : Set G))
    (hNL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N=M)
    (hout : ¬H ≤ M)
    (hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2) :
    K ≤ H.pCoreIn 2 := by
  let Y : Subgroup G := (pResidual 2 K).map K.subtype
  have hYK : Y ≤ K := map_subtype_le _
  have hHY : H ≤ normalizer (Y : Set G) := hHK.trans
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hYC : Y ≤ centralizer (V : Set G) := twoPerfect_seed_kernel_centralizes
    V U Z Y hV hUV hi (isPPerfect_embedded_pResidual 2 K)
    (hYK.trans hKU) (hYK.trans hKN) ((commutator_mono le_rfl hYK).trans hc)
    (hYK.trans (hKH.trans hHZ))
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLC : ⁅L,centralizer (V : Set G)⁆ ≤ L.pCoreIn 2 := by
    apply le_trans (le_inf ?_ ?_) hfaith
    · exact le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.centralizer_le_normalizer _).trans hNL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (hLN.trans (normalizer_le_normalizer_centralizer V))
  have hQH : L.pCoreIn 2 ≤ H := by
    have hm : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer hTL)
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hh
    exact hm.trans (hh.trans hTH)
  have hLY : L ≤ normalizer (Y : Set G) := normalizes_residual_of_commutator_le_two
    L H K (L.pCoreIn 2) hHK hQH (isPGroup_pCoreIn 2 L) hLQ
    ((commutator_mono le_rfl hYC).trans hLC)
  have hY : Y=⊥ := normal_eq_bot_of_unique_core (L ⊔ (T : Subgroup G)) H M Y hu hout
    hself (hYK.trans hKH) hHY (sup_le hLY (hTH.trans hHY))
  have hres : pResidual 2 K=⊥ := (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hY
  have hp : IsPGroup 2 K := (isPGroup_quotient_pResidual (G:=K) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 K)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hres])
  exact le_pCoreIn_of_normalizes hp hKH hHK

/-- The literal normal core of the seed quotient centralizer satisfies
F.9.1(a); all ambient subgroup inclusions and the quotient point are retained. -/
theorem normalCore_point_kernel_le_of_index_two
    (T : Sylow 2 G) (L H M V U Z : Subgroup G)
    (hV : IsPGroup 2 V) (hUV : U ≤ V) (hi : U.relIndex V = 2)
    (hVH : V ≤ H) (hZU : Z ≤ U) (hHZ : H ≤ centralizer (Z : Set G))
    (hcontrol : H ⊓ normalizer (U : Set G) ≤ normalizer (V : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLN : L ≤ normalizer (V : Set G))
    (hNL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N=M)
    (hout : ¬H ≤ M)
    (hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2) :
    let : (Z.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
      (hHZ.trans (Subgroup.centralizer_le_normalizer _))
    (centralizerModulo (⊤ : Subgroup H) (U.subgroupOf H)
      (Z.subgroupOf H)).normalCore ≤ pCore 2 H := by
  let : (Z.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (hHZ.trans (Subgroup.centralizer_le_normalizer _))
  dsimp only
  let K₀ : Subgroup H := (centralizerModulo (⊤ : Subgroup H) (U.subgroupOf H)
    (Z.subgroupOf H)).normalCore
  let K : Subgroup G := K₀.map H.subtype
  have hKH : K ≤ H := map_subtype_le _
  have hHK : H ≤ normalizer (K : Set G) := by
    have hh := K₀.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hc : ⁅U,K⁆ ≤ Z := by
    apply commutator_le.mpr
    intro u hu k hk
    obtain ⟨k,hk,rfl⟩ := hk
    have hm := mem_centralizerModulo_iff.mp (Subgroup.normalCore_le _ hk)
    exact hm.2 ⟨u,hVH (hUV hu)⟩ hu
  have hKU : K ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hc.trans hZU)
  have hKN : K ≤ normalizer (V : Set G) := (le_inf hKH hKU).trans hcontrol
  have hb := point_kernel_le_twoCore_of_index_two T L H M V U Z K hV hUV hi
    hKH hHK hKN hKU hc hHZ hTH hTL hLN hNL hfaith hu hout hself
  intro k hk
  obtain ⟨a,ha,heq⟩ := hb (mem_map_of_mem H.subtype hk)
  exact (Subtype.ext heq : a=k) ▸ ha
end Subgroup
