module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointMovement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.Commutator.PerfectCoreKernel
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The actual point-action kernel in F.9 applicability

Coprime commutator idempotence makes the two-residual of the point quotient
kernel fix V₃. The natural invariant pairing puts its remaining displacement
inside V₃, and a second idempotence step makes it fix V. Faithfulness of the
original normal component bounds its commutators by O₂(L), so L normalizes
this residual. Characteristic two in H and uniqueness over LT force the
residual to vanish. Thus the literal normal core of C_H(V₃/V₁) lies in O₂(H).

This proves F.9.1(a)'s kernel clause using the original automizer, point
quotient and subgroup inclusions. The full F.9 source adapter consumes it;
no kernel or residual-vanishing conclusion is assumed.
Source: Aschbacher–Smith 13.3.18(1), printed p.894.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

/-- Coprime action twice kills the actual two-perfect kernel on the
natural module, first on the seed and then on its self-orthogonal quotient. -/
theorem twoPerfect_point_kernel_centralizes_module
    (U Z Y:Subgroup G) (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E U=seed) (hUV:U≤V)
    (hp:IsPPerfect 2 Y) (hYU:Y≤normalizer (U:Set G))
    (hYV:Y≤normalizer (V:Set G)) (hc:⁅U,Y⁆≤Z)
    (hYZ:Y≤centralizer (Z:Set G)) : Y≤centralizer (V:Set G) := by
  let :IsElementaryAbelian 2 U:=IsElementaryAbelian.of_le hUV
  have hU:⁅U,Y⁆=⊥ := by
    rw [←commutator_isPPerfect_idempotent Y U hp (IsElementaryAbelian.isPGroup 2 U) hYU]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (le_centralizer_iff.mp hYZ))
  have hYS:Y≤centralizer (U:Set G):=le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hU)
  have hVU:⁅V,Y⁆≤U:=commutator_le_seed_of_point_centralizer V U Y rho E he hs hYV hYS
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←commutator_isPPerfect_idempotent Y V hp (IsElementaryAbelian.isPGroup 2 V) hYV]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hVU.trans (le_centralizer_iff.mp hYS))

/-- The literal normal point-kernel lies in O₂(H). Its two-residual is
killed by the natural action, the faithful component and source uniqueness. -/
theorem point_kernel_le_twoCore
    (T:Sylow 2 G) (L H M U Z K:Subgroup G) [Group.IsPerfect L]
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E U=seed) (hUV:U≤V)
    (hKH:K≤H) (hHK:H≤normalizer (K:Set G))
    (hKN:K≤normalizer (V:Set G)) (hKU:K≤normalizer (U:Set G))
    (hc:⁅U,K⁆≤Z) (hHZ:H≤centralizer (Z:Set G))
    (hTH:(T:Subgroup G)≤H) (hTL:(T:Subgroup G)≤normalizer (L:Set G))
    (hLN:L≤normalizer (V:Set G)) (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (hout:¬H≤M) (hchar:Theory.GroupTheory.generalizedFitting H=pCore 2 H) :
    K≤H.pCoreIn 2 := by
  let Y:Subgroup G:=(pResidual 2 K).map K.subtype
  have hYK:Y≤K:=map_subtype_le _
  have hHY:H≤normalizer (Y:Set G):=hHK.trans
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hYC:Y≤centralizer (V:Set G):=twoPerfect_point_kernel_centralizes_module
    U Z Y rho E he hs hUV (isPPerfect_embedded_pResidual 2 K)
    (hYK.trans hKU) (hYK.trans hKN) ((commutator_mono le_rfl hYK).trans hc)
    (hYK.trans (hKH.trans hHZ))
  have hLQ:L≤normalizer (L.pCoreIn 2:Set G):=L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLC:⁅L,centralizer (V:Set G)⁆≤L.pCoreIn 2:=
    perfect_core_commutator L V hLN hNL
      ((commutator_mono hfaith le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hLQ))
  have hQH:L.pCoreIn 2≤H := by
    have hm:L.pCoreIn 2≤(L⊔(T:Subgroup G)).pCoreIn 2:=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer hTL)
    have hh:=pCoreIn_le_sylow (L⊔(T:Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hh
    exact hm.trans (hh.trans hTH)
  have hLY:L≤normalizer (Y:Set G):=normalizes_residual_of_commutator_le_two
    L H K (L.pCoreIn 2) hHK hQH (isPGroup_pCoreIn 2 L) hLQ
    ((commutator_mono le_rfl hYC).trans hLC)
  have hself:H⊓centralizer (H.pCoreIn 2:Set G)≤H.pCoreIn 2 := by
    intro x hx
    have hc':(⟨x,hx.1⟩:H)∈centralizer (pCore 2 H:Set H) := by
      intro q hq
      exact Subtype.ext (hx.2 q.val (mem_map_of_mem H.subtype hq))
    have hh:=Theory.GroupTheory.centralizer_generalizedFitting_le H
    rw [hchar] at hh
    exact mem_map_of_mem H.subtype (hh hc')
  have hY:Y=⊥:=normal_eq_bot_of_unique_core (L⊔(T:Subgroup G)) H M Y hu hout
    hself (hYK.trans hKH) hHY (sup_le hLY (hTH.trans hHY))
  have hres:pResidual 2 K=⊥:=(map_eq_bot_iff_of_injective _ K.subtype_injective).mp hY
  have hp:IsPGroup 2 K:= (isPGroup_quotient_pResidual (G:=K) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 K)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hres])
  exact le_pCoreIn_of_normalizes hp hKH hHK


open scoped commutatorElement
/-- F.9.1(a)'s actual intrinsic normal-core bound, derived from the original
point quotient action instead of assuming its kernel is a two-group. -/
theorem normalCore_point_kernel_le
    (T:Sylow 2 G) (L H M U Z:Subgroup G) [Group.IsPerfect L]
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E U=seed) (hUV:U≤V) (hVH:V≤H) (hZU:Z≤U)
    (hHZ:H≤centralizer (Z:Set G))
    (hcontrol:H⊓normalizer (U:Set G)≤normalizer (V:Set G))
    (hTH:(T:Subgroup G)≤H) (hTL:(T:Subgroup G)≤normalizer (L:Set G))
    (hLN:L≤normalizer (V:Set G)) (hNL:normalizer (V:Set G)≤normalizer (L:Set G))
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (hout:¬H≤M) (hchar:Theory.GroupTheory.generalizedFitting H=pCore 2 H) :
    let :(Z.subgroupOf H).Normal:=normal_subgroupOf_of_le_normalizer
      (hHZ.trans (Subgroup.centralizer_le_normalizer _))
    (centralizerModulo (⊤:Subgroup H) (U.subgroupOf H) (Z.subgroupOf H)).normalCore≤pCore 2 H := by
  let :(Z.subgroupOf H).Normal:=normal_subgroupOf_of_le_normalizer
    (hHZ.trans (Subgroup.centralizer_le_normalizer _))
  dsimp only
  let K₀:Subgroup H:=(centralizerModulo (⊤:Subgroup H) (U.subgroupOf H) (Z.subgroupOf H)).normalCore
  let K:Subgroup G:=K₀.map H.subtype
  have hKH:K≤H:=map_subtype_le _
  have hHK:H≤normalizer (K:Set G) := by
    have hh:=K₀.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hc:⁅U,K⁆≤Z := by
    apply commutator_le.mpr
    intro u hu k hk
    obtain ⟨k,hk,rfl⟩:=hk
    have hm:=mem_centralizerModulo_iff.mp (Subgroup.normalCore_le _ hk)
    exact hm.2 ⟨u,hVH (hUV hu)⟩ hu
  have hKU:K≤normalizer (U:Set G):=
    le_normalizer_iff_commutator_le_left.mpr (hc.trans hZU)
  have hKN:K≤normalizer (V:Set G):=(le_inf hKH hKU).trans hcontrol
  have hb:=point_kernel_le_twoCore T L H M U Z K rho E he hs hUV hKH hHK hKN hKU hc hHZ
    hTH hTL hLN hNL hfaith hu hout hchar
  intro k hk
  obtain ⟨a,ha,heq⟩:=hb (mem_map_of_mem H.subtype hk)
  exact (Subtype.ext heq: a=k) ▸ ha
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
