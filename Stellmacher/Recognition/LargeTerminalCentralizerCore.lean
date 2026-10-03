module

public import Stellmacher.Recognition.LargeTerminalResidual
public import Stellmacher.SectionNine.EmbeddedOrderTwoVertex
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The large residual in a full ambient involution centralizer

The large terminal configuration supplies an involution generating the
omega-center of the prescribed ambient Sylow. Its full centralizer is of
characteristic two. The actual first residual lies in that centralizer's
two-core, which lies in the two-core of the original second local member.

Section Nine identifies the first-step vertex with that second member and
makes its residual subnormal in the full omega-center centralizer. The
order-two center line identifies this with an involution centralizer.
Subnormal core monotonicity gives the lower containment. The centralizer's
normal two-core lies in the prescribed Sylow and is normalized by the
second local member, giving the upper containment. No equality between
that local member and the full centralizer is assumed.

Source: Stellmacher (5.1)(b), (5.2), (7.5), and (10.1)(18)--(20).
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

private theorem core_map_injective
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (E : Subgroup G) :
    (twoCoreIn E).map f = twoCoreIn (E.map f) := by
  let e := E.equivMapOfInjective f hf
  have h := pCore_map_iso 2 e
  change ((pCore 2 E).map E.subtype).map f =
    (pCore 2 (E.map f)).map (E.map f).subtype
  rw [← h, map_map, map_map]
  rfl

private theorem core_le_local_core
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (P C : Subgroup G) (hSP : (S : Subgroup G) ≤ P) (hPC : P ≤ C) :
    twoCoreIn C ≤ twoCoreIn P := by
  let T := S.subtype (hSP.trans hPC)
  have hcoreS : twoCoreIn C ≤ (S : Subgroup G) := by
    rintro x ⟨c, hc, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := C)).le_sylow_of_normal T hc
  have hcoreP := hcoreS.trans hSP
  have hCN : C ≤ normalizer (twoCoreIn C : Set G) := by
    have h := (pCore 2 C).le_normalizer_map C.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  have hn : ((twoCoreIn C).subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer (hPC.trans hCN)
  have hp : IsPGroup 2 ((twoCoreIn C).subgroupOf P) :=
    ((pCore_isPGroup (p := 2) (G := C)).map C.subtype).comap_subtype
  rw [← map_subgroupOf_eq_of_le hcoreP]
  exact map_mono (show (twoCoreIn C).subgroupOf P ≤ pCore 2 P from le_sSup ⟨hn, hp⟩)

public theorem LargeTerminalContext.involution_centralizer_core
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      ctx.firstResidual ≤ twoCoreIn (centralizer ({z} : Set G)) ∧
      twoCoreIn (centralizer ({z} : Set G)) ≤ twoCoreIn ctx.second ∧
      IsCharacteristicTwoType (centralizer ({z} : Set G)) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let f := K.subtype
  let nineCtx := (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext
  let Z := (ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map f
  let E := (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map f
  let W := omegaOneCenter (S0 : Subgroup G)
  let C := centralizer (W : Set G)
  obtain ⟨_, _, hnext, hsub⟩ := nine_two_ambient_setup nineCtx
  have hZ : Z = W := by
    have hn := (lemma_seven_five ctx.terminal.sectionSeven ctx.terminal.Γ
      ctx.terminal.criticalPath ctx.commuting).next_center.1
    change ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep =
      omegaOneCenter ((S0 : Subgroup G).subgroupOf K) at hn
    change (ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map f = _
    rw [hn]
    have hm := omegaOneCenterAmbient_map_injective f K.subtype_injective
      ((S0 : Subgroup G).subgroupOf K)
    rw [map_subgroupOf_eq_of_le ctx.terminal.sylow_le_join] at hm
    exact hm.symm
  have hWcard : Nat.card W = 2 := by
    obtain ⟨_, hcenter, _, hc, _, _⟩ := ctx.first_residual_structure
    change CenterAmbient ctx.firstResidual = Z at hcenter
    rw [← hZ, ← hcenter]
    exact (card_map_of_injective ctx.firstResidual.subtype_injective).trans hc
  have hR : ctx.firstResidual ≤ twoCoreIn C := by
    have h := pCoreAmbient_mono_of_isSubnormalIn E C 2 hsub.1 hsub.2
    change twoCoreIn E ≤ twoCoreIn C at h
    rw [← core_map_injective f K.subtype_injective] at h
    exact h
  have hPC : ctx.second ≤ C := by
    have hnextcenter := (lemma_seven_five ctx.terminal.sectionSeven ctx.terminal.Γ
      ctx.terminal.criticalPath ctx.commuting).next_center.2
    have hcent : GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep ≤
        centralizer (ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep : Set K) := by
      change ctx.terminal.Γ.stabilizer ctx.terminal.criticalPath.firstStep ≤
        centralizer (ctx.terminal.Γ.z ctx.terminal.criticalPath.firstStep : Set K)
      rw [hnextcenter]
      exact le_centralizer_iff.mpr ((omegaOneCenter_le_centerAmbient _).trans
        (centerAmbient_le_centralizer _))
    change ctx.second ≤ centralizer (W : Set G)
    rw [← hnext, ← hZ]
    exact (map_mono hcent).trans (map_centralizer_le_centralizer_image _ f)
  have hupper : twoCoreIn C ≤ twoCoreIn ctx.second :=
    core_le_local_core S0 ctx.second C ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1 hPC
  have hZcard : Nat.card (ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep) = 2 := by
    have hm : Nat.card Z = Nat.card (ZAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep) :=
      card_map_of_injective K.subtype_injective
    exact hm.symm.trans ((congrArg (fun U : Subgroup G => Nat.card U) hZ).trans hWcard)
  have hchar := (embedded_orderTwoVertex_residual_subnormal nineCtx
    ctx.terminal.criticalPath.firstStep hZcard).2.2
  change IsCharacteristicTwoType (centralizer (Z : Set G)) at hchar
  rw [hZ] at hchar
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hWcard
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzgen : zpowers z = (⊤ : Subgroup W) := zpowers_eq_top_of_prime_card hWcard hz
  have hzpow : zpowers (z : G) = W := by
    change zpowers (W.subtype z) = W
    rw [← MonoidHom.map_zpowers W.subtype z, hzgen, ← MonoidHom.range_eq_map, range_subtype]
  have hzorder : orderOf (z : G) = 2 := by rw [← Nat.card_zpowers, hzpow]; exact hWcard
  have hC : centralizer ({(z : G)} : Set G) = C := by
    rw [← centralizer_closure, ← zpowers_eq_closure, hzpow]
  exact ⟨z, hzorder, hzpow, hC.symm ▸ hR, hC.symm ▸ hupper, hC.symm ▸ hchar⟩

end Stellmacher.Recognition
