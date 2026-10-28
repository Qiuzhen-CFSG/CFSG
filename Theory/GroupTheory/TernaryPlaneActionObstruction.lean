module

public import Theory.GroupAction.TernaryPlaneGeneration
public import Theory.GroupTheory.NormalizerAction

/-!
# A ternary fixed-plane obstruction in an actual normalizer

Distinct nontrivial three-group actions on an elementary plane, together with
an involution inverting one action, force16 to divide the ambient actor order.
Every action is the literal subgroup-normalizer conjugation homomorphism;
centralizers distinguish the two images. This applies the concrete GL₂(3)
generation calculation without an assumed model for the original action.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem fixed_le_of_normalizer_image_le (L S T:Subgroup G)
    (hS:S≤normalizer (L:Set G))
    (he:(S.subgroupOf (normalizer (L:Set G))).map L.normalizerMonoidHom≤
      (T.subgroupOf (normalizer (L:Set G))).map L.normalizerMonoidHom) :
    L⊓centralizer (T:Set G)≤L⊓centralizer (S:Set G) := by
  rintro l ⟨hl,hlt⟩
  refine ⟨hl,?_⟩
  intro s hs
  let sn:normalizer (L:Set G):=⟨s,hS hs⟩
  obtain ⟨t,ht,heq⟩:=he (mem_map_of_mem L.normalizerMonoidHom (show sn∈S.subgroupOf _ from hs))
  have hh:=congrArg (fun a:MulAut L=>(a ⟨l,hl⟩:G)) heq
  change (t:G)*l*(t:G)⁻¹=s*l*s⁻¹ at hh
  have htl:l*(t:G)=(t:G)*l:=(hlt t ht).symm
  rw [←htl,mul_inv_cancel_right] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh.symm

theorem ternary_plane_normalizer_sixteen (M L S T:Subgroup G) [IsElementaryAbelian 3 L]
    (hL:Nat.card L=9) (hS:IsPGroup 3 S) (hT:IsPGroup 3 T)
    (hSM:S≤M) (hTM:T≤M)
    (hSN:S≤normalizer (L:Set G)) (hTN:T≤normalizer (L:Set G))
    (hSf:L⊓centralizer (S:Set G)≠L) (hTf:L⊓centralizer (T:Set G)≠L)
    (hne:L⊓centralizer (S:Set G)≠L⊓centralizer (T:Set G))
    (z:G) (hzM:z∈M) (hzN:z∈normalizer (L:Set G)) (hz2:z^2=1)
    (hinv:∀s∈S,z*s*z⁻¹*s∈centralizer (L:Set G)) : 16∣Nat.card M := by
  let N:=normalizer (L:Set G)
  let α:=L.normalizerMonoidHom
  let H:=(M.subgroupOf N).map α
  let C:=(S.subgroupOf N).map α
  let D:=(T.subgroupOf N).map α
  have hCn:C≠⊥:=by
    intro hc
    apply hSf
    apply le_antisymm inf_le_left
    have he:(S.subgroupOf N).map α≤((⊥:Subgroup G).subgroupOf N).map α:=by
      simpa only [bot_subgroupOf,map_bot] using hc.le
    have hh:=fixed_le_of_normalizer_image_le L S ⊥ hSN he
    intro l hl
    exact hh ⟨hl,by intro t ht; simp only [mem_bot.mp ht,mul_one,one_mul]⟩
  have hDn:D≠⊥:=by
    intro hc
    apply hTf
    apply le_antisymm inf_le_left
    have he:(T.subgroupOf N).map α≤((⊥:Subgroup G).subgroupOf N).map α:=by
      simpa only [bot_subgroupOf,map_bot] using hc.le
    have hh:=fixed_le_of_normalizer_image_le L T ⊥ hTN he
    intro l hl
    exact hh ⟨hl,by intro t ht; simp only [mem_bot.mp ht,mul_one,one_mul]⟩
  have hCD:C≠D:=by
    intro he
    exact hne (le_antisymm (fixed_le_of_normalizer_image_le L T S hTN he.ge)
      (fixed_le_of_normalizer_image_le L S T hSN he.le))
  let zn:N:=⟨z,hzN⟩
  obtain ⟨a,ha,ha1⟩:=C.bot_or_exists_ne_one.resolve_left hCn
  obtain ⟨s,hs,rfl⟩:=ha
  have hi:α zn*α s*(α zn)⁻¹=(α s)⁻¹:=by
    have hker:zn*s*zn⁻¹*s∈α.ker:=by
      rw [L.normalizerMonoidHom_ker]
      exact hinv s hs
    have hh:α (zn*s*zn⁻¹*s)=1:=hker
    rw [map_mul,map_mul,map_mul,map_inv] at hh
    exact mul_eq_one_iff_eq_inv.mp hh
  have hdiv:16∣Nat.card H:=MulAut.ternary_plane_two_cubics_inverter hL H C D
    (hS.comap_subtype.map α) (hT.comap_subtype.map α) hCn hDn hCD
    (map_mono (subgroupOf_mono N hSM)) (map_mono (subgroupOf_mono N hTM)) (α zn) (α s)
    (mem_map_of_mem α hzM) (by rw [←map_pow,show zn^2=1 from Subtype.ext hz2,map_one])
    (mem_map_of_mem α hs) ha1 hi
  let i:M.subgroupOf N→*M:={
    toFun x:=⟨x.val.val,x.property⟩
    map_one':=rfl
    map_mul' _ _:=rfl }
  have hi:Function.Injective i:=by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v:M=>(v:G)) he
  exact hdiv.trans (((M.subgroupOf N).card_map_dvd α).trans (card_dvd_of_injective i hi))
end Subgroup
