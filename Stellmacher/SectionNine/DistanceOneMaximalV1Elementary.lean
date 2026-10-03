module

public import Stellmacher.SectionNine.DistanceOneV1ActionClassification
public import Theory.GroupTheory.OrderEightCubicQuotientModel
public import Theory.GroupTheory.QuaternionSubgroupFixedEight
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Elementarity of the actual maximal eight

For an order-eight subgroup U satisfying the actual maximal-V₁ action and
commutator hypotheses, suppose U lies in the extracted quaternion product V
of order32. The initial center normalizes V and its intersection with V has
order8. These explicit properties force U to be elementary abelian.

The exact quotient action packet makes U/Z_terminal an elementary group of
order4. Its full residual action is the cyclic-three case of (1.3). Lift a
nonidentity element of this image to actual conjugation on U; the intrinsic
central-extension theorem makes U elementary or quaternion. No odd-order
hypothesis is made on the action upstairs. If U is quaternion, the selected
initial-center involution preserves U and V and fixes the elementary-eight
intersection with the initial center. The fixed-eight quaternion theorem
therefore makes its action on U inner. Such an action is trivial on the
abelian quotient, contradicting the packet's nonidentity quotient involution.

Source: Stellmacher(9.1), Journal of Algebra190 (1997), p.48. This is the
missing elementary-subgroup transfer needed by the terminal quotient proof;
no terminal S3 quotient, core equality or full local conclusion is assumed.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_v1_elementary_of_card_eight
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=1) (U V : Subgroup G)
    (hUQ : U≤q ctx.Γ ctx.criticalPath.a')
    (hZU : z ctx.Γ ctx.criticalPath.a'≤U)
    (hUQc : ⁅U,q ctx.Γ ctx.criticalPath.a'⁆=z ctx.Γ ctx.criticalPath.a')
    (hUE : ⁅U,twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆=U)
    (hUT : U≤T) (hUn : (U.subgroupOf T).Normal)
    (hlow : Nat.card (U⊓Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a:Set G):Subgroup G)<Nat.card U)
    (hupper : Nat.card U≤4*Nat.card (U⊓Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a:Set G):Subgroup G))
    (hUcard : Nat.card U=8) (hZcard : Nat.card (z ctx.Γ ctx.criticalPath.a')=2)
    (hUV : U≤V) (hV : IsCentralProductQ8Q8 V) (hVcard : Nat.card V=32)
    (hseedcard : Nat.card (V⊓z ctx.Γ ctx.criticalPath.a:Subgroup G)=8)
    (hZaV : z ctx.Γ ctx.criticalPath.a≤Subgroup.normalizer (V:Set G)) :
    IsElementaryAbelian 2 U := by
  classical
  let Z := z ctx.Γ ctx.criticalPath.a'
  let P := stabilizer ctx.Γ ctx.criticalPath.a'
  let Za := z ctx.Γ ctx.criticalPath.a
  obtain ⟨hN,hW,hnt,hPU,rho,hcompat,hQker,hfull,x,hx,hxi,hxQ,hrx,hFx,hclass⟩ :=
    distance_one_v1_action_classification ctx hb U hUQ hZU hUQc hUE hUT hUn hlow hupper
  let _ := hN
  let _ := hW
  let W := U⧸Z.subgroupOf U
  let F := ((twoResidualIn P).subgroupOf P).map rho
  have hZnative : Nat.card (Z.subgroupOf U)=2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).trans hZcard
  have hWcard : Nat.card W=4 := by
    have hh := (Z.subgroupOf U).card_mul_index
    rw [hZnative,Subgroup.index_eq_card,hUcard] at hh
    change 2*Nat.card W=8 at hh
    omega
  have hFcard : Nat.card F=3 := by
    cases hclass with
    | cyclicThree _ hmodel =>
      obtain ⟨e⟩ := hmodel
      rw [Nat.card_congr e.toEquiv]
      simp
    | small hc _ _ =>
      rw [hfull,Subgroup.card_top] at hc
      change Nat.card W=2^4 at hc
      omega
    | extraspecial hc _ _ _ _ =>
      rw [hfull,Subgroup.card_top] at hc
      change Nat.card W=2^6 at hc
      omega
  have hFne : F≠⊥ := by
    intro hh
    have hc : Nat.card F=1 := (Subgroup.card_eq_one.mpr hh)
    omega
  obtain ⟨f,hf,hfne⟩ := SetLike.not_le_iff_exists.mp (show ¬F≤⊥ from fun hh => hFne (le_antisymm hh bot_le))
  have hfne : f≠1 := fun hh => hfne (Subgroup.mem_bot.mpr hh)
  obtain ⟨g,hg,hgf⟩ := hf
  have hf : f∈F := ⟨g,hg,hgf⟩
  have hg3 : (rho g)^3=1 := by
    have hh := pow_card_eq_one' (x:=(⟨f,hf⟩:F))
    rw [hFcard] at hh
    have hff : f^3=1 := congrArg Subtype.val hh
    rwa [hgf]
  have hgne : rho g≠1 := hgf ▸ hfne
  let alpha : MulAut U := U.normalizerMonoidHom ⟨(g:G),hPU g.property⟩
  have halpha : ∀u:U,rho g (QuotientGroup.mk' (Z.subgroupOf U) u)=
      QuotientGroup.mk' (Z.subgroupOf U) (alpha u) := hcompat g
  have hcentral : Z.subgroupOf U≤Subgroup.center U :=
    Subgroup.central_of_normal_card_two _ hZnative
  rcases elementary_or_quaternion_of_cubic_quotient_action hUcard (Z.subgroupOf U)
    hZnative hcentral hWcard alpha (rho g) halpha hg3 hgne with hElem | hQuat
  · exact hElem
  obtain ⟨L,R,hL,hR,hjoin,hinter,hcomm,_⟩ := hV
  have hnbor : ctx.criticalPath.a'∈neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood,ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hnbor
  have hseedexp : ∀a∈V⊓Za,a^2=1 := by
    intro a ha
    exact elemPow_eq_one_of_isElementaryAbelian a (show a∈Za from ha.2)
  have hfix : ∀a∈V⊓Za,Commute (x:G) a := by
    intro a ha
    exact setLike_mul_comm (s:=Za) hx ha.2
  obtain ⟨b,hbU,hbact⟩ := Subgroup.inner_on_quaternion_subgroup_of_fixed_eight
    L R U (V⊓Za) hL hR hQuat hinter hcomm (hUV.trans_eq hjoin)
    (hjoin ▸ hVcard) (inf_le_left.trans_eq hjoin) hseedcard hseedexp
    (x:G) (hjoin ▸ hZaV hx) (hPU x.property) hfix
  apply (hrx.1 ?_).elim
  apply MulEquiv.ext
  intro w
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
  rw [hcompat]
  have heq : (⟨(x:G)*(u:G)*(x:G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPU x.property) u).mp u.property⟩:U)=
      (⟨b,hbU⟩:U)*u*(⟨b,hbU⟩:U)⁻¹ := Subtype.ext (hbact u u.property)
  rw [heq,map_mul,map_mul,map_inv]
  change (QuotientGroup.mk' (Z.subgroupOf U) ⟨b,hbU⟩)*
      (QuotientGroup.mk' (Z.subgroupOf U) u)*
      (QuotientGroup.mk' (Z.subgroupOf U) ⟨b,hbU⟩)⁻¹=
      QuotientGroup.mk' (Z.subgroupOf U) u
  rw [mul_comm',inv_mul_cancel_left]
end Stellmacher.SectionNine
