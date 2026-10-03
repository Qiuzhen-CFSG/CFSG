module
public import Stellmacher.SectionNine.DistanceOneVstarFactorSwap
public import Theory.GroupAction.DisjointCubicAutomorphisms

/-!
# The exact residual order-three centralizer on Vstar

In the ambient-retaining distance-one configuration, the explicit faithful and
local conclusions imply that every element of order three in the terminal
residual centralizes only the terminal center inside the exact Vstar. The center
identification is an explicit input, already proved by the parent action module;
there is no assumed fixedfree action or assumed normalizer witness.

The factor-swap prerequisite constructs an actual terminal element interchanging
the two intrinsic quaternion factors. An order-three actor preserves each
factor. If it fixed one factor pointwise, its conjugate by the swapping element
would fix the other. The two induced automorphisms have independent actions on
the generating factors. Their automorphism group is the actual terminal
conjugation range, whose order divides384 and hence is not divisible by nine.
The disjoint cubic-action theorem forces one automorphism to be trivial,
contradicting the previously proved nontriviality on Vstar. Thus both quaternion
restrictions are nontrivial.

Write a fixed element as b*c in the commuting factors. Its fixed-product
equation places each factor displacement in the common center. A nontrivial
cube-one quaternion automorphism has no noncentral fixed coset modulo the
center, so b and c are central in their factors. Their product lies in the
center of Vstar, identified with the terminal vertex center by the supplied
center equality. The existence of an actual order-three residual actor is
re-exported and included in the principal conclusion for the parent assembly.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48, literal
fixed-point-free action paragraph. The proof retains the original ambient
context and uses only proved lower-layer quaternion, Sylow, core, and finite
automorphism-group results.
-/

namespace Stellmacher.SectionNine
universe u
open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven

private theorem actor_not_centralizes_factor
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hlocal : DistanceOneLocalConclusion ctx)
    (left right : Subgroup G)
    (hleft : Nonempty (left ≃* QuaternionGroup 2))
    (hright : Nonempty (right ≃* QuaternionGroup 2))
    (hjoin : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') = left ⊔ right)
    (hinter : Nat.card (left ⊓ right : Subgroup G) = 2)
    (hcomm : ∀ b ∈ left, ∀ c ∈ right, b * c = c * b)
    (swap : G) (hswap : swap ∈ GAt ctx.Γ ctx.criticalPath.a')
    (hswapL : left.map (MulAut.conj swap).toMonoidHom = right)
    (hswapR : right.map (MulAut.conj swap).toMonoidHom = left)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.a')
    (horder : orderOf actor = 3) :
    ¬ (∀ l ∈ left, Commute actor l) := by
  classical
  intro hfixLeft
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  change V = left ⊔ right at hjoin
  have hn := (distance_one_vstar_containments ctx hlength).1
  have hnorm : terminal ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2
  let action : terminal →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  let M := action.range
  let actorB : terminal := ⟨actor, hactor⟩
  let swapB : terminal := ⟨swap, hswap⟩
  let x : M := ⟨action actorB, ⟨actorB, rfl⟩⟩
  let s : M := ⟨action swapB, ⟨swapB, rfl⟩⟩
  let y : M := s * x * s⁻¹
  have action_apply (p : terminal) (v : V) :
      (action p v : G) = (p : G) * (v : G) * (p : G)⁻¹ := rfl
  have y_apply (v : V) : ((y : MulAut V) v : G) =
      swap * (actor * (swap⁻¹ * (v : G) * swap) * actor⁻¹) * swap⁻¹ := by
    change (action swapB (action actorB ((action swapB)⁻¹ v)) : G) = _
    rw [← map_inv]
    simp only [action_apply]
    change swap * (actor * (swap⁻¹ * (v : G) * (swap⁻¹)⁻¹) * actor⁻¹) * swap⁻¹ = _
    rw [inv_inv]
  have hpow : actor ^ 3 = 1 := by rw [← horder]; exact pow_orderOf_eq_one actor
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    change (action actorB) ^ 3 = 1
    have hh : actorB ^ 3 = 1 := Subtype.ext hpow
    rw [← map_pow, hh, map_one]
  have hy3 : y ^ 3 = 1 := by
    change (MulAut.conj s x) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have h9 : ¬ 9 ∣ Nat.card M := by
    intro hd
    have hm := Subgroup.card_range_dvd action
    rw [distance_one_terminal_card ctx hlength hlocal] at hm
    exact (by decide : ¬ 9 ∣ (384 : ℕ)) (dvd_trans hd hm)
  have hL : left ≤ V := by rw [hjoin]; exact le_sup_left
  have hR : right ≤ V := by rw [hjoin]; exact le_sup_right
  let L := left.subgroupOf V
  let R := right.subgroupOf V
  have hgen : L ⊔ R = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hL hR, ← hjoin, Subgroup.subgroupOf_self]
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm hactor)
  rw [hjoin] at hmap
  have hcube : ∀ v : G, (MulAut.conj actor) ((MulAut.conj actor) ((MulAut.conj actor) v)) = v := by
    intro v
    have hc : (MulAut.conj actor) ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
    have hv := congrArg (fun e : MulAut G => e v) hc
    simpa [pow_succ] using hv
  have hpres := Subgroup.quaternion_factors_invariant_of_cube_eq_one left right hleft hright
    hinter hcomm (MulAut.conj actor) hmap hcube
  have hgRight : actor ∈ Subgroup.normalizer (right : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hpres.2
  have hxL : ∀ v ∈ L, (x : MulAut V) v = v := by
    intro v hv
    apply Subtype.ext
    change actor * (v : G) * actor⁻¹ = (v : G)
    rw [(hfixLeft v hv).eq, mul_inv_cancel_right]
  have hyR : ∀ v ∈ R, (y : MulAut V) v = v := by
    intro v hv
    have hvm : (v : G) ∈ left.map (MulAut.conj swap).toMonoidHom := hswapL.symm ▸ hv
    obtain ⟨l, hl, heq⟩ := hvm
    change swap * l * swap⁻¹ = (v : G) at heq
    have hback : swap⁻¹ * (v : G) * swap = l := by rw [← heq]; group
    apply Subtype.ext
    rw [y_apply, hback, (hfixLeft l hl).eq, mul_inv_cancel_right]
    exact heq
  have hxR : ∀ v ∈ R, (x : MulAut V) v ∈ R := by
    intro v hv
    exact (Subgroup.mem_normalizer_iff.mp hgRight v).mp hv
  have hyL : ∀ v ∈ L, (y : MulAut V) v ∈ L := by
    intro v hv
    have hvm : (v : G) ∈ right.map (MulAut.conj swap).toMonoidHom := hswapR.symm ▸ hv
    obtain ⟨r, hr, heq⟩ := hvm
    change swap * r * swap⁻¹ = (v : G) at heq
    have hback : swap⁻¹ * (v : G) * swap ∈ right := by
      rw [← heq]
      simpa [mul_assoc] using hr
    have hinner := (Subgroup.mem_normalizer_iff.mp hgRight _).mp hback
    have hforward := Subgroup.mem_map_of_mem (MulAut.conj swap).toMonoidHom hinner
    rw [hswapR] at hforward
    change ((y : MulAut V) v : G) ∈ left
    rw [y_apply]
    exact hforward
  have hc := MulAut.eq_one_or_eq_one_of_disjoint_cubic_actions M L R hgen x y
    hx3 hy3 h9 hxL hyR hxR hyL
  have hxone : x = 1 := by
    rcases hc with hc | hc
    · exact hc
    · apply (MulAut.conj s).injective
      simpa [y, MulAut.conj_apply] using hc
  obtain ⟨v, hv, hnc⟩ := distance_one_terminal_order_three_moves_vstar ctx hlength hlocal
    actor hactor horder
  have heq := congrArg (fun a : M => ((a : MulAut V) ⟨v, hv⟩ : G)) hxone
  change actor * v * actor⁻¹ = v at heq
  exact hnc (mul_inv_eq_iff_eq_mul.mp heq)


private theorem fixed_product_factor_central
    {G : Type*} [Group G] (B C : Subgroup G)
    (model : B ≃* QuaternionGroup 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (actor : G) (hpow : actor ^ 3 = 1)
    (hBn : actor ∈ Subgroup.normalizer (B : Set G))
    (hCn : actor ∈ Subgroup.normalizer (C : Set G))
    (hnot : ¬ ∀ b ∈ B, Commute actor b)
    (b c : G) (hb : b ∈ B) (hc : c ∈ C) (hfixed : Commute actor (b * c)) :
    (⟨b, hb⟩ : B) ∈ Subgroup.center B := by
  let e : MulAut B := B.normalizerMonoidHom ⟨actor, hBn⟩
  have hthree : e ^ 3 = 1 := by
    have hh : (⟨actor, hBn⟩ : Subgroup.normalizer (B : Set G)) ^ 3 = 1 := Subtype.ext hpow
    change (B.normalizerMonoidHom ⟨actor, hBn⟩) ^ 3 = 1
    rw [← map_pow, hh, map_one]
  have hne : e ≠ 1 := by
    intro he
    apply hnot
    intro x hx
    have hh := congrArg (fun f : MulAut B => (f ⟨x, hx⟩ : G)) he
    change actor * x * actor⁻¹ = x at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hproduct : (actor * b * actor⁻¹) * (actor * c * actor⁻¹) = b * c := by
    calc
      _ = actor * (b * c) * actor⁻¹ := by group
      _ = b * c := by rw [hfixed.eq, mul_inv_cancel_right]
  have heq : b⁻¹ * (actor * b * actor⁻¹) = c * (actor * c * actor⁻¹)⁻¹ := by
    have hh := congrArg (fun value : G => b⁻¹ * value * (actor * c * actor⁻¹)⁻¹) hproduct
    simpa [mul_assoc] using hh
  have hdiff : b⁻¹ * (actor * b * actor⁻¹) ∈ C := by
    rw [heq]
    exact C.mul_mem hc (C.inv_mem ((Subgroup.mem_normalizer_iff.mp hCn c).mp hc))
  have hcentral : (⟨b, hb⟩ : B)⁻¹ * e ⟨b, hb⟩ ∈ Subgroup.center B := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hcomm y y.property _ hdiff
  exact QuaternionGroup.mem_center_of_central_difference_of_cube_eq_one_ne_one_of_equiv
    model e hthree hne hcentral

private theorem fixed_product_mem_center
    {G : Type*} [Group G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (actor : G) (hpow : actor ^ 3 = 1)
    (hBn : actor ∈ Subgroup.normalizer (B : Set G))
    (hCn : actor ∈ Subgroup.normalizer (C : Set G))
    (hnotB : ¬ ∀ b ∈ B, Commute actor b) (hnotC : ¬ ∀ c ∈ C, Commute actor c)
    (element : G) (helement : element ∈ B ⊔ C) (hfixed : Commute actor element) :
    element ∈ CenterAmbient (B ⊔ C) := by
  obtain ⟨modelB⟩ := hB
  obtain ⟨modelC⟩ := hC
  have hnorm : B ≤ Subgroup.normalizer (C : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hprod : element ∈ (↑(B ⊔ C) : Set G) := helement
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B C hnorm] at hprod
  obtain ⟨b, hb, c, hc, hbc⟩ := hprod
  change b * c = element at hbc
  have hbcenter := fixed_product_factor_central B C modelB hcomm actor hpow hBn hCn hnotB
    b c hb hc (by rw [hbc]; exact hfixed)
  have hcb : c * b = element := (hcomm b hb c hc).symm.trans hbc
  have hccenter := fixed_product_factor_central C B modelC
    (fun c hc b hb => (hcomm b hb c hc).symm) actor hpow hCn hBn hnotC
    c b hc hb (by rw [hcb]; exact hfixed)
  have hbcent : b ∈ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hx | hx
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hbcenter ⟨x, hx⟩)
    · exact (hcomm b hb x hx).symm
  have hccent : c ∈ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hx | hx
    · exact hcomm x hx c hc
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hccenter ⟨x, hx⟩)
  have hecent : element ∈ Subgroup.centralizer ((B ⊔ C : Subgroup G) : Set G) := by
    rw [← hbc]
    exact (Subgroup.centralizer _).mul_mem hbcent hccent
  refine ⟨⟨element, helement⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hecent other other.property)


public theorem distance_one_vstar_residual_centralizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (hcenter : CenterAmbient (conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')) = ZAt ctx.Γ ctx.criticalPath.a') :
    (∃ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' ∧ orderOf actor = 3) ∧
      ∀ actor : G, actor ∈ EAt ctx.Γ ctx.criticalPath.a' → orderOf actor = 3 →
        ∀ element : G, element ∈ conjugateClosure
          (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
          (GAt ctx.Γ ctx.criticalPath.a') → Commute actor element →
            element ∈ ZAt ctx.Γ ctx.criticalPath.a' := by
  refine ⟨distance_one_terminal_residual_order_three ctx.toLocalContext hlocal, ?_⟩
  obtain ⟨left, right, hleft, hright, hjoin, hinter, hcomm, swap, _, hswap, hswapL, hswapR⟩ :=
    distance_one_vstar_factor_swap ctx.toLocalContext hlength hfaithful hlocal
  intro actor hactorE horder element helement hfixed
  have hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.a' := by
    apply SevenSix.twoResidualIn_le (GAt ctx.Γ ctx.criticalPath.a')
    simpa only [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using hactorE
  have hnotL := actor_not_centralizes_factor ctx.toLocalContext hlength hlocal
    left right hleft hright hjoin hinter hcomm swap hswap hswapL hswapR actor hactor horder
  have hnotR := actor_not_centralizes_factor ctx.toLocalContext hlength hlocal
    right left hright hleft (hjoin.trans (sup_comm left right))
    (by simpa [inf_comm] using hinter)
    (fun c hc b hb => (hcomm b hb c hc).symm)
    swap hswap hswapR hswapL actor hactor horder
  have hn := (distance_one_vstar_containments ctx.toLocalContext hlength).1
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hn.1).mp hn.2 hactor
  have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
  rw [hjoin] at hmap
  have hpow : actor ^ 3 = 1 := by rw [← horder]; exact pow_orderOf_eq_one actor
  have hcube : ∀ v : G, (MulAut.conj actor) ((MulAut.conj actor) ((MulAut.conj actor) v)) = v := by
    intro v
    have hc : (MulAut.conj actor) ^ 3 = 1 := by rw [← map_pow, hpow, map_one]
    have hv := congrArg (fun e : MulAut G => e v) hc
    simpa [pow_succ] using hv
  have hpres := Subgroup.quaternion_factors_invariant_of_cube_eq_one left right hleft hright
    hinter hcomm (MulAut.conj actor) hmap hcube
  have hjoin' : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') = left ⊔ right := hjoin
  rw [← hcenter, hjoin']
  exact fixed_product_mem_center left right hleft hright hcomm actor hpow
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hpres.1)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hpres.2)
    hnotL hnotR element (hjoin' ▸ helement) hfixed

end Stellmacher.SectionNine
