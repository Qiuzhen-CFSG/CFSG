module
public import Stellmacher.SectionNine.DistanceOneTerminalEightCentralizer
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24

/-!
# The terminal normalizer quotient of the selected elementary eight

The explicit distance-one subgroup selection properties imply that the
terminal normalizer of U modulo U is S4, and that U is self-centralizing
in the entire terminal stabilizer. The original ambient context and actual
Vstar, two-residual, core, and vertex centers remain unchanged.

The lower centralizer leaf proves that the terminal normalizer has order192
and its conjugation kernel on U is exactly U of order8. Thus the actual
conjugation image has order24. The terminal center has order2 and lies in
U; its unique nonidentity element is fixed by the terminal stabilizer because
that center is terminal-normal. The generic elementary-eight fixed-point
recognition theorem identifies this automorphism image with S4. Composing
the range-restricted conjugation map with that isomorphism gives the required
surjective homomorphism with exactly the prescribed kernel.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48, terminal local
normalizer. The source-specific subgroup selection is explicit and has
independent producers; no normalizer model is assumed.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven
universe u

/-- The selected elementary eight has terminal normalizer quotient S4 and
is self-centralizing in the terminal stabilizer. -/
public theorem distance_one_terminal_eight_normalizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (U : Subgroup G) (hElem : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 8)
    (hUV : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a'))
    (hZdU : ZAt ctx.Γ ctx.criticalPath.a' ≤ U)
    (hUE : NormalIn U (EAt ctx.Γ ctx.criticalPath.a'))
    (hZaN : ZAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (U : Set G))
    (hQnot : ¬ QAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (U : Set G))
    (hself : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ⊓ Subgroup.centralizer (U : Set G) = U) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G)) U
      (Equiv.Perm (Fin 4)) ∧
      GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer (U : Set G) = U := by
  classical
  let := hElem
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let N := terminal ⊓ Subgroup.normalizer (U : Set G)
  obtain ⟨hNcard, hcentral⟩ := distance_one_terminal_eight_order_and_centralizer
    ctx hlength hfaithful hlocal U hElem hUcard hUV hUE hZaN hQnot hself
  have hUT : U ≤ terminal :=
    hUV.trans (distance_one_vstar_containments ctx.toLocalContext hlength).1.1
  have hUN : U ≤ N := le_inf hUT U.le_normalizer
  let action : N →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  have hker : action.ker = U.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      apply hcentral.le
      refine ⟨x.property.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      have hh := congrArg (fun f : MulAut U => (f ⟨u, hu⟩ : G)) hx
      change (x : G) * u * (x : G)⁻¹ = u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change (x : G) * (u : G) * (x : G)⁻¹ = (u : G)
      have hcomm : (x : G) * (u : G) = (u : G) * (x : G) :=
        setLike_mul_comm (s := U) (show (x : G) ∈ U from hx) u.property
      rw [hcomm, mul_inv_cancel_right]
  have hKcard : Nat.card action.ker = 8 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv, hUcard]
  have hAcard : Nat.card action.range = 24 := by
    have hh := action.ker.card_mul_index
    rw [hKcard, Subgroup.index_ker, hNcard] at hh
    omega
  have hZdcard := (distance_one_vstar_center ctx hlength hfaithful hlocal).2
  let Zd := ZAt ctx.Γ ctx.criticalPath.a'
  have hZdT : Zd ≤ terminal := hZdU.trans hUT
  let Zdt := Zd.subgroupOf terminal
  let : Zdt.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZdT).mpr
    (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a')
  have hZdtcard : Nat.card Zdt = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZdT).toEquiv).trans hZdcard
  have hZdcentral : Zdt ≤ Subgroup.center terminal :=
    Subgroup.central_of_normal_card_two Zdt hZdtcard
  obtain ⟨z, hzne, _⟩ := (Nat.card_eq_two_iff' (1 : Zd)).mp hZdcard
  let zu : U := ⟨z, hZdU z.property⟩
  have hzune : zu ≠ 1 := by
    intro hh
    apply hzne
    have hzG : (z : G) = 1 := congrArg (fun q : U => (q : G)) hh
    exact Subtype.ext hzG
  have hfix : ∀ a : action.range, (a : MulAut U) zu = zu := by
    rintro ⟨a, x, rfl⟩
    apply Subtype.ext
    change (x : G) * (z : G) * (x : G)⁻¹ = (z : G)
    have hh := congrArg Subtype.val (Subgroup.mem_center_iff.mp
      (hZdcentral (show (⟨z, hZdT z.property⟩ : terminal) ∈ Zdt from z.property))
      (⟨x, x.property.1⟩ : terminal))
    change (x : G) * (z : G) = (z : G) * (x : G) at hh
    rw [hh, mul_inv_cancel_right]
  obtain ⟨model⟩ := elementaryEight_fixed_point_order24_equiv_S4 hUcard zu hzune action.range hAcard hfix
  refine ⟨⟨model.toMonoidHom.comp action.rangeRestrict,
    model.surjective.comp action.rangeRestrict_surjective, ?_⟩, hcentral⟩
  ext x
  change model (action.rangeRestrict x) = 1 ↔ x ∈ U.subgroupOf N
  rw [← hker, MonoidHom.mem_ker, ← model.map_one, model.injective.eq_iff]
  exact Subtype.ext_iff

end Stellmacher.SectionNine
