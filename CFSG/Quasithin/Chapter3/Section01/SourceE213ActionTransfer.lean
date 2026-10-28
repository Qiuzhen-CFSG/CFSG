module
public import CFSG.Quasithin.Chapter3.Section01.SourceE213CoreInput
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.WeakAction
/-!
# Transfer of the intrinsic E.2.13 bound to the original qrc action

The same Sylow subgroup acts on the intrinsic module in H and on the original
module in M₀. Its centralizer quotient embeds in the conjugation image of M₀,
and the subgroup-of equivalence intertwines their binary representations.
Consequently every intrinsic cubic-ratio estimate transfers to the original
image without a TI or maximal-normalization hypothesis.

Source: Aschbacher--Smith 3.1.6, printed p.574, immediately after E.2.13.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

omit [Finite G] in
theorem QrcHypotheses.intrinsic_module_normalized
    (h : QrcHypotheses T M M₀ H V) :
    ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤
      normalizer (V.subgroupOf H : Set H) := by
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  rw [← subgroupOf_normalizer_eq hVH]
  exact fun _ hx => h.module_normalized (h.sylow_le hx)

theorem QrcHypotheses.cubicRatio_le_nat_of_intrinsic_action
    (h : QrcHypotheses T M M₀ H V) (n : ℕ) :
    letI := h.module_elementary
    letI : IsElementaryAbelian 2 (V.subgroupOf H) :=
      IsElementaryAbelian.subgroupOf (h.module_le_sylow.trans h.right_mem.1.1.2)
    cubicRatio (ChapterE.DihedralCubic.canonicalAction
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)
      (V.subgroupOf H) h.intrinsic_module_normalized) ≤ n →
      cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ n := by
  let := h.module_elementary
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let hTV := h.intrinsic_module_normalized
  let σ := imageRepresentation M₀ V h.module_normalized
  intro hbound
  let := ChapterE.DihedralCubic.centralizer_normal (S : Subgroup H) W hTV
  let ρ := ChapterE.DihedralCubic.canonicalAction (S : Subgroup H) W hTV
  let q := ChapterE.DihedralCubic.projection (S : Subgroup H) W hTV
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  let i : (S : Subgroup H) →* M₀ :=
    (H.subtype.comp (S : Subgroup H).subtype).codRestrict M₀ (fun s => h.sylow_le s.property)
  let f := (actionHom M₀ V h.module_normalized).rangeRestrict.comp i
  have hk : q.ker ≤ f.ker := by
    intro s hs
    have hsC : s ∈ (centralizer (W : Set H)).subgroupOf (S : Subgroup H) :=
      (QuotientGroup.eq_one_iff s).mp hs
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have hc := congrArg H.subtype (hsC ⟨v,hVH v.property⟩ v.property)
    change (v : G) * (s.val : G) = (s.val : G) * (v : G) at hc
    change (s.val : G) * (v : G) * (s.val : G)⁻¹ = v
    rw [←hc,mul_inv_cancel_right]
  let ψ := q.liftOfSurjective hqs ⟨f,hk⟩
  have hψ (s : (S : Subgroup H)) : ψ (q s) = f s := q.liftOfRightInverse_comp_apply _ _ _ s
  let e := subgroupOfEquivOfLe hVH
  let E : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  have he : ∀ a v, E (ρ a v) = σ (ψ a) (E v) := by
    intro a v
    obtain ⟨s,rfl⟩ := hqs a
    rw [hψ]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg H.subtype
      (ChapterE.DihedralCubic.representation_apply (S : Subgroup H) W hTV q hqs
        (QuotientGroup.ker_mk' _) s v)
  have hψi : Function.Injective ψ := by
    intro a b hab
    apply ChapterE.DihedralCubic.representation_injective (S : Subgroup H) W hTV q hqs
      (QuotientGroup.ker_mk' _)
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (ρ a v) = E (ρ b v)
    exact (he a v).trans ((congrArg (fun z => σ z (E v)) hab).trans (he b v).symm)
  exact cubicRatio_le_nat_of_equivariant ρ σ ψ hψi E he n hbound
end CFSG.Quasithin.Chapter3
