module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.CoverTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Contradiction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup

/-!
# Ambient scalar motion from the source wreath overgroup

The preceding sentence in the proof of Aschbacher–Smith 13.8.16(1)
constructs H₁/O₂(H₁) ≃ S₃ wr C₂ and identifies R = O²(H₁), inside M.
The simultaneous transposition in its two S₃ factors inverts the cubic
base. Lifting this element to H₁ gives an actual element of N_M(R).

The cover scalar has a lift in R: it acts trivially on the marked binary
module, hence lies in the image of N_L(V₁), and its odd order places it in
the image of that subgroup's two-residual. If the lifted inverter fixed
this scalar, the product of a lift and its conjugate would belong to
O₂(R), while its image in the cover would have order three. This is
impossible. No identification of cubic coordinates or of the two marked
lines is needed.

`normalizer_scalar_moves_of_source_pair` applies the completed
`WreathOvergroup.exists_source_wreath_overgroup` construction to the literal
R = O²(N_{LT}(V₁)). Thus H₁, its quotient equivalence and the residual
identity are proved, with the same earlier source inputs as that construction:
the moving PSL₃(2) data, H ≤ G₁, the solvable-overgroup exclusion 13.8.13,
and the theta identity 13.7.3(9). The final branch assembly supplies those
earlier outputs and the compatible triple-cover marking. No scalar motion,
outer-action image, or identity [R,T] = R is assumed. This route uses the
actual wreath construction, beyond its rank-two and order-nine consequences.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16(1), printed p.952 (PDF p.969); standing hypotheses pp.946–947;
Notation 13.2.1 and Lemma 13.2.2, pp.877–878. The preceding wreath
construction uses 13.7.3(9) to identify the actual residual.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.SourceScalarAction

private instance : Fintype WreathModel.W := Fintype.ofEquiv
  ((WreathModel.C2 → WreathModel.SL2) × WreathModel.C2)
  (RegularWreathProduct.equivProd WreathModel.SL2 WreathModel.C2).symm

private instance : DecidableEq WreathModel.W := fun a b => decidable_of_iff
  (a.left = b.left ∧ a.right = b.right) RegularWreathProduct.ext_iff.symm

private instance : DecidablePred (fun x : WreathModel.W => x ∈ WreathModel.cubicBase) := fun x =>
  inferInstanceAs (Decidable (x.right = 1 ∧ ∀ i, (x.left i)^3 = 1))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem wreath_inversion (x : WreathModel.cubicBase) :
    WreathModel.action (wreathTwoDihedralHom (DihedralGroup.r 2)) x = x⁻¹ := by
  revert x
  decide +kernel

variable {G : Type*} [Group G] [Finite G]

/-- The scalar already lies in the actual marked residual image. -/
theorem scalar_mem_markedResidual_image (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hV₁V : V₁ ≤ V) (hRL : markedResidual L T V₁ ≤ L) :
    Atlas.Codes.hexEvenZ ∈ (d.subgroupMap (markedResidual L T V₁) hRL).range := by
  let P := L ⊓ normalizer (V₁ : Set G)
  let f : P →* Model.Cover := d.subgroupMap P inf_le_left
  obtain ⟨l, hl⟩ := d.quotientEquiv.surjective Atlas.Codes.hexEvenZ
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) l
  have hz : Atlas.Codes.hexEvenCoordinate Atlas.Codes.hexEvenZ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [Atlas.Codes.hexEvenCoordinate_kernel]
    exact mem_zpowers _
  have hfix (v : V) : V.normalizerMonoidHom (inclusion hLV l) v = v := by
    apply d.moduleEquiv.injective
    change Multiplicative.toAdd (d.moduleEquiv _) = Multiplicative.toAdd (d.moduleEquiv v)
    rw [d.equivariant, hl, hz]
    exact polarAction_one _
  have hn : (l : G) ∈ normalizer (V₁ : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    apply mem_centralizer_iff.mpr
    intro v hv
    have he := congrArg Subtype.val (hfix (inclusion hV₁V ⟨v, hv⟩))
    change (l : G) * v * (l : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hmem : Atlas.Codes.hexEvenZ ∈ f.range := ⟨⟨l, l.property, hn⟩, hl⟩
  let z : f.range := ⟨Atlas.Codes.hexEvenZ, hmem⟩
  have ho : orderOf z = 3 := (orderOf_coe z).symm.trans Atlas.Codes.hexEvenZ_order
  have hr : z ∈ pResidual 2 f.range :=
    mem_pResidual_of_orderOf_coprime (by rw [ho]; decide)
  rw [← map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective] at hr
  obtain ⟨r, hr, he⟩ := hr
  have hP : P ≤ markedParabolic L T V₁ := le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hr' : inclusion hP r ∈ pResidual 2 (markedParabolic L T V₁) :=
    map_pResidual_le 2 (inclusion hP) ⟨r, hr, rfl⟩
  refine ⟨⟨r, ⟨inclusion hP r, hr', rfl⟩⟩, ?_⟩
  exact congrArg Subtype.val he

/-- The simultaneous cubic inverter lifts to the actual overgroup. -/
private theorem exists_inverter (R H₁ : Subgroup G)
    (hres : R = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) :
    ∃ h : H₁, ∀ r : R ⧸ pCore 2 R,
      quotientAction R H₁ (normalizes_embedded_residual R H₁ hres) h r = r⁻¹ := by
  obtain ⟨q, hq⟩ := e.surjective (wreathTwoDihedralHom (DihedralGroup.r 2))
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H₁) q
  refine ⟨h, fun r => ?_⟩
  let c := markedQuotientEquiv R H₁ hres
  have hi : ResidualAction.action h (c.symm r) = (c.symm r)⁻¹ := by
    apply (ResidualAction.residualQuotientEquiv e).injective
    rw [ResidualAction.intertwines, hq, wreath_inversion, map_inv]
  have hi' := congrArg c hi
  rw [marked_intertwines, MulEquiv.apply_symm_apply, map_inv,
    MulEquiv.apply_symm_apply] at hi'
  exact hi'

/-- An actual residual inverter cannot fix a scalar of order three. -/
theorem scalar_moves_of_wreath_overgroup (L T V V₁ H₁ M : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hV₁V : V₁ ≤ V) (hRL : markedResidual L T V₁ ≤ L)
    (hHM : H₁ ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hres : markedResidual L T V₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) :
    ∃ m : (M ⊓ normalizer (markedResidual L T V₁ : Set G) : Subgroup G),
      coverAction d M hML (inclusion inf_le_left m) Atlas.Codes.hexEvenZ ≠
        Atlas.Codes.hexEvenZ := by
  let R := markedResidual L T V₁
  let f := d.subgroupMap R hRL
  obtain ⟨r, hr⟩ := scalar_mem_markedResidual_image L T V V₁ hLV d hV₁V hRL
  obtain ⟨h, hh⟩ := exists_inverter R H₁ hres e
  have hn := normalizes_embedded_residual R H₁ hres
  let m : (M ⊓ normalizer (R : Set G) : Subgroup G) := inclusion (le_inf hHM hn) h
  refine ⟨m, ?_⟩
  intro hfix
  let r' : R := R.normalizerMonoidHom (inclusion hn h) r
  have hp : r' * r ∈ pCore 2 R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 R) (r' * r) = 1
    rw [map_mul]
    have he := hh (QuotientGroup.mk' (pCore 2 R) r)
    rw [quotientAction_mk] at he
    change QuotientGroup.mk' (pCore 2 R) r' = _ at he
    rw [he, inv_mul_cancel]
  have he : f (r' * r) = Atlas.Codes.hexEvenZ ^ 2 := by
    rw [map_mul]
    change d.subgroupMap R hRL (R.normalizerMonoidHom (inclusion inf_le_right m) r) * f r = _
    rw [d.subgroupMap_conjugation R M hRL hML m r]
    change coverAction d M hML (inclusion inf_le_left m) (f r) * f r = _
    rw [show f r = Atlas.Codes.hexEvenZ from hr, hfix, pow_two]
  have hg : IsPGroup 2 ((pCore 2 R).map f) := pCore_isPGroup.map f
  let c : (pCore 2 R).map f := ⟨f (r' * r), mem_map_of_mem f hp⟩
  have ho : orderOf c = 3 := by
    rw [← orderOf_coe]
    change orderOf (f (r' * r)) = 3
    rw [he, orderOf_pow, Atlas.Codes.hexEvenZ_order]
    decide
  have hc := hg.orderOf_coprime (by decide : Nat.Coprime 2 3) c
  rw [ho] at hc
  norm_num at hc

/-- With the preceding source wreath construction supplied, the genuine
Sylow arrangement gives a moving element in N_M(R), for M = N_G(L) and
R = O²(N_{LT}(V₁)). The subgroup witness retains literal conjugation. -/
theorem normalizer_scalar_moves_of_source_wreath
    (L V V₁ H₁ : Subgroup G) (T : Sylow 2 G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (hV₁V : V₁ ≤ V)
    (hHM : H₁ ≤ normalizer (L : Set G))
    (hres : markedResidual L T V₁ = (pResidual 2 H₁).map H₁.subtype)
    (e : H₁ ⧸ pCore 2 H₁ ≃* WreathModel.W) :
    ∃ m : (normalizer (L : Set G) ⊓
        normalizer (markedResidual L T V₁ : Set G) : Subgroup G),
      coverAction d (normalizer (L : Set G)) le_rfl
        (inclusion inf_le_left m) Atlas.Codes.hexEvenZ ≠ Atlas.Codes.hexEvenZ :=
  scalar_moves_of_wreath_overgroup L T V V₁ H₁ (normalizer (L : Set G)) hLV d
    hV₁V (markedResidual_le_left L T V₁ T.isPGroup' hTL) hHM le_rfl hres e

/-- Actual scalar motion in the moving PSL₃(2) source branch of 13.8.16(1).
The component and earlier-source data are precisely those of the preceding
wreath construction, specialized to the literal marked residual and Sylow T.
Here `hex` is 13.8.13 and `htheta` is 13.7.3(9), with M = N_G(L).

The constructed H₁ discharges all three extra premises of
`normalizer_scalar_moves_of_source_wreath`: containment in M, its wreath
quotient, and the ambient residual identity. The witness is in N_M(R),
and `coverAction` is the transport of literal conjugation on L/O₂(L). -/
theorem normalizer_scalar_moves_of_source_pair
    (L V V₁ H G₁ K K₀ : Subgroup G) (T : Sylow 2 G)
    (hLV : L ≤ normalizer (V : Set G)) (d : CoverPointModel L V hLV)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (hV₁V : V₁ ≤ V)
    (s : WreathOvergroup.SourcePair.Input H (markedResidual L T V₁) T K K₀)
    (hH : H ≤ G₁)
    (hex : ∀ J : Subgroup G, markedResidual L T V₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ normalizer (L : Set G))
    (htheta : markedResidual L T V₁ =
      closure {x : G | x ∈ H ⊓ normalizer (L : Set G) ∧ orderOf x = 3}) :
    ∃ m : (normalizer (L : Set G) ⊓
        normalizer (markedResidual L T V₁ : Set G) : Subgroup G),
      coverAction d (normalizer (L : Set G)) le_rfl
        (inclusion inf_le_left m) Atlas.Codes.hexEvenZ ≠ Atlas.Codes.hexEvenZ := by
  obtain ⟨H₁, _, hHM, _, ⟨e⟩, _, hres, _⟩ :=
    WreathOvergroup.exists_source_wreath_overgroup s G₁
      (normalizer (L : Set G)) hH hex htheta
  exact normalizer_scalar_moves_of_source_wreath L V V₁ H₁ T hLV d hTL hV₁V
    (hHM.trans inf_le_right) hres e

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.SourceScalarAction

end
