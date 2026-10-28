module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Setup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Rank
public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.GroupAction.PerfectCentralQuotient


/-!
# The ordinary component in the central-quotient fixed subgroup

A central quotient need not map a fixed subgroup onto the fixed subgroup
downstairs. Its image is nevertheless normal: a lift of a fixed element has
central displacement, so conjugation by the lift preserves fixed points.
The original ordinary component therefore has subnormal image. Its embedding
is faithful by `Setup`, retaining its actual PSL₃(2) isomorphism.

The induced automorphism has order two. A trivial action upstairs would make
the original component all of K, contradicting rank two and |PSL₃(2)| = 168.
Faithfulness of the action on a perfect group's central quotient excludes
triviality downstairs. These reductions preserve v outside K and do not
replace an ordinary component by a mere section of a centralizer.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed p.1137, in the application of Theorem C (p.33). No model sieve is
asserted here.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

private theorem fixed_map_range_normal {X Y : Type*} [Group X] [Group Y]
    (a : MulAut X) (b : MulAut Y) (f : X →* Y) (hf : Function.Surjective f)
    (hc : f.ker ≤ center X) (heq : ∀ x, f (a x) = b (f x)) :
    (MulAut.fixedSubgroupMap a b f heq).range.Normal := by
  let g := MulAut.fixedSubgroupMap a b f heq
  refine ⟨?_⟩
  intro z hz y
  obtain ⟨k, rfl⟩ := hz
  obtain ⟨x, hx⟩ := hf (y : Y)
  have hxc : a x * x⁻¹ ∈ center X := by
    apply hc
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, hx,
      (MulAut.mem_fixedSubgroup _ _).mp y.property, mul_inv_cancel]
  have hk : a (x * (k : X) * x⁻¹) = x * (k : X) * x⁻¹ := by
    rw [map_mul, map_mul, map_inv, (MulAut.mem_fixedSubgroup _ _).mp k.property]
    calc
      _ = (a x * x⁻¹) * (x * (k : X) * x⁻¹) * (a x * x⁻¹)⁻¹ := by group
      _ = _ := by
        rw [← mem_center_iff.mp hxc (x * (k : X) * x⁻¹)]
        group
  refine ⟨⟨x * (k : X) * x⁻¹, (MulAut.mem_fixedSubgroup _ _).mpr hk⟩, ?_⟩
  apply Subtype.ext
  change f (x * (k : X) * x⁻¹) = (y : Y) * f k * (y : Y)⁻¹
  rw [map_mul, map_mul, map_inv, hx]

universe u
variable {G : Type u} [Group G] {H K : Subgroup G} {v : G} (d : Input H K v)
include d

/-- The involution acts nontrivially on K. Otherwise its centralizer is K,
whose only ordinary component is K itself. Its identification with PSL₃(2)
would contradict the elementary subgroup of order nine supplied by rank two. -/
theorem Input.involutionAction_ne_one [Finite G] : d.involutionAction ≠ 1 := by
  intro ha
  have hc : K ⊓ centralizer ({v} : Set G) = K := by
    apply le_antisymm inf_le_left
    intro x hx
    refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := congrArg (fun a : MulAut K => (a ⟨x, hx⟩ : G)) ha
    change v * x * v⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let e := MulEquiv.subgroupCongr hc
  let : IsQuasisimple K := d.quasisimple
  let : IsQuasisimple (⊤ : Subgroup K) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have htop : IsComponent K ⊤ := ⟨IsSubnormal.top, inferInstance⟩
  have hD := d.centralizerComponent_isComponent.map_equiv e
  have hEq := hD.eq_of_le htop le_top
  let eK : d.centralizerComponent ≃* K :=
    (d.centralizerComponent.equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hEq).trans topEquiv)
  have hcard : Nat.card K = 168 :=
    (Nat.card_congr (eK.symm.trans d.centralizerComponent_equiv).toEquiv).trans
      Matrix.PSL3Two.card_PSL
  obtain ⟨E, _, hE⟩ := CoverReduction.LocalCover.exists_elementary_nine d.rank.ge
  have hd := E.card_subgroup_dvd_card
  rw [hE, hcard] at hd
  norm_num at hd

/-- The genuine induced automorphism of the full central quotient. -/
@[expose] def Input.centralQuotientInvolutionAction : MulAut (K ⧸ center K) :=
  quotientAut (center K) d.involutionAction

/-- The induced central-quotient action has square one. -/
theorem Input.centralQuotientInvolutionAction_sq :
    d.centralQuotientInvolutionAction ^ 2 = 1 := by
  exact (map_pow (quotientAut (center K)) _ 2).symm.trans
    (by rw [d.involutionAction_sq, map_one])

/-- Perfectness detects trivial automorphisms on the central quotient,
so the nontrivial involution action remains nontrivial there. -/
theorem Input.centralQuotientInvolutionAction_ne_one [Finite G] :
    d.centralQuotientInvolutionAction ≠ 1 := by
  let : IsQuasisimple K := d.quasisimple
  intro he
  apply d.involutionAction_ne_one
  apply MulAut.quotient_center_injective
  exact he.trans (map_one (quotientAut (center K))).symm

/-- The induced automorphism is an involution, not the identity. -/
theorem Input.centralQuotientInvolutionAction_order [Finite G] :
    orderOf d.centralQuotientInvolutionAction = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one d.centralQuotientInvolutionAction_sq) with h | h
  · exact (d.centralQuotientInvolutionAction_ne_one (orderOf_eq_one_iff.mp h)).elim
  · exact h

/-- The given ordinary PSL₃(2) component survives in the fixed subgroup of
the actual central-quotient involution. The fixed map need not be onto:
normality of its range suffices to transport subnormality. -/
theorem Input.exists_centralQuotient_fixed_component :
    ∃ D : Subgroup d.centralQuotientInvolutionAction.fixedSubgroup,
      IsComponent d.centralQuotientInvolutionAction.fixedSubgroup D ∧
      Nonempty (D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let q := QuotientGroup.mk' (center K)
  have heq (x : K) : q (d.involutionAction x) =
      d.centralQuotientInvolutionAction (q x) := (quotientAut_apply_mk _ _ _).symm
  let f := MulAut.fixedSubgroupMap d.involutionAction d.centralQuotientInvolutionAction q heq
  have hn : f.range.Normal := fixed_map_range_normal _ _ q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) heq
  let g := f.comp d.centralizerEquivFixed.toMonoidHom
  have hg : g.range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      d.centralizerEquivFixed.surjective, ← MonoidHom.range_eq_map]
  have hgn : g.range.Normal := hg ▸ hn
  have hi : Function.Injective (g.subgroupMap d.centralizerComponent) := by
    intro x y hxy
    apply d.componentQuotientEmbedding_injective
    exact congrArg (fun z : d.centralizerComponent.map g =>
      ((z : d.centralQuotientInvolutionAction.fixedSubgroup) : K ⧸ center K)) hxy
  let e := MulEquiv.ofBijective (g.subgroupMap d.centralizerComponent)
    ⟨hi, g.subgroupMap_surjective _⟩
  have hsn : (d.centralizerComponent.map g).IsSubnormal := by
    have hs := (d.centralizerComponent_isComponent.1.map g.rangeRestrict_surjective).trans'
      hgn.isSubnormal
    simpa only [map_map, MonoidHom.subtype_comp_rangeRestrict] using hs
  let := d.centralizerComponent_isComponent.2
  exact ⟨d.centralizerComponent.map g, ⟨hsn, IsQuasisimple.of_mulEquiv e⟩,
    ⟨e.symm.trans d.centralizerComponent_equiv⟩⟩
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
