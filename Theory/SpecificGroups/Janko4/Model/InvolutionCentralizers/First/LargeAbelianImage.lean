module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ResidualCore
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.GroupTheory.PCoreCentralKernelTransfer
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Large abelian subgroups survive a first-centralizer quotient

A homomorphism killing the two-core and retaining the perfect residual
cannot kill an abelian two-subgroup of order greater than 256. Intersect
that subgroup with the index-two triple-cover preimage. Its image in the
quasisimple core quotient lies in a central kernel, so its binary image is
trivial. The extraspecial core bounds this intersection by 128.

For a quasisimple residual image, full core movement supplies the required
kernel containment. The Mathieu Hall application uses this to keep its
original rank-ten module nontrivial under the containing component action.
Source: Aschbacher--Smith 4.4.3, printed p.623; GLS3 Table 5.3i.
The imported native J₄ certificates retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.InvolutionCentralizers.First
open QuotientExtension
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- A nontrivial residual image prevents a large abelian two-subgroup from vanishing. -/
theorem large_abelian_image_ne_bot {Y : Type*} [Group Y]
    (f : centralizer →* Y) (hc : pCore 2 centralizer ≤ f.ker)
    (hr : (solvableResidual centralizer).map f ≠ ⊥)
    (E : Subgroup centralizer) [IsMulCommutative E] (hp : IsPGroup 2 E)
    (hE : 256 < Nat.card E) : E.map f ≠ ⊥ := by
  intro hzero
  have hPH : solvableResidual centralizer ≤ H := by
    let : Group.IsSolvable (centralizer ⧸ H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := centralizerQuotientEquivC2.toMonoidHom) centralizerQuotientEquivC2.injective
    exact solvableResidual_le_of_solvable_quotient H
  let g := f.comp H.subtype
  have hgn : g.range ≠ ⊥ := by
    intro he
    apply hr
    apply bot_unique
    calc
      (solvableResidual centralizer).map f ≤ H.map f := map_mono hPH
      _ = g.range := by rw [MonoidHom.range_comp,range_subtype]
      _ = ⊥ := he
  let : Nontrivial g.range := (nontrivial_iff_ne_bot _).mpr hgn
  have hcore : pCore 2 H = Q.subgroupOf H := pCore_eq_comap_of_normal 2 H
  let e : (H ⧸ pCore 2 H) ≃* Sporadic.Mathieu.M22TripleCover :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans HQuotientEquivCover
  let : IsQuasisimple (H ⧸ pCore 2 H) := IsQuasisimple.of_mulEquiv e.symm
  have hgc : pCore 2 H ≤ g.rangeRestrict.ker := by
    rw [hcore]
    intro x hx
    apply Subtype.ext
    exact hc hx
  have hk := g.rangeRestrict.map_ker_central_of_quasisimple_pCore
    g.rangeRestrict_surjective hgc
  let U := E.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hUk : U ≤ g.rangeRestrict.ker := by
    intro x hx
    apply Subtype.ext
    exact (map_eq_bot_iff E).mp hzero hx
  have hz : U.map q ≤ center (H ⧸ pCore 2 H) := (map_mono hUk).trans hk
  have hn : (U.map q).Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hz hn) g,mul_assoc,mul_inv_cancel,mul_one]
    exact hn⟩
  have hUc : U.map q ≤ pCore 2 (H ⧸ pCore 2 H) :=
    le_sSup ⟨hn,(hp.comap_subtype (K := H)).map q⟩
  rw [pCore_quotient_pCore_eq_bot] at hUc
  have hUQ : U ≤ Q.subgroupOf H := by
    rw [←hcore,←QuotientGroup.ker_mk' (pCore 2 H)]
    exact (map_eq_bot_iff U).mp (bot_unique hUc)
  let UQ := U.map H.subtype
  have hUQQ : UQ ≤ Q := by
    rintro _ ⟨u,hu,rfl⟩
    exact hUQ hu
  let W := UQ.subgroupOf Q
  have hUQE : UQ ≤ E := map_comap_le H.subtype E
  let : IsMulCommutative W := ⟨⟨fun x y => Subtype.ext (Subtype.ext
    (setLike_mul_comm (hUQE x.property) (hUQE y.property)))⟩⟩
  let := centralizer_twoCore_extraspecial
  have hW := extraspecial_prime_abelian_card_sq_le_any (p := 2) W
  have hWU : Nat.card W = Nat.card U := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUQQ).toEquiv]
    exact card_map_of_injective H.subtype_injective
  rw [hWU,centralizer_twoCore_card] at hW
  have hU128 : Nat.card U ≤ 128 := by nlinarith
  let r := (QuotientGroup.mk' H).comp E.subtype
  have hker : Nat.card r.ker = Nat.card U := by
    let er : r.ker ≃* U :=
      { toFun := fun x => ⟨⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩,x.val.property⟩
        invFun := fun x => ⟨⟨x.val.val,x.property⟩,(QuotientGroup.eq_one_iff _).mpr x.val.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact Nat.card_congr er.toEquiv
  have hrange : Nat.card r.range ≤ 2 := by
    have hh := r.range.card_le_card_group
    have hh' : Nat.card (centralizer ⧸ H) = 2 := by
      rw [Nat.card_congr centralizerQuotientEquivC2.toEquiv]
      simp
    exact hh.trans_eq hh'
  have hcount : Nat.card E = Nat.card r.ker * Nat.card r.range := by
    rw [←index_ker]
    exact r.ker.card_mul_index.symm
  rw [hker] at hcount
  nlinarith

/-- A quasisimple residual image supplies the full-core kernel condition. -/
theorem large_abelian_image_ne_bot_of_quasisimple_residual {Y : Type*} [Group Y]
    (f : centralizer →* Y)
    [IsQuasisimple ((solvableResidual centralizer).map f)]
    (E : Subgroup centralizer) [IsMulCommutative E] (hp : IsPGroup 2 E)
    (hE : 256 < Nat.card E) : E.map f ≠ ⊥ := by
  let P := solvableResidual centralizer
  have hc : pCore 2 centralizer ≤ f.ker := by
    have hk := residual_quasisimple_image_kills_twoCore (f.subgroupMap P)
      (f.subgroupMap_surjective P)
    intro x hx
    let u : P := ⟨x,twoCore_le_residual hx⟩
    have hu : u ∈ pCore 2 P := by
      rw [pCore_eq_comap_of_normal]
      exact hx
    exact congrArg Subtype.val (hk hu)
  let : IsSimpleGroup (P.map f ⧸ center (P.map f)) := IsQuasisimple.simple
  let : Nontrivial (P.map f) := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center (P.map f)))
  have hr : P.map f ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  exact large_abelian_image_ne_bot f hc hr E hp hE

end Janko4.InvolutionCentralizers.First
