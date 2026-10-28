module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction.FiveOuter.Geometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction.FiveOuter.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction.FiveOuter.Transport

/-!
# A genuinely outer actor in the L₅(2) Sylow embedding

The full transvection directions of the permuting Sylow pair give a
canonical proper subspace. In dimensions two and three its pointwise
fixer in the order-nine subgroup is proper and nontrivial. In dimensions
one and four, the action on the four-dimensional section has two-group
kernel and reduces to the proved L₄(2) calculation. Thus inner pair
actors preserve a proper subgroup of the complement, contradicting the
local irreducibility hypothesis.

We retain the actual component quotient, relative normality, and permuting
Sylow pair throughout. The resulting outer element gives the full
Aut(L₅(2)) quotient by the existing exact-kernel and inner/graph theorems.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
1.3.4, printed pp.509–511, and the proof of 15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup BinaryLinear BinaryLinear.OuterCyclic Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction
namespace FiveOuter

local instance : Finite Lin := Finite.of_equiv _ (matrixEquivLinear 5).toEquiv

/-- The inner normalizer of a permuting Sylow pair in GL₅(2) is reducible on R. -/
theorem invariant_subgroup (S : Sylow 2 Lin) (R : Subgroup Lin) (hR : Nat.card R = 9)
    (hperm : (R : Set Lin) * (S : Set Lin) = (S : Set Lin) * (R : Set Lin)) :
    InnerSubgroupInvariant (S : Subgroup Lin) R := by
  obtain ⟨W, hW0, hW1, hRW, hSW, hNW⟩ := pair_subspace S R hR hperm
  have hdim : Module.finrank (ZMod 2) Vec = 5 := by simp [Vec, Space]
  have hsum := W.finrank_quotient_add_finrank
  have hWd : Module.finrank (ZMod 2) W < 5 := by
    simpa only [hdim] using Submodule.finrank_lt hW1
  have hWp : 0 < Module.finrank (ZMod 2) W := by
    by_contra hn
    exact hW0 (Submodule.finrank_eq_zero.mp (by omega))
  by_cases hd1 : Module.finrank (ZMod 2) W = 1
  · have hd4 : Module.finrank (ZMod 2) (Vec ⧸ W) = 4 := by omega
    let e : BinaryLinear.GL (Vec ⧸ W) ≃* LinearGroup 4 := by
      rw [← hd4]
      exact linearCoordinates (V := Vec ⧸ W)
    apply invariant_from_four_section S R (parabolic W) hR hRW hSW hNW hperm
      (e.toMonoidHom.comp (quotientAction W))
      (e.surjective.comp (quotientAction_surjective W))
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact quotientAction_kernel_two W hd1
  by_cases hd4 : Module.finrank (ZMod 2) W = 4
  · have hd1 : Module.finrank (ZMod 2) (Vec ⧸ W) = 1 := by omega
    let e : BinaryLinear.GL W ≃* LinearGroup 4 := by
      rw [← hd4]
      exact linearCoordinates (V := W)
    apply invariant_from_four_section S R (parabolic W) hR hRW hSW hNW hperm
      (e.toMonoidHom.comp (restrictionAction W))
      (e.surjective.comp (restrictionAction_surjective W))
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact restrictionAction_kernel_two W hd1
  have hwsmall : Module.finrank (ZMod 2) W < 4 := by omega
  have hqsmall : Module.finrank (ZMod 2) (Vec ⧸ W) < 4 := by omega
  obtain ⟨hKb, hKt⟩ := pointwiseFixer_proper_nontrivial R hR W hwsmall hqsmall hRW
  refine ⟨pointwiseFixer R W, hKb, hKt, ?_⟩
  rintro α ⟨q, hqS, hqR⟩ x hx
  have hqNR := normalizes_of_extension R α q hqR
  have hqNS : q ∈ normalizer (S : Set Lin) := fun x => (hqS x).symm
  exact pointwiseFixer_invariant R W α q (hNW ⟨hqNR, hqNS⟩) hqR hx

variable {Q : Type*} [Group Q]

/-- Actual order excludes an extraspecial complement of order 27 in degree five. -/
theorem elementary_nine_of_linear_equiv (e : Q ≃* Lin)
    (R : Subgroup Q) (hR : Chapter1.XiOddQuotient 3 R) :
    IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
  rcases hR with he | ⟨_, hc, _⟩
  · exact he
  · have hd := R.card_subgroup_dvd_card
    rw [hc, Nat.card_congr e.toEquiv, card_linear] at hd
    norm_num at hd

/-- Transport the intrinsic pair calculation through the specified model isomorphism. -/
theorem invariant_subgroup_of_linear_equiv [Finite Q] (e : Q ≃* Lin)
    (S : Sylow 2 Q) (R : Subgroup Q) (hR : Nat.card R = 9)
    (hperm : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q)) :
    InnerSubgroupInvariant (S : Subgroup Q) R := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let R' := R.map e.toMonoidHom
  let eR : R ≃* R' := e.subgroupMap R
  have hcard : Nat.card R' = 9 := (Nat.card_congr eR.toEquiv).symm.trans hR
  have hperm' : (R' : Set Lin) * (S' : Set Lin) =
      (S' : Set Lin) * (R' : Set Lin) := by
    change ((R.map e.toMonoidHom : Subgroup Lin) : Set Lin) *
      (((S : Subgroup Q).map e.toMonoidHom : Subgroup Lin) : Set Lin) =
      (((S : Subgroup Q).map e.toMonoidHom : Subgroup Lin) : Set Lin) *
      ((R.map e.toMonoidHom : Subgroup Lin) : Set Lin)
    simpa only [coe_map, ← Set.image_mul, Sylow.coe_coe] using congrArg (Set.image e.toMonoidHom) hperm
  obtain ⟨K', hK'b, hK't, hK⟩ := invariant_subgroup S' R' hcard hperm'
  let K := K'.comap eR.toMonoidHom
  refine ⟨K, ?_, ?_, ?_⟩
  · intro hb
    apply hK'b
    apply comap_injective (f := eR.toMonoidHom) eR.surjective
    simpa only [MonoidHom.comap_bot, MonoidHom.ker_eq_bot eR.toMonoidHom eR.injective] using hb
  · intro ht
    apply hK't
    apply comap_injective (f := eR.toMonoidHom) eR.surjective
    simpa only [comap_top] using ht
  · rintro α ⟨q, hqS, hqR⟩ x hx
    have hqNS : q ∈ normalizer (S : Set Q) := fun x => (hqS x).symm
    have hqnS : e q ∈ normalizer (S' : Set Lin) := by
      change e q ∈ normalizer (((S : Subgroup Q).map e.toMonoidHom : Subgroup Lin) : Set Lin)
      rw [← map_equiv_normalizer_eq (S : Subgroup Q) e]
      exact mem_map_of_mem e.toMonoidHom hqNS
    have hα' (r : R') :
        ((MulAut.congr eR α) r : Lin) = MulAut.conj (e q) r := by
      change e (α (eR.symm r) : Q) = _
      rw [hqR]
      simp [MulAut.conj_apply, eR]
      exact congrArg Subtype.val (eR.apply_symm_apply r)
    have hx' := hK (MulAut.congr eR α)
      ⟨e q, fun x => (hqnS x).symm, hα'⟩ (eR x) hx
    change eR (α (eR.symm (eR x))) ∈ K' at hx'
    change eR (α x) ∈ K'
    simpa only [eR.symm_apply_apply] using hx'

/-- The intrinsic inner-pair invariant for the actual PSL₅(2) model. -/
theorem five_innerPairInvariant [Finite Q] (hm : ClassicalGroup.IsPSL Q 5 2)
    (S : Sylow 2 Q) (R : Subgroup Q) (hR : Chapter1.XiOddQuotient 3 R)
    (hperm : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q)) :
    Chapter1.Terminal.LinearFourActions.InnerPairInvariant (S : Subgroup Q) R := by
  obtain ⟨e⟩ := binary_linear_equiv (by decide : 0 < 5) hm
  obtain ⟨he, hc⟩ := elementary_nine_of_linear_equiv e R hR
  let _ := he
  exact (invariant_subgroup_of_linear_equiv e S R hc hperm).toInnerPairInvariant _ _

end FiveOuter

open Chapter1 Chapter1.XiEmbedding.InvariantThree
variable {G : Type*} [Group G] [Finite G] {U X P H L : Subgroup G}

/-- Local irreducibility and the permuting Sylow pair force an outer actor in degree five. -/
theorem five_not_le_innerNormalizer
    (h : XiEmbedding.LocalInput 3 U X P H) (hS : IsSylowIn 2 U H)
    (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 5 2) :
    ¬ U ≤ Terminal.innerTwoQuotientNormalizer L := by
  have hUL : U ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  have hPL : P ≤ L := (le_sup_right.trans h.complement.le).trans hXL
  apply Terminal.LinearFourActions.not_le_innerNormalizer_of_innerPairInvariant h hPL hUL
  obtain ⟨S, hSe⟩ := component_quotient_sylow hS hLH hLn
  rw [← hSe]
  apply FiveOuter.five_innerPairInvariant hm S (XiEmbedding.quotientImage L P)
  · exact h.odd_complement.of_mulEquiv (complementEquiv h hPL)
  · simpa only [← hSe, Sylow.coe_coe] using component_quotient_permute h hPL

/-- The requested component statement, retaining all of the source inputs. -/
theorem five_outer {κ : GroupClass}
    (_hH : IsSQTK κ H) (h : XiEmbedding.LocalInput 3 U X P H)
    (hS : IsSylowIn 2 U H) (hL : L ∈ cComponentsIn H)
    (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (_hq : IsQuasisimple (XiQuotient L))
    (_hD : Nonempty (XiEmbedding.automizer U P ≃* DihedralGroup 4))
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 5 2) :
    ¬ U ≤ Terminal.innerTwoQuotientNormalizer L :=
  five_not_le_innerNormalizer h hS hL.1 hLn hXL hm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction
