module

public import BenderSuzuki.External.Huppert.X.ConjugationFamily
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Extremal normalizer steps with a p-group automizer

In ABG Chapter II §1, article p.11 (the paragraph following the Alperin
fusion formulation), a tame intersection cannot introduce new fusion if its
normalizer modulo centralizer is a 2-group. This module proves the corresponding
statement for an extremal subgroup `U` of a Sylow `p`-subgroup `P`. It uses the
conjugation-action image, isomorphic to the normalizer/centralizer quotient,
and also gives the sufficient hypothesis that the whole `MulAut U` is a p-group.
The conclusion is actual conjugacy of elements in the subgroup type `P`.

Extremality realizes `P ∩ N_G(U)` as a Sylow subgroup of `N_G(U)`. Its image
under the normalizer action is a Sylow subgroup of the action image. If that
image is a p-group, the mapped Sylow subgroup is the whole image. Thus each
normalizer action agrees with an action from `P ∩ N_G(U)`; evaluating the
inverse automorphisms proves the required right-conjugation identity.
-/

noncomputable section

namespace ABG

open BenderSuzuki.External

universe u

/-- A p-group image of the normalizer action introduces no new element fusion
at an extremal subgroup of a Sylow subgroup. -/
public theorem extremal_normalizer_fusion_control_of_range_isPGroup
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (U : Subgroup G) (hU : HuppertExtremal P U)
    (hRange : IsPGroup p (Subgroup.normalizerMonoidHom (H := U)).range)
    (g : G) (hg : g ∈ Subgroup.normalizer (U : Set G))
    (x y : P) (hxU : (x : G) ∈ U)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) : IsConj x y := by
  let N : Subgroup G := Subgroup.normalizer (U : Set G)
  let phi : N →* MulAut U := Subgroup.normalizerMonoidHom (H := U)
  obtain ⟨SN, hSN⟩ := hU.exists_sylow_normalizer
  let R : Subgroup (MulAut U) := phi.range
  let SR : Sylow p R := SN.mapSurjective (f := phi.rangeRestrict)
    phi.rangeRestrict_surjective
  have hRp : IsPGroup p R := hRange
  have hSRtop : (SR : Subgroup R) = ⊤ := by
    symm
    exact SR.is_maximal' (hRp.to_subgroup ⊤) le_top
  let gN : N := ⟨g, hg⟩
  let a : R := ⟨phi gN, ⟨gN, rfl⟩⟩
  have haSR : a ∈ (SR : Subgroup R) := by rw [hSRtop]; trivial
  rw [Sylow.coe_mapSurjective] at haSR
  rcases haSR with ⟨sN, hsSN, hphis⟩
  have hphi : phi sN = phi gN := congrArg Subtype.val hphis
  have hsP : (sN : G) ∈ (P : Subgroup G) := by
    have hsmap := Subgroup.mem_map_of_mem N.subtype hsSN
    rw [hSN] at hsmap
    exact hsmap.1
  let s : P := ⟨sN, hsP⟩
  apply isConj_iff.mpr
  refine ⟨s⁻¹, ?_⟩
  apply Subtype.ext
  simp only [inv_inv]
  change (sN : G)⁻¹ * (x : G) * (sN : G) = (y : G)
  have hinv : phi sN⁻¹ = phi gN⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv hphi
  have heq := congrArg (fun f : MulAut U => ((f ⟨(x : G), hxU⟩ : U) : G)) hinv
  have hconj : (sN : G)⁻¹ * (x : G) * (sN : G) = g⁻¹ * (x : G) * g := by
    simpa [phi, N, gN, Subgroup.normalizerMonoidHom_apply_apply_coe] using heq
  exact hconj.trans hxy

/-- In particular, a p-group full automorphism group ensures that normalizer
fusion at an extremal subgroup is already conjugacy inside the Sylow subgroup. -/
public theorem extremal_normalizer_fusion_control
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (U : Subgroup G) (hU : HuppertExtremal P U)
    (hAut : IsPGroup p (MulAut U))
    (g : G) (hg : g ∈ Subgroup.normalizer (U : Set G))
    (x y : P) (hxU : (x : G) ∈ U)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) : IsConj x y :=
  extremal_normalizer_fusion_control_of_range_isPGroup P U hU
    (hAut.to_subgroup _) g hg x y hxU hxy

end ABG
