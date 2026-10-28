module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearEquality.Irreducible
public import CFSG.Quasithin.ChapterG.Section01.RankOne.Irreducible
public import Theory.Representation.Quotient

/-!
# The natural chart on the original two-conjugate core

In the equality range the original P/Z action is irreducible. Its
normal two-core acts trivially, so J=O₂(X) permits descent through the
literal X/J projection. The original B/Z embeds into the fixed space
of V*. When V* is the whole Sylow subgroup, its dimension reaches m;
the Schur-fixed-space recognition then gives the actual natural chart.
The exported linear equivalence intertwines the original X-conjugation
with the specified original X/J matrix marking.

Source: the linear-two equality case in Aschbacher–Smith E.2.15,
printed p.228, using the irreducible part of G.1.7.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Representation
open Representation.BinaryOffender
open scoped Matrix MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

set_option maxRecDepth 2000 in
theorem linear_two_core_natural_of_rank_le_and_sylow
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* SL(2,F))
    (hrank : Nat.log 2 ((Z V g).relIndex (A V M g)) ≤ m)
    (S : Sylow 2 SL(2,F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) = S) :
    letI := h.Z_normal
    letI := h.core_geometry.1
    let q := QuotientGroup.mk' (Z V g)
    letI := h.quotient_direct_sum.1
    letI := ZMod.algebra F 2
    ∃ e : Additive ((P V M g).map q) ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ x u, e (normalRepresentation ((P V M g).map q) (q x) u) =
        (ξ (QuotientGroup.mk' (J M) x)).val *ᵥ (e u) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let := h.elementary
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  let := ZMod.algebra F 2
  let ρ := normalRepresentation U
  let σ := ρ.comp q
  let : IsIrreducible ρ := h.linear_two_core_action_irreducible_of_rank_le
    hproper hfit m hm hcard ξ hrank
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q
    (QuotientGroup.mk'_surjective _) ρ).mpr inferInstance
  have hk : J M ≤ σ.ker := by
    rw [h.J_eq_twoCore_of_linear_two m hm hcard ξ]
    exact normal_p_subgroup_le_ker σ _ pCore_isPGroup
  let τ := quotientOfLEKer σ (J M) hk
  let ψ := τ.comp ξ.symm.toMonoidHom
  let : IsIrreducible τ := (quotientOfLEKer_irreducible_iff σ _ hk).mpr inferInstance
  let : IsIrreducible ψ := (irreducible_comp_surjective_iff ξ.symm.toMonoidHom
    ξ.symm.surjective τ).mpr inferInstance
  have hact (x : X) (u : Additive U) :
      ψ (ξ (QuotientGroup.mk' (J M) x)) u = ρ (q x) u := by
    simp only [ψ,τ,σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      ξ.symm_apply_apply,quotientOfLEKer_apply]
  have hn : ∃ a, ψ a ≠ 1 := by
    by_contra! hn
    have hr := h.quotient_core_noncentral_chief_exists hproper hfit
    obtain ⟨s⟩ := SeriesOn.exists_series U
    obtain ⟨i,hi⟩ := hr s
    apply hi
    rw [s.central_iff_action]
    intro x u
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Z V g) x
    have hs : ρ (q x) = 1 := by
      ext v
      rw [← hact x v,hn]
    -- The whole original action is trivial, hence so is every literal chief factor.
    obtain ⟨z,hz⟩ := QuotientGroup.mk'_surjective ((s.lower i).val.subgroupOf (s.upper i).val) u
    rw [← hz,s.action_mk]
    congr 1
    apply Subtype.ext
    have he := congrArg (fun a => (a (Additive.ofMul
      ⟨z, s.term_le i.succ z.property⟩)).toMul) hs
    exact congrArg (fun z : U => (z : X ⧸ Z V g)) he
  have hdim : Module.finrank (ZMod 2) (Additive U) ≤ 2*m := by
    have hh := h.quotient_core_finrank_eq_twice_actor
    dsimp only [U,q] at ⊢
    omega
  let Bbar := (B V M).map q
  have hBU : Bbar ≤ U := map_mono le_sup_left
  have hfix (b : Bbar) : (Additive.ofMul ⟨b,hBU b.property⟩ : Additive U) ∈
      fixedSpace ψ (S : Subgroup _) := by
    intro s
    have hs : (s : SL(2,F)) ∈ V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) := by
      rw [hVS]
      exact s.property
    obtain ⟨v,hv,hvs⟩ := hs
    change ψ (s : SL(2,F)) _ = _
    rw [← hvs]
    change ψ (ξ (QuotientGroup.mk' (J M) v)) _ = _
    rw [hact]
    apply Additive.toMul.injective
    apply Subtype.ext
    obtain ⟨b0,hb0,hbb⟩ := b.property
    change q v * b * (q v)⁻¹ = b
    rw [← hbb,← map_mul,← map_inv,← map_mul]
    congr 1
    rw [(V.le_centralizer hb0.2) v hv,mul_inv_cancel_right]
  let j : Bbar → fixedSpace ψ (S : Subgroup _) := fun b =>
    ⟨Additive.ofMul ⟨b,hBU b.property⟩,hfix b⟩
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : fixedSpace ψ (S : Subgroup _) => (z.val.toMul : X ⧸ Z V g)) hab
  have hBc : Nat.card Bbar = (Z V g).relIndex (A V M g) := by
    rw [← relIndex_ker,QuotientGroup.ker_mk']
    have hZg : (Z V g).map (MulAut.conj g).toMonoidHom = Z V g :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
    have ht := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (Z V g) (B V M) (MulAut.conj g).injective
    rw [hZg] at ht
    exact ht.symm
  have hfdim : m ≤ Module.finrank (ZMod 2) (fixedSpace ψ (S : Subgroup _)) := by
    have hc := Nat.card_le_card_of_injective j hj
    rw [hBc] at hc
    have hl := Nat.log_mono_right (b := 2) hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Nat.log_pow (by decide : 1 < 2)] at hl
    exact (h.actor_rank_ge_linear_two_star hproper hfit m hm hcard ξ).trans hl
  obtain ⟨e⟩ := ChapterG.Section01.RankOne.natural_of_minimal_degree_and_sylow_fixed
    ψ m hm hcard hn S hdim hfdim
  refine ⟨e.toLinearEquiv,?_⟩
  intro x u
  rw [← hact x u]
  exact Representation.IntertwiningMap.isIntertwining ψ _ e.toIntertwiningMap _ _
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
