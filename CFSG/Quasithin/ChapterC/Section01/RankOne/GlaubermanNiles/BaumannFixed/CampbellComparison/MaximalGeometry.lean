module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.Normalizers
public import Theory.SpecificGroups.SL2.SylowBorelSeparation

/-!
# The actual maximal overgroup in Campbell's comparison

The original marked local group has one maximal overgroup M of its Sylow.
Its natural SL₂ quotient identifies M with the preimage of the Sylow Borel.
Thus g outside M cannot carry a Sylow element outside O₂(H) back into M.
The same M controls the normalizers of every subgroup centralized by J(S)
but not by J(H), as required in the paired replacement argument.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.5.1, II.5.3–5.4,
printed pp.27–28; Aschbacher–Smith C.1.17–18, printed p.126.
-/

public section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Theory.GroupTheory Stellmacher
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J] {e : B →* H}
 {F : Type} [Field F] [CharP F 2] [Finite F]

omit [Finite B] in
theorem InLocalClass.campbell_maximal_eq_borel_preimage (h : InLocalClass e) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) (M : Subgroup H)
    (hM : (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤)
    (q : H →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = localKernel e) :
    M = (normalizer ((d.sylow : Subgroup H).map q : Set SL(2,F))).comap q := by
  obtain ⟨S0,he,hS0⟩ := h.sylow
  have hu : Order.HasUniqueMaximalOver (d.sylow : Subgroup H) ⊤ := by
    rw [hS,he]; exact hS0.1
  have hKM : localKernel e ≤ M := le_sup_left.trans
    (hu.le_maximal hM le_sup_right (h.kernel_sup_sylow_lt_top d.sylow))
  have hkM : q.ker ≤ M := hk ▸ hKM
  have hMmap : M.map q ≠ ⊤ := by
    intro heq
    have hh := congrArg (Subgroup.comap q) heq
    rw [comap_map_eq,sup_eq_left.mpr hkM,comap_top] at hh
    exact hM.2.ne hh
  let P := d.sylow.mapSurjective hq
  have hMP : M.map q ≤ normalizer (P : Set SL(2,F)) :=
    proper_overgroup_le_sylow_normalizer P (M.map q) (map_mono hM.1) hMmap
  apply le_antisymm (map_le_iff_le_comap.mp hMP)
  have hproper : (normalizer (P : Set SL(2,F))).comap q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    apply sylow_normalizer_ne_top P
    have hh := congrArg (Subgroup.map q) ht
    simpa only [map_comap_eq_self_of_surjective hq,map_top_of_surjective q hq] using hh
  apply hu.le_maximal hM ?_ hproper
  intro x hx
  exact (P : Subgroup SL(2,F)).le_normalizer (mem_map_of_mem q hx)

theorem InLocalClass.campbell_maximal_separation (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) (M : Subgroup H)
    (hM : (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤)
    (g x : H) (hg : g ∉ M) (hx : x ∈ d.sylow) (hxQ : x ∉ pCore 2 H) :
    g*x*g⁻¹ ∉ M := by
  obtain ⟨q,f,hq,hk,hf,he⟩ := h.exists_campbell_projection hB m
  have hMP := InLocalClass.campbell_maximal_eq_borel_preimage h d hS M hM q hq hk
  have hSK : (d.sylow : Subgroup H) ⊓ localKernel e = pCore 2 H :=
    d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
  have hqx : q x ≠ 1 := by
    intro he
    have hxK : x ∈ localKernel e := hk ▸ (show x ∈ q.ker from he)
    exact hxQ (hSK ▸ (show x ∈ (d.sylow : Subgroup H) ⊓ localKernel e from ⟨hx,hxK⟩))
  intro hconj
  have hh : q g * q x * (q g)⁻¹ ∈ normalizer ((d.sylow : Subgroup H).map q : Set SL(2,F)) := by
    have hc := hMP ▸ hconj
    change q (g*x*g⁻¹) ∈ normalizer ((d.sylow : Subgroup H).map q : Set SL(2,F)) at hc
    simpa only [map_mul,map_inv] using hc
  have hgq := mem_sylow_normalizer_of_conjugate_mem (d.sylow.mapSurjective hq) (q x) (q g)
    (mem_map_of_mem q hx) hqx hh
  apply hg
  rw [hMP]
  exact hgq

theorem InLocalClass.exists_campbell_maximal_geometry (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (d : Campbell.Embedding J H)
    (hS : (d.sylow : Subgroup H) = e.range) :
    ∃ M : Subgroup H, (d.sylow : Subgroup H) ≤ M ∧ M ⋖ ⊤ ∧
      (∀ Z : Subgroup H, Z ≤ centralizer (Campbell.J (d.sylow : Subgroup H) : Set H) →
        ¬ Z ≤ centralizer (Campbell.J (⊤ : Subgroup H) : Set H) →
        normalizer (Z : Set H) ≤ M) ∧
      ∀ g ∉ M, ∀ x ∈ d.sylow, x ∉ pCore 2 H → g*x*g⁻¹ ∉ M := by
  obtain ⟨M,hSM,hMt,hcontrol⟩ := h.exists_campbell_maximal_normalizer_bound hB m d hS
  exact ⟨M,hSM,hMt,hcontrol,fun g hg x hx hxQ =>
    InLocalClass.campbell_maximal_separation h hB m d hS M ⟨hSM,hMt⟩ g x hg hx hxQ⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
