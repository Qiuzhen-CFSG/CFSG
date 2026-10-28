module
public import Theory.Representation.BinaryRadicalFlag.FixedFiltration
public import Theory.Representation.BinaryRadicalFlag.FlagKernel
public import Theory.GroupTheory.PRadicalParabolicReduction
public import Theory.GroupTheory.PRadical
/-!
# Radical normalizers from the canonical fixed filtration

For a faithful binary representation, repeatedly taking fixed vectors on the
quotient gives a strictly increasing invariant filtration from zero to the
whole space. Its full stabilizer normalizes the subgroup acting trivially on
each layer. This layer kernel is a two-group containing the original radical
subgroup, so the radical-normalizer reduction identifies both subgroups and
both normalizers. Removing the endpoints gives a nonempty proper partial flag.

No flag, triangular coordinates, or parabolic placement is assumed.
Source: Aschbacher (1981), A pushing up theorem for finite groups, 8.2(7),
pp.73–74; Aschbacher–Smith C.2.7(3), printed pp.145–146.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Representation.BinaryRadical
open Subgroup
variable {F G V : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V] [CharP F 2]
    (ρ : Representation F G V) (hρ : Function.Injective ρ)

include hρ in
theorem exists_fullFlag_normalizer (U : Subgroup G) (hU : U.IsPRadical 2) :
    ∃ (k : ℕ) (W : Fin (k+1) → Submodule F V),
      2 ≤ k ∧ k ≤ Module.finrank F V ∧
      StrictMono W ∧ W 0 = ⊥ ∧ W (Fin.last k) = ⊤ ∧
      normalizer (U : Set G) = flagStabilizer ρ W := by
  let N := normalizer (U : Set G)
  let A := U.subgroupOf N
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let τ := ρ.comp N.subtype
  obtain ⟨k,W,hs,hzero,hlast,hbound,hstable,hlayers⟩ :=
    exists_fixed_filtration τ A hU.isPGroup.comap_subtype
  have hNP : N ≤ flagStabilizer ρ W := by
    intro g hg
    apply (mem_flagStabilizer ρ W).mpr
    intro i v
    constructor
    · intro hv
      have hh := hstable (⟨g⁻¹,N.inv_mem hg⟩ : N) i (ρ g v) hv
      simpa only [τ,MonoidHom.comp_apply,Subgroup.subtype_apply,Subgroup.coe_mk,←Module.End.mul_apply,
        ←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh
    · exact hstable (⟨g,hg⟩ : N) i v
  have hUQ : U ≤ flagKernel ρ W := by
    intro u hu
    refine ⟨hNP (U.le_normalizer hu),?_⟩
    intro i v hv
    exact hlayers i (⟨⟨u,U.le_normalizer hu⟩,hu⟩ : A) v hv
  have heq := SubgroupFusion.pRadical_eq_of_normalizer_le hU.isPGroup hU.2.le
    (flagKernel_isPGroup ρ hρ W hzero hlast) hUQ hNP
    (flagStabilizer_le_normalizer ρ W)
  have hk : 2 ≤ k := by
    by_contra hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · have he : (⊥ : Submodule F V) = ⊤ := hzero.symm.trans hlast
      exact bot_ne_top he
    · apply hU.1
      apply le_antisymm _ bot_le
      intro u hu
      apply mem_bot.mpr
      apply hρ
      rw [map_one]
      apply LinearMap.ext
      intro v
      have hd := (hUQ hu).2 (0 : Fin 1) v (hlast.symm ▸ Submodule.mem_top)
      rw [show (0 : Fin 1).castSucc = (0 : Fin 2) from rfl,hzero,Submodule.mem_bot] at hd
      exact sub_eq_zero.mp hd
  exact ⟨k,W,hk,hbound,hs,hzero,hlast,heq.2⟩

include hρ in
theorem exists_partialFlag_normalizer (U : Subgroup G) (hU : U.IsPRadical 2) :
    ∃ (k : ℕ) (W : Fin k → Submodule F V),
      0 < k ∧ k < Module.finrank F V ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      normalizer (U : Set G) = ⨅ i, stabilizer ρ (W i) := by
  obtain ⟨k,W,hk,hbound,hs,hzero,hlast,heq⟩ := exists_fullFlag_normalizer ρ hρ U hU
  let f : Fin (k-1) → Fin (k+1) := fun i => ⟨i.val+1,by omega⟩
  have hf : StrictMono f := by intro i j hij; change i.val+1<j.val+1; exact Nat.add_lt_add_right hij 1
  refine ⟨k-1,W ∘ f,by omega,by omega,hs.comp hf,?_,?_⟩
  · intro i
    have ha : (0 : Fin (k+1)) < f i := by change (0 : ℕ) < i.val + 1; omega
    have hb : f i < Fin.last k := by change i.val+1<k; have := i.isLt; omega
    exact ⟨by simpa only [Function.comp_apply,hzero] using (hs ha).ne.symm,
      by simpa only [Function.comp_apply,hlast] using (hs hb).ne⟩
  · rw [heq]
    apply le_antisymm
    · intro g hg
      simp only [Subgroup.mem_iInf]
      intro i
      exact (mem_flagStabilizer ρ W).mp hg (f i)
    · intro g hg
      simp only [Subgroup.mem_iInf] at hg
      apply (mem_flagStabilizer ρ W).mpr
      intro i v
      by_cases hi : i=0
      · subst i
        rw [hzero]
        simp only [Submodule.mem_bot]
        constructor
        · intro hv
          have hh := congrArg (ρ g⁻¹) hv
          simpa only [map_zero,←Module.End.mul_apply,←map_mul,inv_mul_cancel,
            map_one,Module.End.one_apply] using hh
        · rintro rfl; exact map_zero _
      by_cases hi' : i=Fin.last k
      · subst i
        simp only [hlast,Submodule.mem_top]
      · let j : Fin (k-1) := ⟨i.val-1,by
          have ht := i.isLt
          have hz : i.val ≠ 0 := by intro hz; exact hi (Fin.ext hz)
          have hl : i.val ≠ k := by intro hl; exact hi' (Fin.ext hl)
          omega⟩
        have hji : f j = i := by
          apply Fin.ext
          have hz : i.val ≠ 0 := by intro hz; exact hi (Fin.ext hz)
          change i.val-1+1=i.val
          omega
        simpa only [Function.comp_apply,hji] using hg j v

end Representation.BinaryRadical
