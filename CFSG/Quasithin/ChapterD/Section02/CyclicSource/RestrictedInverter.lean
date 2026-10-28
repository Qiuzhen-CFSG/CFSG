module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceReduction

/-!
# A three-core inverter on the residual source module

A rank-one binary operator commuting with an odd group has an invariant
binary line, hence a fixed line. This is impossible on a fully moved module.
If the involution centralizes the odd complement of O₃, a nontrivial
commutator with O₃ therefore acts on the module; that commutator is inverted
by the involution. This gives the actual residual element in D.2.25.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) G W)

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
private theorem binary_line_fixed (L : Submodule (ZMod 2) W)
    (hL : Module.finrank (ZMod 2) L = 1) (a : G)
    (hstable : ∀ v ∈ L, σ a v ∈ L) : ∀ v ∈ L, σ a v = v := by
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have he := eq_span_singleton_of_mem_of_finrank_eq_one hL hv hv0
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (he ▸ hstable v hv)
  have hc0 : c ≠ 0 := by
    intro hz
    have hzero : σ a v = 0 := by simpa [hz] using hc.symm
    have hh := congrArg (σ a⁻¹) hzero
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] at hh
    exact hv0 hh
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- On a fixed-point-free binary module, a rank-one operator cannot commute
with every acting element. No faithfulness or involution assumption is needed. -/
theorem exists_noncommuting_of_rank_one (P : Subgroup G)
    (hfixed : fixedSpace σ P = ⊥) (t : G)
    (hr : Module.finrank (ZMod 2) (σ t - 1).range = 1) :
    ∃ p ∈ P, ∃ w : W, σ t (σ p w) ≠ σ p (σ t w) := by
  by_contra! hn
  have hle : (σ t - 1).range ≤ fixedSpace σ P := by
    intro v hv p
    apply binary_line_fixed σ (σ t - 1).range hr p.val ?_ v hv
    rintro _ ⟨w,rfl⟩
    refine ⟨σ p w,?_⟩
    change σ t (σ p w) - σ p w = σ p (σ t w - w)
    rw [map_sub, hn p p.property w]
  have he : (σ t - 1).range = ⊥ := le_bot_iff.mp (hle.trans_eq hfixed)
  rw [he, finrank_bot] at hr
  exact Nat.zero_ne_one hr

omit [FiniteDimensional (ZMod 2) W] in
/-- The actual inverted three-core element required for the residual rank-one
module in source D.2.25. Applying this to a subrepresentation keeps its literal
vectors and action, without any faithful quotient or complement deletion. -/
theorem exists_three_core_inverted_mover
    (hcore : pCore 2 G = ⊥)
    (hmoved : subspaceCommutator σ ⊤ (fittingSubgroup G) = ⊤)
    (t : G) (ht : t * t = 1)
    (hcomp : t ∈ centralizer (SourceReduction.oddComplement G : Set G))
    (hr : Module.finrank (ZMod 2) (σ t - 1).range = 1) :
    ∃ x ∈ pCore 3 G, t * x * t⁻¹ = x⁻¹ ∧ ∃ w : W, σ x w ≠ w := by
  have hfixed : fixedSpace σ (fittingSubgroup G) = ⊥ := by
    have hs := Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd
      (ρ := σ) (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore)
    have he : Representation.RegularCyclicNormalClosure.displacementSpan
        σ (fittingSubgroup G) ⊤ = subspaceCommutator σ ⊤ (fittingSubgroup G) := by
      unfold Representation.RegularCyclicNormalClosure.displacementSpan subspaceCommutator
      congr 1
      ext v
      simp only [Set.mem_ofPred_eq,eq_comm]
    rw [he,hmoved] at hs
    simpa only [inf_top_eq] using hs.disjoint.eq_bot
  have hp : ∃ p ∈ pCore 3 G, ∃ w : W, σ t (σ p w) ≠ σ p (σ t w) := by
    by_contra! hn
    obtain ⟨f,hf,w,hw⟩ := exists_noncommuting_of_rank_one σ _ hfixed t hr
    rw [SourceReduction.fitting_eq_three_sup_complement] at hf
    obtain ⟨p,hp,q,hq,rfl⟩ := mem_sup_of_normal_left.mp hf
    apply hw
    simp only [map_mul,Module.End.mul_apply]
    rw [hn p hp]
    congr 1
    exact congrArg (fun e : Module.End (ZMod 2) W => e w)
      (show σ t * σ q = σ q * σ t by rw [← map_mul,← map_mul,hcomp q hq])
  obtain ⟨p,hp,w,hw⟩ := hp
  let x := t * p * t⁻¹ * p⁻¹
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  refine ⟨x,(pCore 3 G).mul_mem ((inferInstance : (pCore 3 G).Normal).conj_mem p hp t)
    ((pCore 3 G).inv_mem hp),?_,?_⟩
  · dsimp [x]
    simp only [mul_inv_rev,inv_inv,hti]
    group
    simp only [ht,one_mul]
  · by_contra! hn
    apply hw
    have hh := hn (σ p (σ t w))
    have hprod : x * (p * t) = t * p := by dsimp [x]; group
    simpa only [← Module.End.mul_apply,← map_mul,hprod] using hh

end CFSG.Quasithin.ChapterD.CyclicSource
