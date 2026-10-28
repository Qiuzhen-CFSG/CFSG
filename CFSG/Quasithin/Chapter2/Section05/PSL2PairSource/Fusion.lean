module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.InitialAction
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# Internal fusion in the actual crossing pair

The source square condition makes x swap K and Kˣ and hence normalize their
join. PSL₂ has a single involution class, so every involution in either factor
is conjugate to t inside the original M₊. This proves the easy direction of
the marked-class identity, with explicit conjugators. It does not exclude
additional global conjugates of t in M₊.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
2.5.21, printed pp.566–567.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

omit [Finite G] in
/-- Conjugacy inside a subgroup with an actual PSL₂ model. -/
theorem involutions_conjugate_in_factor (K : Subgroup G)
    (e : K ≃* PSL(2, ZMod p)) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (hoa : orderOf a = 2) (hob : orderOf b = 2) :
    ∃ k ∈ K, k * a * k⁻¹ = b := by
  let aK : K := ⟨a, ha⟩
  let bK : K := ⟨b, hb⟩
  have hA : orderOf (e aK) = 2 :=
    (e.orderOf_eq aK).trans ((orderOf_coe aK).symm.trans hoa)
  have hB : orderOf (e bK) = 2 :=
    (e.orderOf_eq bK).trans ((orderOf_coe bK).symm.trans hob)
  have hh := e.symm.toMonoidHom.map_isConj (Theory.PSL2.involutions_isConj (e aK) (e bK) hA hB)
  have hab : IsConj aK bK := by simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hh
  obtain ⟨k, hk⟩ := isConj_iff.mp hab
  exact ⟨k, k.property, congrArg Subtype.val hk⟩

namespace Incoming
variable (d : Incoming κ G p)

/-- The original crossing element swaps the actual two factors, so belongs
to M₊. The source square condition, rather than x² = 1, is used. -/
theorem crossing_mem_pair_normalizer : d.x ∈
    normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) := by
  apply (mem_normalizer_iff_conjugate_eq _ _).mpr
  change (d.K ⊔ conjugate d.K d.x).map (MulAut.conj d.x⁻¹).toMonoidHom = _
  rw [Subgroup.map_sup]
  change conjugate d.K d.x ⊔ conjugate (conjugate d.K d.x) d.x = _
  rw [conjugate_conjugate, ← pow_two]
  have hSK : d.S ≤ normalizer (d.K : Set G) := by
    have hSJ : d.S ≤ centralizer ({d.t} : Set G) := by
      rw [← d.sylow_eq]
      exact map_subtype_le _
    have hKJ : d.K ≤ centralizer ({d.t} : Set G) := by
      rw [d.generated]
      exact le_sup_of_le_left le_sup_left
    exact hSJ.trans ((normal_subgroupOf_iff_le_normalizer hKJ).mp d.normalK)
  rw [(mem_normalizer_iff_conjugate_eq _ _).mp (hSK d.x_square), sup_comm]

/-- Every involution in either actual factor is fused with t inside M₊.
This proves internal fusion and the easy inclusion of the marked-class
identity without an assumption on global fusion. -/
theorem factor_involution_conjugate {a : G} (ha : orderOf a = 2)
    (hmem : a ∈ (d.K : Set G) ∪ conjugate d.K d.x) :
    ∃ m ∈ normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G),
      m * d.t * m⁻¹ = a := by
  let M := normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G)
  have hKM : d.K ≤ M := le_sup_left.trans (d.K ⊔ conjugate d.K d.x).le_normalizer
  have hLM : conjugate d.K d.x ≤ M := le_sup_right.trans (d.K ⊔ conjugate d.K d.x).le_normalizer
  rcases hmem with haK | haL
  · have htx : orderOf (d.x⁻¹ * d.t * d.x) = 2 := by
      have hh := (MulAut.conj d.x⁻¹).orderOf_eq d.t
      simpa only [MulAut.conj_apply, inv_inv, d.t_order] using hh
    obtain ⟨k, hk, he⟩ := involutions_conjugate_in_factor d.K d.model d.crossing_mark haK htx ha
    refine ⟨k * d.x⁻¹, M.mul_mem (hKM hk) (M.inv_mem d.crossing_mem_pair_normalizer), ?_⟩
    calc
      _ = k * (d.x⁻¹ * d.t * d.x) * k⁻¹ := by group
      _ = a := he
  · let eL : conjugate d.K d.x ≃* PSL(2, ZMod p) :=
      ((MulAut.conj d.x⁻¹).subgroupMap d.K).symm.trans d.model
    obtain ⟨l, hl, he⟩ := involutions_conjugate_in_factor _ eL d.mark_mem haL d.t_order ha
    exact ⟨l, hLM hl, he⟩

end Incoming
end CFSG.Quasithin.Chapter2.PSL2PairSource

end
