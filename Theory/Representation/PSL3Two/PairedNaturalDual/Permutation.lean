module
public import Theory.Representation.PSL3Two.PairedNaturalDual
public import Theory.Representation.BinaryOffender.QuadraticPairPermutation.Stability
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# No offenders on a permuted pair of natural--dual supports

Quadratic replacement and the large-support swapping obstruction put an
offender in the common support stabilizer. The two marked natural--dual
actions there have additive displacement costs and jointly faithful actor
maps, contradicting the offender bound. In particular no involution acts as
a transvection, including an involution exchanging the component supports.

Source: Aschbacher--Smith 14.6.24(a)--(b), printed p.1039. The Chapter14
consumer applies this to the original U/Z and selects the critical endpoint.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual.Paired
variable {H E : Type*} [_root_.Group H] [Finite H]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E) (N : Subgroup H) (m : Marking (ρ.comp N.subtype))

/-- Replacement reduces every offender to a quadratic one. Large disjoint
supports force it to preserve the pair, where the two non-FF bounds add. -/
theorem not_ff_of_permuted_pair (hf : Function.Injective ρ)
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : H,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range)) :
    ¬ IsFFModule ρ := by
  rintro ⟨A,hA⟩
  obtain ⟨B,_,hB,hq,_⟩ := hA.exists_quadratic_minimalBestOffender ρ
  have hb := hB.1.isOffender ρ
  let : IsElementaryAbelian 2 B := hb.1.2
  have hdim : 2 < Module.finrank (ZMod 2) m.leftEmbedding.range := by
    rw [←(LinearEquiv.ofInjective m.leftEmbedding m.left_injective).finrank_eq]
    change 2 < Module.finrank (ZMod 2) (Vector × Module.Dual (ZMod 2) Vector)
    rw [Module.finrank_prod,Subspace.dual_finrank_eq]
    norm_num [Vector,Matrix.PSL3Two.Fano.Vector]
  have hp := quadratic_preserves_large_pair ρ hf m.leftEmbedding.range m.rightEmbedding.range
    m.disjoint hspan hdim B hq (by have := hb.2; omega) (fun a _ => hperm a)
  have hBN : B ≤ N := by
    rw [hN]
    apply le_inf
    · apply le_subspaceStabilizer
      intro b hb v hv
      exact (hp b hb).1 ▸ Submodule.mem_map_of_mem hv
    · apply le_subspaceStabilizer
      intro b hb v hv
      exact (hp b hb).2 ▸ Submodule.mem_map_of_mem hv
  have hm : (B.subgroupOf N).map N.subtype = B := map_subgroupOf_eq_of_le hBN
  have hc := fixedCodim_map_equivariant (ρ.comp N.subtype) ρ N.subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) (B.subgroupOf N)
  rw [hm] at hc
  have hr := rank_map_injective N.subtype N.subtype_injective (B.subgroupOf N)
  rw [hm] at hr
  apply m.not_ff (hf.comp N.subtype_injective)
  refine ⟨B.subgroupOf N,⟨?_,IsElementaryAbelian.subgroupOf hBN⟩,?_⟩
  · intro he
    exact hb.1.1 (by rw [←hm,he,Subgroup.map_bot])
  · rw [hc,←hr]
    exact hb.2

/-- The component markings discharge the no-transvection premise used to
select the terminal critical endpoint. This includes exchanging involutions. -/
theorem no_involution_transvections (hf : Function.Injective ρ)
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : H,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (a : H) (ha : orderOf a = 2) : 2 ≤ fixedCodim ρ (zpowers a) := by
  have hn := not_ff_of_permuted_pair ρ N m hf hN hspan hperm
  obtain ⟨he,hr,_,_⟩ := involution_actor_rank_and_fixedCodim ρ a ha
  have hh : rank (zpowers a) < fixedCodim ρ (zpowers a) :=
    Nat.lt_of_not_ge (fun hle => hn ⟨_,he,hle⟩)
  omega
end BinaryLinearThree.NaturalDual.Paired
