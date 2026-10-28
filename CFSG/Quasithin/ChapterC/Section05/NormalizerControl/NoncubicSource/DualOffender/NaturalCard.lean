module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Quadratic
public import Theory.Representation.SL2OrthogonalCover.Universal
/-!
# The numerical bound for a genuine natural central cover

The universal binary orthogonal cover surjects onto the original module,
so its order is at most q³. The literal natural quotient identifies q
with the source coordinate field order. C.5.6 gives the conjugate actor
index q, hence the actual fixed intersection has order at most q².
Source: Aschbacher–Smith I.2.3 and C.5.13, printed pp.413 and162.
-/
public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {K T : Subgroup G} {F : Type*} [Field F]
omit [Finite G] in
private theorem projection_index_of_kernel {E : Type*} [Field E]
    (p : U K →* Multiplicative (Fin 2 → E)) (hp : Function.Surjective p)
    (hk : ∀ u, p u = 1 ↔ (u : G) ∈ centralizer (K : Set G)) :
    (centralizer (K : Set G)).relIndex (U K) = Nat.card E * Nat.card E := by
  have he : (centralizer (K : Set G)).subgroupOf (U K) = p.ker := by
    ext u
    exact (hk u).symm
  change ((centralizer (K : Set G)).subgroupOf (U K)).index = _
  rw [he,index_ker,p.range_eq_top_of_surjective hp,
    Nat.card_congr (topEquiv.toEquiv.trans Multiplicative.toAdd),Nat.card_fun,Nat.card_fin,pow_two]
omit [Finite G] in
/-- The original block and the Baumann marking have the same natural field order. -/
theorem natural_coordinate_card (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) :
    Nat.card F = 2^n := by
  obtain ⟨_,_,E,_,_,hE,_,_,⟨m⟩,_⟩ := hn
  have hh := (projection_index h.coordinates).symm.trans
    (projection_index_of_kernel (modelProjection m) (modelProjection_surjective m) (modelProjection_kernel m))
  have he : Nat.card F = Nat.card E := by nlinarith
  exact he.trans hE
/-- The full natural block module, including its central layer, has order
at most the cube of the field order in the actual source coordinates. -/
theorem natural_module_card_le (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) :
    Nat.card (U K) ≤ Nat.card F ^ 3 := by
  obtain ⟨hn,hs,E,_,_,hE,_,α,⟨m⟩,hα⟩ := hn
  let : IsElementaryAbelian 2 (blockU K) := hs.elementary
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let π := SL2OrthogonalCover.binaryNatural (F := E)
  let σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) E) (Additive (blockU K)) := IntrinsicCover.action hs m
  let p : σ.IntertwiningMap π := IntrinsicCover.projection hs m π hα
  have hp : IsCover p := IntrinsicCover.projection_isCover hs m π hα
  have hd : Module.finrank (ZMod 2) (SL2OrthogonalCover.binaryProjection (F := E)).toLinearMap.ker =
      Module.finrank (ZMod 2) (H1 π.dual) := by
    rw [SL2OrthogonalCover.binary_kernel_finrank n hE,SL2OrthogonalCover.binary_dual_H1_finrank n hn hE]
  obtain ⟨f,hf,_⟩ := exists_quotient_of_finrank_ker_eq (k := ZMod 2)
    (ρ := π) (σ := SL2OrthogonalCover.binaryAction (F := E)) (τ := σ)
    (SL2OrthogonalCover.binaryProjection (F := E))
    (SL2OrthogonalCover.binaryProjection_isCover (SL2OrthogonalCover.card_gt_two n hn hE)) hd p hp
  have hb := Nat.card_le_card_of_surjective f hf
  have heq : Nat.card F = Nat.card E := by
    have hh := (projection_index h.coordinates).symm.trans
      (projection_index_of_kernel (modelProjection m) (modelProjection_surjective m) (modelProjection_kernel m))
    nlinarith
  rw [heq,← Nat.card_congr (intrinsicEquiv K).toEquiv]
  simpa only [SL2OrthogonalCover.Space,Nat.card_fun,Nat.card_fin,
    Nat.card_congr (Additive.toMul : Additive (blockU K) ≃ blockU K)] using hb
/-- The original noncommuting conjugate has index q and full fixed subgroup
of order at most q². This is the numerical C.5.13 natural-cover inequality. -/
theorem natural_pair_card_bounds (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    let E := U K ⊓ B
    1 < Nat.card F ∧ E.relIndex B = Nat.card F ∧ Nat.card E ≤ Nat.card F ^ 2 := by
  let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let E := U K ⊓ B
  let : Finite F := Finite.of_surjective
    (fun s => (h.coordinates.parameter s).toAdd) h.coordinates.parameter_surjective
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hi : E.relIndex B = Nat.card F := by
    change (U K ⊓ (U K).map (MulAut.conj x⁻¹).toMonoidHom).relIndex B = _
    rw [← h.conjugate_fixed_intersection hx hnc,inf_relIndex_left]
    exact (h.indices hx hnc).conjugate
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) E B bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,hi,card_map_of_injective (MulAut.conj x⁻¹).injective] at hm
  have hu := natural_module_card_le h hn
  refine ⟨hq,hi,?_⟩
  rw [pow_succ] at hu
  nlinarith
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
