module
public import Theory.SpecificGroups.SL2.NormalSylowFieldAction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# A binary rank-one automorphism fixing a Borel torus is inner

Full semilinear coverage writes an automorphism as an inner actor followed by
its coefficient automorphism. Trivial displacements on a Sylow normalizer
kill the coefficient. Pointwise fixation of a complement gives precisely
these displacements, since the normalizer is the product of its Sylow
subgroup and that complement. The second theorem transports the literal
Sylow and torus through any group isomorphism.

Source application: Aschbacher–Smith, Lemma 2.4.17(1), printed p.534.
-/

public section
open scoped MatrixGroups Pointwise
open Subgroup
namespace Matrix.ProjectiveSpecialLinearGroup

private theorem benderFieldAut_eq_fieldEquiv {F : Type*} [Field F] [CharP F 2]
    (σ : F ≃+* F) :
    BenderSuzuki.ZD.Linear.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g, rfl⟩ := BenderSuzuki.Converse.pi_surjective x
  rw [BenderSuzuki.ZD.Linear.fieldAut_apply_pi]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

/-- Trivial action on a Sylow normalizer quotient forces innerness. -/
theorem inner_of_normalizer_displacements (F : Type*) [Field F] [Finite F] [CharP F 2]
    (P : Sylow 2 PSL(2,F)) (α : MulAut PSL(2,F))
    (hP : (P : Subgroup PSL(2,F)).map α.toMonoidHom = P)
    (hd : ∀ x ∈ normalizer (P : Set PSL(2,F)), x⁻¹ * α x ∈ P) :
    α ∈ MulAut.innerSubgroup PSL(2,F) := by
  obtain ⟨g, σ, hg⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage α
  rw [benderFieldAut_eq_fieldEquiv] at hg
  have hs := Atlas.RankOneFieldAutomorphisms.NormalSylow.field_eq_one_of_normalizer_displacements
    F P g σ (hg ▸ hP) (hg ▸ hd)
  refine ⟨g, ?_⟩
  rw [hg, hs]
  change MulAut.conj g = MulAut.conj g * Atlas.RankOneFieldAutomorphisms.pslFieldAction 1
  rw [map_one, mul_one]

/-- Pointwise fixation of a Borel complement forces innerness. -/
theorem inner_of_torus_fixed {K : Type*} [Group K]
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : K ≃* PSL(2,F)) (P : Sylow 2 K) (D : Subgroup K) (α : MulAut K)
    (hDN : D ≤ normalizer (P : Set K))
    (hgen : (P : Subgroup K) ⊔ D = normalizer (P : Set K))
    (hP : (P : Subgroup K).map α.toMonoidHom = P)
    (hD : ∀ x ∈ D, α x = x) : α ∈ MulAut.innerSubgroup K := by
  have hd : ∀ x ∈ normalizer (P : Set K), x⁻¹ * α x ∈ P := by
    intro x hx
    rw [← hgen] at hx
    have hx' : x ∈ (P : Set K) * (D : Set K) :=
      (coe_mul_of_right_le_normalizer_left (P : Subgroup K) D hDN) ▸ hx
    obtain ⟨p,hp,d,hd,rfl⟩ := hx'
    change (p * d)⁻¹ * α (p * d) ∈ P
    rw [map_mul, hD d hd, _root_.mul_inv_rev]
    have hpp : p⁻¹ * α p ∈ P := (P : Subgroup K).mul_mem
      ((P : Subgroup K).inv_mem hp) (hP ▸ mem_map_of_mem α.toMonoidHom hp)
    have hn := (normalizer (P : Set K)).inv_mem (hDN hd)
    have hh := (mem_normalizer_iff.mp hn (p⁻¹ * α p)).mp hpp
    change d⁻¹ * p⁻¹ * (α p * d) ∈ (P : Subgroup K)
    simpa only [inv_inv, mul_assoc] using hh
  let : Finite K := Finite.of_equiv _ e.symm.toEquiv
  let Q : Sylow 2 PSL(2,F) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let β := MulAut.congr e α
  have hb : β ∈ MulAut.innerSubgroup PSL(2,F) := inner_of_normalizer_displacements F Q β (by
    change ((P : Subgroup K).map e.toMonoidHom).map β.toMonoidHom = _
    have he : β.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp α.toMonoidHom := by
      ext x
      exact congrArg e (congrArg α (e.symm_apply_apply x))
    rw [Subgroup.map_map, he, ← Subgroup.map_map, hP]
    rfl) (by
    intro x hx
    have hn : (normalizer (P : Set K)).map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) :=
      map_equiv_normalizer_eq _ e
    rw [← hn] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    change (e y)⁻¹ * e (α (e.symm (e y))) ∈ (P : Subgroup K).map e.toMonoidHom
    rw [e.symm_apply_apply, ← map_inv, ← map_mul]
    exact mem_map_of_mem _ (hd y hy))
  rw [← MulAut.map_innerSubgroup_congr e] at hb
  obtain ⟨a,ha,he⟩ := hb
  exact (MulAut.congr e).injective he ▸ ha
end Matrix.ProjectiveSpecialLinearGroup
