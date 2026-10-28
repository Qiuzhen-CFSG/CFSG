module

public import Theory.Representation.SL3DoubledNaturalOffenders
public import Theory.Representation.PSL3Two.DoubledFixedSpace
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.Pi

/-!
# The full normalizer of the doubled binary three-space

The explicit `Fin 2`/product equivalence transports the general doubled-natural
SL₃ normalizer theorems to the literal action `W.prod W`. In particular every
offender lies in the diagonal component. Tensor factorization also proves that
the full normalizer's pointwise fixer of the marked radical's fixed space is
exactly that radical: fixation forces the multiplicity matrix to be the identity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.10(2)
and the doubled-natural branch of 13.6.20, printed pp.109 and 931.
-/

@[expose] public section
open Matrix Representation Representation.BinaryOffender Subgroup
noncomputable section
namespace BinaryLinearThree.DoubledOffenders
abbrev D := (Module.End (ZMod 2) (Vector × Vector))ˣ
abbrev δ : Group →* D := (W.prod W).asGroupHom
abbrev τ : Representation (ZMod 2) D (Vector × Vector) := Units.coeHom _
abbrev N : Subgroup D := normalizer (δ.range : Set D)
abbrev radical : Subgroup D := R.map δ


private def coordinates : SL3DoubledNaturalOffenders.Space (ZMod 2) ≃ₗ[ZMod 2] (Vector × Vector) :=
  LinearEquiv.finTwoArrow (ZMod 2) Vector

private def transport : SL3DoubledNaturalOffenders.Ambient (ZMod 2) ≃* D :=
  LinearMap.GeneralLinearGroup.congrLinearEquiv coordinates

private lemma transport_representation (g : Group) :
    transport ((SL3DoubledNaturalOffenders.representation (ZMod 2)).asGroupHom g) = δ g := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  rfl

private lemma component_map : (SL3DoubledNaturalOffenders.component (ZMod 2)).map transport.toMonoidHom = δ.range := by
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, transport_representation g⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨g, rfl⟩, transport_representation g⟩

private lemma normalizer_map : (SL3DoubledNaturalOffenders.normalizer (ZMod 2)).map transport.toMonoidHom = N := by
  rw [SL3DoubledNaturalOffenders.normalizer, map_equiv_normalizer_eq, component_map]

private lemma mem_model_normalizer (x : D) (hx : x ∈ N) :
    transport.symm x ∈ SL3DoubledNaturalOffenders.normalizer (ZMod 2) := by
  rw [← normalizer_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

lemma δ_injective : Function.Injective δ := by
  intro g h he
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact congrArg (fun x : D => (τ x (v, 0)).1) he

lemma fixedSpace_radical : fixedSpace τ radical = fixedSpace (W.prod W) R :=
  (fixedSpace_comp_map τ δ R).symm

lemma radical_isOffender : IsOffender τ radical :=
  DoubledFixedSpace.radical_isOffender.map_equivariant (W.prod W) τ δ δ_injective
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

lemma offender_le_component {E : Subgroup D} (hE : IsOffender τ E) (hEN : E ≤ N) :
    E ≤ δ.range := by
  have he : IsOffender (SL3DoubledNaturalOffenders.action (ZMod 2)) (E.map transport.symm.toMonoidHom) :=
    hE.map_equivariant τ (SL3DoubledNaturalOffenders.action (ZMod 2)) transport.symm.toMonoidHom
      transport.symm.injective coordinates.symm (by
        intro g v
        rfl)
  have hn : E.map transport.symm.toMonoidHom ≤ SL3DoubledNaturalOffenders.normalizer (ZMod 2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_model_normalizer x (hEN hx)
  have hc := SL3DoubledNaturalOffenders.offender_le_component_of_le_normalizer
    (F := ZMod 2) (m := 1) (by simp) (by decide) (by decide) he hn
  intro x hx
  rw [← component_map]
  exact ⟨transport.symm x, hc (mem_map_of_mem _ hx), transport.apply_symm_apply x⟩

lemma normalizer_block_form (x : D) (hx : x ∈ N) :
    ∃ g : Group, ∃ a b c d : ZMod 2, ∀ u : Vector × Vector,
      τ x u = (a • W g u.1 + b • W g u.2, c • W g u.1 + d • W g u.2) := by
  obtain ⟨g, q, he⟩ := SL3DoubledNaturalOffenders.normalizer_linear_tensor_factors
    (transport.symm x) (mem_model_normalizer x hx) (fun a v => map_smul _ a v)
  obtain ⟨g', hg⟩ := Matrix.PSL3Two.toGL_surjective g
  refine ⟨g', q.val 0 0, q.val 0 1, q.val 1 0, q.val 1 1, fun u => ?_⟩
  have hg' : g'.val = g.val := congrArg Units.val hg
  have h0 := he (coordinates.symm u) 0
  have h1 := he (coordinates.symm u) 1
  apply Prod.ext
  · change (τ x u).1 = g.val.mulVec (q.val 0 0 • u.1 + q.val 0 1 • u.2) at h0
    rw [← hg', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at h0
    exact h0
  · change (τ x u).2 = g.val.mulVec (q.val 1 0 • u.1 + q.val 1 1 • u.2) at h1
    rw [← hg', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at h1
    exact h1
lemma fixes_fixedSpace_iff (x : D) (hx : x ∈ N) :
    (∀ u ∈ fixedSpace τ radical, τ x u = u) ↔ x ∈ radical := by
  constructor
  · intro hf
    obtain ⟨g, a, b, c, d, he⟩ := normalizer_block_form x hx
    have hm : (![1,0,0], (0 : Vector)) ∈ fixedSpace τ radical := by
      rw [fixedSpace_radical, DoubledFixedSpace.mem_fixedSpace_iff]
      exact ⟨rfl, rfl⟩
    have hm' : ((0 : Vector), ![1,0,0]) ∈ fixedSpace τ radical := by
      rw [fixedSpace_radical, DoubledFixedSpace.mem_fixedSpace_iff]
      exact ⟨rfl, rfl⟩
    have h0 := hf _ hm
    have h1 := hf _ hm'
    rw [he] at h0 h1
    have hne : W g (![1,0,0] : Vector) ≠ 0 := by
      intro hz
      have hz' := (LinearMap.GeneralLinearGroup.toLinearEquiv (W.asGroupHom g)).injective
        (hz.trans (map_zero (W g)).symm)
      exact (by decide : (![1,0,0] : Vector) ≠ 0) hz'
    have binary (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide
    have ha : a = 1 := by
      rcases binary a with ha | ha
      · have hc := congrArg (fun u : Vector × Vector => u.1 0) h0
        simp [ha] at hc
      · exact ha
    have hd : d = 1 := by
      rcases binary d with hd | hd
      · have hc := congrArg (fun u : Vector × Vector => u.2 0) h1
        simp [hd] at hc
      · exact hd
    have hb : b = 0 := by
      have hb' : b • W g (![1,0,0] : Vector) = 0 := by
        simpa using congrArg Prod.fst h1
      exact (smul_eq_zero.mp hb').resolve_right hne
    have hc : c = 0 := by
      have hc' : c • W g (![1,0,0] : Vector) = 0 := by
        simpa using congrArg Prod.snd h0
      exact (smul_eq_zero.mp hc').resolve_right hne
    have hxg : x = δ g := by
      apply Units.ext
      apply LinearMap.ext
      intro u
      change τ x u = (W g u.1, W g u.2)
      simpa [ha, hb, hc, hd] using he u
    rw [hxg] at hf ⊢
    refine mem_map_of_mem δ ((DoubledFixedSpace.fixes_fixedSpace_iff g).mp ?_)
    intro u hu
    have hu' : u ∈ fixedSpace τ radical := fixedSpace_radical.symm ▸ hu
    exact hf u hu'
  · intro hx' u hu
    exact hu ⟨x, hx'⟩
end BinaryLinearThree.DoubledOffenders
