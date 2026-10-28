module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalSource
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalOrthogonal

/-!
# The original noncyclic D.2.22 classification

Under the actual SQTK quotient, faithful action, F*=F, O₂=1,
V=[V,F] and Jhat=G hypotheses, a noncyclic starred actor is Sylow and
complements the three-core. The first branch is the natural Ω⁺₄ module,
with both its S₃ × S₃ isomorphism and the original action intertwining.
The second branch is the actual elementary group of order 27 extended by
the original elementary actor of order four, on the six-dimensional module.
The literal support factors and their action data are retained separately
by `source_noncyclic_global_configurations`.

No indecomposability premise is used in this noncyclic branch.
Source: Aschbacher–Smith D.2.22 and D.2.17(5),(6), printed pp.188–189.
-/

public section

namespace CFSG.Quasithin.ChapterD.SourceReduction
open Subgroup Representation.BinaryOffender Theory.GroupTheory FittingConfigurations
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
  (f : H →* G) (honto : Function.Surjective f)
  (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
  (hr : 1 < rank A)
  (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
  (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤)
  (hgen : Jhat ρ = ⊤)

include hH f honto hf hA hr hF hcore hmoved hgen in
/-- The original noncyclic D.2.22 endpoint, including the actual Ω⁺₄ action
in case (5) and the split elementary-three-by-four structure in case (6). -/
theorem source_lemma_D_2_22 :
    (∃ S : Sylow 2 G, (S : Subgroup G) = A) ∧
      IsCompl (pCore 3 G) A ∧ cubicRatio ρ = 3 / 2 ∧
      ((Module.finrank (ZMod 2) V = 4 ∧
        Nonempty (G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
        ∃ (c : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
          (e : G ≃* OrthogonalFourBinary.omega),
          ∀ g v, c (ρ g v) = (e g).val.val (c v)) ∨
       (Module.finrank (ZMod 2) V = 6 ∧ IsElementaryAbelian 3 (pCore 3 G) ∧
        Nat.card (pCore 3 G) = 27 ∧ IsElementaryAbelian 2 A ∧
        Nat.card A = 4 ∧ Nat.card G = 108)) := by
  obtain ⟨s,h,d,hd,hdim,hq,hS⟩ :=
    source_noncyclic_global_configurations ρ hH f honto hf hA hr hF hcore hmoved hgen
  let : IsElementaryAbelian 3 (pCore 3 G) := h.elementary
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hdis : Disjoint (pCore 3 G) A := IsPGroup.disjoint_of_coprime
    pCore_isPGroup (IsElementaryAbelian.isPGroup 2 A) (by decide)
  refine ⟨hS,⟨hdis,codisjoint_iff.mpr h.generated⟩,hq,?_⟩
  rcases hd with ⟨rfl,e,_,_⟩ | ⟨rfl,_⟩
  · refine Or.inl ⟨hdim,⟨e⟩,?_⟩
    apply d.exists_omega_coordinates ρ hf (d.factor_conj_closed ρ hf) e
    rw [hq]
    norm_num [ENNReal.lt_div_iff_mul_lt]
  · refine Or.inr ⟨hdim,h.elementary,h.card_core,inferInstance,h.card_actor,?_⟩
    have hc := card_sup_eq_mul_of_normalizes_of_disjoint (pCore 3 G) A
      le_normalizer_of_normal hdis
    rw [h.generated,card_top,h.card_core,h.card_actor] at hc
    exact hc

end CFSG.Quasithin.ChapterD.SourceReduction
