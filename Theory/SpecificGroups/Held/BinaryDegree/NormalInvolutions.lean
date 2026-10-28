module

public import Theory.SpecificGroups.Held.ThreeConjugates
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.BinaryDegree
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension
public import Theory.Representation.BinaryOffender.ConjugateDisplacement
public import Theory.Representation.NormalInvariants

/-!
# Involutions in a normal Held component

The checked Held automorphism realization supplies three conjugates of every
nontrivial involution in a self-centralizing normal Held subgroup.  Conjugate
generation and the faithful Held binary degree bound then give the fixed
codimension lower bound used by the quasithin residual argument.

Source: Aschbacher--Smith, the three-conjugate Held automorphism argument and
the binary degree estimate in G.7.1(2); the Section 15.2 consumer only needs
the specialized lower bound below.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Held.BinaryDegree
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem three_conjugates
    (K : Subgroup G) [K.Normal] (hc : centralizer (K : Set G) = ⊥)
    (e : K ≃* He) (a : G) (ha : a ≠ 1) (ha2 : a ^ 2 = 1) :
    ∃ g h : K, K ≤ zpowers a ⊔ zpowers (g.val * a * g.val⁻¹) ⊔
      zpowers (h.val * a * h.val⁻¹) := by
  let f : G →* MulAut He := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hc)
  have hinner (k : K) : f k.val = MulAut.conj (e k) := by
    change MulAut.congr e (MulAut.conjNormal k.val) = _
    rw [MulAut.conjNormal_val, MulAut.congr_conj]
  obtain ⟨g,h,hgen⟩ := threeConjugateAutomorphisms Realization.normalizer_surjective
    (f a) (fun he => ha (hf (he.trans f.map_one.symm)))
    (by rw [← map_pow,ha2,map_one])
  refine ⟨e.symm g,e.symm h,?_⟩
  apply (map_le_map_iff_of_injective hf).mp
  rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,
    MonoidHom.map_zpowers,MonoidHom.map_zpowers]
  simp only [map_mul,map_inv,hinner,e.apply_symm_apply]
  apply le_trans _ hgen
  rintro _ ⟨k,hk,rfl⟩
  exact ⟨e ⟨k,hk⟩, (hinner ⟨k,hk⟩).symm⟩

/-- A nontrivial involution in a group with a self-centralizing normal Held
subgroup moves at least fourteen dimensions in every faithful irreducible
binary representation of the whole group. -/
public theorem fourteen_le_fixedCodim_of_normal_held
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (K : Subgroup G) [K.Normal]
    (hc : centralizer (K : Set G) = ⊥) (e : K ≃* He)
    (a : G) (ha : a ≠ 1) (ha2 : a ^ 2 = 1) :
    14 ≤ fixedCodim ρ (zpowers a) := by
  let := hi
  have hK : K ≠ ⊥ := by
    intro hh
    have he : centralizer (K : Set G) = ⊤ := by
      rw [hh]
      exact centralizer_eq_top_iff_subset.mpr
        (show (⊥ : Subgroup G) ≤ center G from bot_le)
    have hG : (⊤ : Subgroup G) = ⊥ := he.symm.trans hc
    exact ha (mem_bot.mp (hG ▸ mem_top a))
  have hfix : fixedSpace ρ K = ⊥ := by
    by_contra hn
    have hk := ρ.le_ker_of_normal_invariants_ne_bot K hn
    apply hK
    apply le_bot_iff.mp
    intro k hk'
    exact hf ((hk hk').trans ρ.map_one.symm)
  obtain ⟨g,h,hgen⟩ := three_conjugates K hc e a ha ha2
  let c : Fin 3 → G := ![1,g.val,h.val]
  have hgen' : K ≤ closure (Set.range fun i => c i * a * (c i)⁻¹) := by
    apply hgen.trans
    refine sup_le (sup_le ?_ ?_) ?_
    · apply zpowers_le.mpr
      exact subset_closure ⟨0,by simp [c]⟩
    · apply zpowers_le.mpr
      exact subset_closure ⟨1,by simp [c]⟩
    · apply zpowers_le.mpr
      exact subset_closure ⟨2,by simp [c]⟩
  have hu := finrank_le_mul_fixedCodim_of_conjugate_generation ρ K hfix a c hgen'
  have hl := finrank_ge_fortyTwo ((ρ.comp K.subtype).comp e.symm.toMonoidHom)
    ((hf.comp K.subtype_injective).comp e.symm.injective)
  omega

end Held.BinaryDegree
