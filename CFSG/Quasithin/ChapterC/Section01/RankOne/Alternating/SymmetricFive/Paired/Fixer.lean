module
public import Theory.Representation.BinaryPermutation.FivePairNormalizer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.Stable

/-!
# The full paired natural pointwise fixer

Each transposition four-group fixes a nonzero natural subspace. A linear
normalizer fixing their product fixed space cannot exchange the two actor
factors. Its actual permutation pair therefore lies in the two single-factor
pointwise fixers, which are exactly the original four-groups.

Source: Aschbacher–Smith C.1.24 and E.2.3(3), pp.130–131 and216–217.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open BinaryPermutation ChapterB.Offenders

private theorem nonzero_fixed_core (a : Sym) :
    ∃ v : FivePair.Core, v ≠ 0 ∧
      v ∈ fixedSpace (coreRepresentation (Fin 5)) ((D 5).map (MulAut.conj a).toMonoidHom) := by
  have hc := fixedCodim_add_finrank (coreRepresentation (Fin 5))
    ((D 5).map (MulAut.conj a).toMonoidHom)
  rw [fixedCodim_map_conj,Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl] at hc
  have hdim : Module.finrank (ZMod 2) (core (Fin 5)) = 4 := by simpa using finrank_core (Fin 5)
  rw [hdim] at hc
  have hp : 0 < Module.finrank (ZMod 2)
      (fixedSpace (coreRepresentation (Fin 5)) ((D 5).map (MulAut.conj a).toMonoidHom)) := by omega
  let := Module.nontrivial_of_finrank_pos hp
  obtain ⟨v,hv⟩ := exists_ne (0 : fixedSpace (coreRepresentation (Fin 5)) ((D 5).map (MulAut.conj a).toMonoidHom))
  exact ⟨v,fun h => hv (Subtype.ext h),v.property⟩

theorem normalizer_fixer
    (f : (FivePair.Core × FivePair.Core) ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core))
    (φ : MulAut (Sym × Sym))
    (hf : ∀ g v, f (FivePair.action g v) = FivePair.action (φ g) (f v))
    (hperm :
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤) ∨
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥))
    (a b : Sym)
    (hfixed : ∀ v ∈ fixedSpace FivePair.action
      (((D 5).map (MulAut.conj a).toMonoidHom).prod ((D 5).map (MulAut.conj b).toMonoidHom)),
      f v = v) :
    ∃ g ∈ (((D 5).map (MulAut.conj a).toMonoidHom).prod ((D 5).map (MulAut.conj b).toMonoidHom)),
      ∀ v, f v = FivePair.action g v := by
  have hleft (v : FivePair.Core) (hv : v ∈ fixedSpace (coreRepresentation (Fin 5))
      ((D 5).map (MulAut.conj a).toMonoidHom)) :
      (v,0) ∈ fixedSpace FivePair.action
        (((D 5).map (MulAut.conj a).toMonoidHom).prod ((D 5).map (MulAut.conj b).toMonoidHom)) := by
    intro g
    exact Prod.ext (hv ⟨g.val.1,g.property.1⟩) (map_zero (coreRepresentation (Fin 5) g.val.2))
  have hright (v : FivePair.Core) (hv : v ∈ fixedSpace (coreRepresentation (Fin 5))
      ((D 5).map (MulAut.conj b).toMonoidHom)) :
      (0,v) ∈ fixedSpace FivePair.action
        (((D 5).map (MulAut.conj a).toMonoidHom).prod ((D 5).map (MulAut.conj b).toMonoidHom)) := by
    intro g
    exact Prod.ext (map_zero (coreRepresentation (Fin 5) g.val.1)) (hv ⟨g.val.2,g.property.2⟩)
  obtain ⟨v,hv,hvfix⟩ := nonzero_fixed_core a
  obtain ⟨g,hg⟩ := FivePair.normalizer_of_fixed_axis f φ hf hperm v hv (hfixed (v,0) (hleft v hvfix))
  refine ⟨g,⟨?_,?_⟩,hg⟩
  · apply fixed_space_fixer_le_conjugate_D
    intro w hw
    have hh := hfixed (w,0) (hleft w hw)
    rw [hg] at hh
    exact congrArg Prod.fst hh
  · apply fixed_space_fixer_le_conjugate_D
    intro w hw
    have hh := hfixed (0,w) (hright w hw)
    rw [hg] at hh
    exact congrArg Prod.snd hh
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
