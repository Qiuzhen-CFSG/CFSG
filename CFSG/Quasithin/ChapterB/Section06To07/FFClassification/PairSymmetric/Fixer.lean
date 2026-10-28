module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.Fixer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Source

/-!
# The pointwise fixer on the actual source product layer

The genuine B.5.6 product intrinsically permutes its two factors under every
ambient conjugation. The faithful full quotient action and this proved
dichotomy identify an actor fixing the natural Thompson fixed space with an
actual element of the same transposition product. No separate ambient
factor-preservation or normalizer classification assumption is introduced.

Source: Aschbacher–Smith E.2.3(3), pp.216–217.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]

theorem source_mem_transposition_product
    (Y : Subgroup H) [Y.Normal] (α : Representation (ZMod 2) Y V)
    (d : SourceTwoFactorCase α) (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hcore : pCore 2 Y = ⊥)
    (ρ : Representation (ZMod 2) H (FivePair.Core × FivePair.Core)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : Y) v, ρ (g : H) v = FivePair.action (c.action.groupEquiv g) v)
    (x : H) (a b : Sym)
    (hfix : ∀ v ∈ fixedSpace FivePair.action
      (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)), ρ x v = v) :
    x ∈ (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
      ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
      (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) := by
  let e := c.action.groupEquiv
  let j := Y.subtype.comp e.symm.toMonoidHom
  let ψ : MulAut Y := MulAut.conjNormal x
  let φ : MulAut (Sym × Sym) := e.symm.trans (ψ.trans e)
  let f : (FivePair.Core × FivePair.Core) ≃ₗ[ZMod 2] (FivePair.Core × FivePair.Core) :=
    LinearEquiv.ofBijective (ρ x) (ρ.apply_bijective x)
  have hact (g : Sym × Sym) (v : FivePair.Core × FivePair.Core) :
      f (FivePair.action g v) = FivePair.action (φ g) (f v) := by
    have hg (g : Sym × Sym) (v : FivePair.Core × FivePair.Core) : ρ (j g) v = FivePair.action g v := by
      have hh := hnat (e.symm g) v
      change ρ (j g) v = FivePair.action (e (e.symm g)) v at hh
      rw [e.apply_symm_apply] at hh
      exact hh
    change ρ x (FivePair.action g v) = FivePair.action (φ g) (ρ x v)
    rw [←hg g v,←hg (φ g) (ρ x v)]
    have he : j (φ g) = x * j g * x⁻¹ := by
      change ((e.symm (e (ψ (e.symm g))) : Y) : H) = _
      rw [e.symm_apply_apply]
      rfl
    rw [he]
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have hmap (A : Subgroup (Sym × Sym)) :
      (A.map φ.toMonoidHom).map e.symm.toMonoidHom =
        (A.map e.symm.toMonoidHom).map ψ.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro g
    exact e.symm_apply_apply _
  have hperm :
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤) ∨
      (((⊤ : Subgroup Sym).prod ⊥).map φ.toMonoidHom = (⊥ : Subgroup Sym).prod ⊤ ∧
       ((⊥ : Subgroup Sym).prod ⊤).map φ.toMonoidHom = (⊤ : Subgroup Sym).prod ⊥) := by
    rcases d.automorphism_permutation hcore ψ with h | h
    · left
      constructor
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.first_eq]
        exact h.1
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.second_eq]
        exact h.2
    · right
      constructor
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.first_eq,c.second_eq]
        exact h.1
      · apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
        rw [hmap,c.second_eq,c.first_eq]
        exact h.2
  obtain ⟨g,hg,hgf⟩ := normalizer_fixer f φ hact hperm a b hfix
  refine ⟨g,hg,?_⟩
  apply hfaith
  apply LinearMap.ext
  intro v
  change ρ (j g) v = ρ x v
  have hh := hnat (e.symm g) v
  change ρ (j g) v = FivePair.action (e (e.symm g)) v at hh
  rw [e.apply_symm_apply] at hh
  exact hh.trans (hgf v).symm
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
