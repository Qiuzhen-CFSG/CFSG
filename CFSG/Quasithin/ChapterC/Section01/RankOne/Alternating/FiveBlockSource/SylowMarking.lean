module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.SourceConclusion
/-!
# Removing the coordinate Sylow marking

Conjugate the actual full Sylow to the standard eight-group, transporting
both the actor quotient and the original natural-module projection by the
same conjugation. The kernel and its fixed-space property remain literal.
The assembled source theorem therefore has no subgroup-image marking
premise, and applies to the original covered S₅ action.
Source: C.1.23(1), printed p.130.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB Theory.GroupTheory Theory.SpecificGroups.SymmetricFive
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Reposition the actual Sylow and all natural coordinates simultaneously.
The original module and projection kernel are preserved. -/
theorem exists_sylow_natural_marking (R : Sylow 2 H)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (L : Subgroup H) (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v) :
    ∃ (q' : H →* Equiv.Perm (Fin 5)) (hq' : Function.Surjective q')
      (hk' : q'.ker = centralizer (U : Set H))
      (p' : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)),
      (R : Subgroup H).map q' = OuterFourGeometry.eight ∧
      L.map q' = alternatingGroup (Fin 5) ∧ Function.Surjective p' ∧
      (∀ g v, p' (NormalElementaryQuotient.representation U q' hq' hk' g v) =
        BinaryPermutation.coreRepresentation (Fin 5) g (p' v)) ∧
      (∀ v, p' v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
        NormalElementaryQuotient.representation U q' hq' hk' g v = v) := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 5))
    (R.mapSurjective hq) OuterFourGeometry.standardSylow
  let f := (MulAut.conj a).toMonoidHom
  let q' := f.comp q
  have hq' : Function.Surjective q' := (MulAut.conj a).surjective.comp hq
  have hk' : q'.ker = centralizer (U : Set H) := by
    change (f.comp q).ker = _
    rw [MonoidHom.ker_comp_of_injective q f (MulAut.conj a).injective,hk]
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let ρ' := NormalElementaryQuotient.representation U q' hq' hk'
  let σ := BinaryPermutation.coreRepresentation (Fin 5)
  let p' := (σ a).comp p
  have hcompat (g : Equiv.Perm (Fin 5)) (v : Additive U) : ρ' (f g) v = ρ g v := by
    obtain ⟨x,rfl⟩ := hq g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply U q' hq' hk' x v).trans
      (NormalElementaryQuotient.representation_apply U q hq hk x v).symm
  have hR' : (R : Subgroup H).map q' = OuterFourGeometry.eight := by
    rw [←map_map]
    exact congrArg (fun S : Sylow 2 (Equiv.Perm (Fin 5)) => (S : Subgroup (Equiv.Perm (Fin 5)))) ha
  have hL' : L.map q' = alternatingGroup (Fin 5) := by
    rw [←map_map,hL]
    exact Normal.map_conj_eq _ a
  refine ⟨q',hq',hk',p',hR',hL',?_,?_,?_⟩
  · exact (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom a)).surjective.comp hp
  · intro g v
    obtain ⟨b,rfl⟩ := (MulAut.conj a).surjective g
    change σ a (p (ρ' (f b) v)) = σ (f b) (σ a (p v))
    rw [hcompat,he]
    change σ a (σ b (p v)) = σ (a*b*a⁻¹) (σ a (p v))
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  · intro v hv g hg
    have hpv : p v = 0 := (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom a)).injective (hv.trans (map_zero (σ a)).symm)
    let b := (MulAut.conj a).symm g
    have hb : b ∈ alternatingGroup (Fin 5) := by
      change a⁻¹*g*a ∈ alternatingGroup (Fin 5)
      exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem g hg a⁻¹
    have hg' : f b = g := (MulAut.conj a).apply_symm_apply g
    rw [←hg',hcompat]
    exact hfix v hpv b hb

/-- The marked covered-S₅ source conclusion retains the original component,
its module, the original pair, and its full Thompson commutator. -/
theorem source_conclusion
    (R : Sylow 2 H) (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann (R : Subgroup H)))
    (hD : D.Universal.{u,u}) (C : Subgroup H)
    (hC : C ≤ (center (R : Subgroup H)).map (R : Subgroup H).subtype)
    (hCD : C ≤ D.first.map (baumann (R : Subgroup H)).subtype) :
    C ≤ center H ∨ (D.second.map (baumann (R : Subgroup H)).subtype).Normal ∨
      (IsBlock L ∧ IsAlternatingBlock L 5 ∧
        L = ⁅L,elementaryAbelianMaxJ (R : Subgroup H)⁆ ∧
        (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U) := by
  obtain ⟨q',hq',hk',p',hR',hL',hp',he',hfix'⟩ :=
    exists_sylow_natural_marking R U q hq hk L hL p hp he hfix
  exact marked_source_conclusion R hfit L hcomp hprod eL U q' hq' hk' hR' hL'
    p' hp' he' hfix' hJ D hD C hC hCD

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
