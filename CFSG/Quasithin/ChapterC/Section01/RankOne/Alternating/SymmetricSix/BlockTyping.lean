module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.BlockTyping.Layer
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
/-!
# The literal A₆ block type in C.1.24(c)

The faithful natural action identifies the kernel on L with C_L(U(L))=O₂(L).
Its zero fixed space identifies U(L)/C_U(L) with the same native natural
module. These actual maps construct BlockModuleModel, retaining its quotient
map and conjugation identity. The final source adapter uses only the original
normal elementary module coordinates and nontrivial commutator; no additional
classification or action-kernel premise is imposed.
Source: Aschbacher–Smith C.1.24(c), printed pp.130–131.
-/
public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem natural_six_kernel_eq_centralizer
    (V : Subgroup G) [V.Normal]
    (q : G →* Equiv.Perm (Fin 6))
    (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd) :
    q.ker = centralizer (V : Set G) := by
  ext g
  constructor
  · intro hg v hv
    have hh := he g ⟨v,hv⟩
    rw [show q g = 1 from hg,map_one] at hh
    have hx := e.injective (Multiplicative.toAdd.injective hh)
    have hc : g*v*g⁻¹ = v := congrArg Subtype.val hx
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro hg
    change q g = 1
    apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := e.surjective (Multiplicative.ofAdd w)
    have hc : MulAut.conjNormal g v = v := by
      apply Subtype.ext
      change g*(v : G)*g⁻¹ = v
      rw [← hg v v.property,mul_inv_cancel_right]
    have hh := he g v
    rw [hc,hv] at hh
    rw [map_one]
    exact hh.symm

omit [Finite G] in
theorem isAlternatingBlock_of_six_layer_coordinates
    (L : Subgroup G) (hL : IsShort L)
    (q : G →* Equiv.Perm (Fin 6)) (hLq : L.map q = alternatingGroup (Fin 6))
    (E : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hE : ∀ (l : L) (u : blockU L), (E (blockConjugate L l u)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q l) (E u).toAdd) :
    IsAlternatingBlock L 6 := by
  let π := BinaryPermutation.naturalRepresentation (Fin 6)
  have hfaith : Function.Injective π := BinaryPermutation.naturalRepresentation_injective _ (by decide)
  let a : L →* alternatingGroup (Fin 6) :=
    (q.comp L.subtype).codRestrict _ (fun l => hLq ▸ mem_map_of_mem q l.property)
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨l,hl,he⟩ := hLq.ge x.property
    exact ⟨⟨l,hl⟩,Subtype.ext he⟩
  have hcore : a.ker = pCore 2 L := by
    rw [← hL.centralizer_blockU]
    ext l
    constructor
    · intro hl u hu
      have hql : q l = 1 := congrArg Subtype.val hl
      have he := hE l ⟨u,hu⟩
      rw [hql,map_one] at he
      have he' : blockConjugate L l ⟨u,hu⟩ = ⟨u,hu⟩ :=
        E.injective (Multiplicative.toAdd.injective he)
      have hc : l*u*l⁻¹ = u := congrArg Subtype.val he'
      exact (mul_inv_eq_iff_eq_mul.mp hc).symm
    · intro hl
      apply Subtype.ext
      change q l = 1
      apply hfaith
      apply LinearMap.ext
      intro v
      obtain ⟨u,hu⟩ := E.surjective (Multiplicative.ofAdd v)
      have hc : blockConjugate L l u = u := by
        apply Subtype.ext
        change l*(u : L)*l⁻¹ = u
        rw [← hl u u.property,mul_inv_cancel_right]
      have hh := hE l u
      rw [hc,hu] at hh
      rw [map_one]
      exact hh.symm
  have hfixed : blockFixed L = ⊥ := by
    have hz := Representation.BinaryOffender.fixedSpace_eq_bot_of_faithful_irreducible_on
      π (alternatingGroup (Fin 6)) hfaith
      (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
    apply le_bot_iff.mp
    intro u hu
    have hv : (E u).toAdd ∈ Representation.BinaryOffender.fixedSpace π (alternatingGroup (Fin 6)) := by
      intro b
      obtain ⟨l,hl⟩ := ha b
      have he := hE l u
      have hc : blockConjugate L l u = u := by
        apply Subtype.ext
        change l*(u : L)*l⁻¹ = u
        have hu' : (u : L) ∈ center L := hu
        have hc' : l * (u : L) = (u : L) * l := mem_center_iff.mp hu' l
        rw [hc',mul_inv_cancel_right]
      rw [hc] at he
      have hl' : q l = (b : Equiv.Perm (Fin 6)) := congrArg Subtype.val hl
      rw [hl'] at he
      exact he.symm
    rw [hz] at hv
    have he : E u = E 1 := by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      exact hv
    exact E.injective he
  let eQ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective a ha)
  let eU : BlockModule L ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    ((QuotientGroup.quotientMulEquivOfEq hfixed).trans QuotientGroup.quotientBot).trans E
  let ρ : alternatingGroup (Fin 6) →* MulAut (Multiplicative (BinaryPermutation.natural (Fin 6))) := {
    toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv (π.asGroupHom g.val)).toAddEquiv.toMultiplicative
    map_one' := by apply MulEquiv.ext; intro v; apply Multiplicative.toAdd.injective; change π 1 v.toAdd = v.toAdd; rw [map_one]; rfl
    map_mul' g h := by apply MulEquiv.ext; intro v; apply Multiplicative.toAdd.injective; change π (g.val*h.val) v.toAdd = π g.val (π h.val v.toAdd); rw [map_mul]; rfl }
  refine ⟨by decide,hL,ρ,⟨{ quotientIso := eQ, moduleIso := eU, intertwining := ?_ }⟩,fun _ _ => rfl⟩
  intro l u
  apply Multiplicative.toAdd.injective
  exact hE l u

theorem isAlternatingBlock_of_natural_six
    (L V : Subgroup G) (hL : IsBlock L) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Equiv.Perm (Fin 6)) (hLq : L.map q = alternatingGroup (Fin 6))
    (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hm : ⁅V,L⁆ ≠ ⊥) : IsAlternatingBlock L 6 := by
  obtain ⟨E,hE⟩ := blockU_natural_six_coordinates L V hL q hLq e he hm
  exact isAlternatingBlock_of_six_layer_coordinates L hL.short q hLq E hE
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
