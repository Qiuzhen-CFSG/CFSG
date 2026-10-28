module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.BinaryPermutationNaturalStructure
/-!
# The actual A₆ natural coordinates on the block layer

The original normal module commutator is U(L), by the short-block support
lemma. Its image in the specified six-point natural module is a nonzero
A₆-subrepresentation. Native irreducibility therefore makes this image the
entire module, preserving conjugation on the original block layer.
Source: Aschbacher–Smith C.1.24(c), printed pp.130–131.
-/
public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
variable {G : Type*} [Group G] [Finite G]

theorem blockU_natural_six_coordinates
    (L V : Subgroup G) (hL : IsBlock L) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Equiv.Perm (Fin 6)) (hLq : L.map q = alternatingGroup (Fin 6))
    (e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (q g) (e v).toAdd)
    (hm : ⁅V,L⁆ ≠ ⊥) :
    ∃ E : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
      ∀ (l : L) (u : blockU L), (E (blockConjugate L l u)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (q l) (E u).toAdd := by
  let : IsElementaryAbelian 2 (blockU L) := hL.short.elementary
  have hU := ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator L V hL hm
  have hUV : (blockU L).map L.subtype ≤ V := hU ▸ commutator_le_left V L
  let i : blockU L →* V := {
    toFun u := ⟨u,hUV (mem_map_of_mem L.subtype u.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let f := e.toMonoidHom.comp i
  have hfi : Function.Injective f := by
    intro u v hh
    have hi := e.injective hh
    have hh : ((u : L) : G) = ((v : L) : G) := congrArg (fun x : V => (x : G)) hi
    exact Subtype.ext (Subtype.ext hh)
  have hact (l : L) (u : blockU L) :
      (f (blockConjugate L l u)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (q l) (f u).toAdd := by
    exact he l (i u)
  let fadd : Additive (blockU L) →+ BinaryPermutation.natural (Fin 6) := {
    toFun u := (f u.toMul).toAdd
    map_zero' := map_one f
    map_add' u v := map_mul f u.toMul v.toMul }
  let F := fadd.toZModLinearMap 2
  let W : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)) :=
    ⟨F.range, by
      intro a v hv
      obtain ⟨l,hl,hla⟩ := hLq.ge a.property
      obtain ⟨u,rfl⟩ := hv
      refine ⟨Additive.ofMul (blockConjugate L ⟨l,hl⟩ u.toMul),?_⟩
      change (f (blockConjugate L ⟨l,hl⟩ u.toMul)).toAdd = _
      rw [hact]
      rw [hla]
      rfl ⟩
  let : IsIrreducible (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)) :=
    BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  have hW : W = ⊤ := by
    rcases eq_bot_or_eq_top W with hbot | htop
    · exfalso
      apply hm
      rw [← hU]
      apply le_bot_iff.mp
      rintro x ⟨u,hu,rfl⟩
      have hz : F (Additive.ofMul (⟨u,hu⟩ : blockU L)) = 0 := by
        have hv : F (Additive.ofMul (⟨u,hu⟩ : blockU L)) ∈ W := ⟨_,rfl⟩
        rw [hbot] at hv
        exact hv
      have hfz : f ⟨u,hu⟩ = f 1 := by
        apply Multiplicative.toAdd.injective
        rw [map_one]
        exact hz
      have hu1 := congrArg (fun w : blockU L => ((w : L) : G)) (hfi hfz)
      exact hu1
    · exact htop
  have hfs : Function.Surjective f := by
    intro v
    have hv : v.toAdd ∈ W := by rw [hW]; trivial
    change ∃ u, F u = v.toAdd at hv
    obtain ⟨u,hu⟩ := hv
    exact ⟨u.toMul,congrArg Multiplicative.ofAdd hu⟩
  exact ⟨MulEquiv.ofBijective f ⟨hfi,hfs⟩,hact⟩
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
