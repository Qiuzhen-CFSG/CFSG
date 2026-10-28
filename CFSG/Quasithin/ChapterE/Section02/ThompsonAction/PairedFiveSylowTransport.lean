module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveIndices
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualControl
public import CFSG.Quasithin.ChapterB.Section02.Baumann.PairSpanSylow

/-!
# Source Sylow transport for the paired symmetric-five branch

The original residual factors generate O²(G), are normal in it, and are
permuted by every original ambient element. Their common quotient marking
puts Baum(T) in both normalizers. Apply the genuine componentwise C.1.24
Sylow extension inside the original maximal intersection, then transport
through the supplied source Sylow container. No module or factor-placement
assumption is added to the source action.

Source: Aschbacher–Smith E.2.3(3) and3.1.7, pp.216–217 and575–576.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The actual paired symmetric-five source gives the whole residual Sylow
in a prescribed source container. Individual factors need not be normal in G. -/
theorem paired_symmetric_residual_sylow_of_container
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (D R : Subgroup G) (hRT : R ≤ T)
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hBR : baumann (T : Subgroup G) ≤ R)
    (hR : Chapter1.IsSylowIn 2 R D)
    (hMD : minimalParabolicMax T hP ≤ normalizer (D : Set G)) :
    Chapter1.IsSylowIn 2 R (pResidual 2 G ⊔ R) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let K := factorResidual q Y d.first
  let L := factorResidual q Y d.second
  let := d.product.first_normal
  let := d.product.second_normal
  have hgen : K ⊔ L = pResidual 2 G :=
    paired_residual_factors_generate T hP U hU hJ q hq hker d
  have hKY : K ≤ Y.comap q := by
    intro x hx
    have hh : x ∈ factorPreimage q Y d.first := map_subtype_le _ hx
    exact map_subtype_le d.first hh
  have hLY : L ≤ Y.comap q := by
    intro x hx
    have hh : x ∈ factorPreimage q Y d.second := map_subtype_le _ hx
    exact map_subtype_le d.second hh
  have hKN : (K.subgroupOf (K ⊔ L)).Normal := normal_subgroupOf_of_le_normalizer
    ((sup_le hKY hLY).trans (factorResidual_normalized q Y d.first))
  let := hKN
  have hn : R ≤ normalizer ((K ⊔ L : Subgroup G) : Set G) := by
    rw [hgen]
    exact le_normalizer_of_normal
  obtain ⟨_,a,b,hB⟩ := paired_thompson_baumann_of_symmetric_model T hP U hU hJ q hq hker d c hexchange
  have hBY : (baumann (T : Subgroup G)).map q ≤ Y := by
    rw [hB,←map_map]
    exact map_subtype_le _
  have hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (map_le_iff_le_comap.mp hBY).trans (factorResidual_normalized q Y d.first)
  obtain ⟨Q,hQ,_,_,hspan⟩ := paired_component_index_two_sylow T hP U hU hJ q hq hker d c
    hexchange K (Set.mem_insert _ _)
  have hperm (g : G) : K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom = L := by
    rcases paired_residual_factors_permuted U hU q hq hker d g with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hex := paired_residual_factors_exchange T U q hq hker d hexchange
  have hs := sylow_sup_of_permuted_pair_span T K L D R
    (K ⊓ minimalParabolicMax T hP) Q hRT hTR hBR hR (inf_le_right.trans hMD)
    hn hBK hQ hspan hperm hex
  rwa [hgen] at hs
end CFSG.Quasithin.ChapterE.ThompsonAction
