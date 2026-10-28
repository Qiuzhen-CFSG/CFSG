module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Filtration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# The G₂ filtration on the original critical pair

Faithfulness of the literal U_H/V₁ action identifies Dγ with Uγ∩O₂(H).
Apply rank-nullity in H, first modulo O₂(H), then modulo U_H. The strict
layer is Dγ∩V_H < Dγ because V_H≤H_C and Dγ is not contained in H_C.
The actual critical-pair conjugator identifies the ranks of Uγ and U_H.
Thus contributions at least two, three and three contradict m(U_H)≤8.

Every quotient map is the displayed canonical projection, and all normality
is relative to H. The model and parabolic estimates are explicit earlier
inputs; they are not inferred from an unrelated group-family tag.

Source: Aschbacher–Smith 13.8.27, final paragraph, printed p.963.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceFiltration
open CriticalGeometry
open AlternatingAndLinear.FourStructure.CriticalTransfer

variable {G : Type*} [Group G] [Finite G] {L T H V V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [((Source.UH H V₃).subgroupOf H).Normal]

/-- The source filtration contradiction, on the actual critical pair. The
middle contribution is the literal image in H/U_H and the bottom one is the
actual intersection Dγ∩U_H. -/
theorem contradiction_of_source_bounds
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hf : Function.Injective ρ)
    (hUg : c.Ugamma V₃ ≤ H)
    (hUV : Source.UH H V₃ ≤ Source.VH H V)
    (hVC : Source.VH H V ≤ Source.HC H V₃)
    (hDC : ¬ Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ≤ Source.HC H V₃)
    (ha : 2 ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hm : 3 ≤ rank
      (((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.VH H V).subgroupOf H).map
        (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H))))
    (hb : 3 ≤ rank (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃))
    (hu : rank (Source.UH H V₃) ≤ 8) : False := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let q := QuotientGroup.mk' ((Source.UH H V₃).subgroupOf H)
  let A := (c.Ugamma V₃).subgroupOf H
  have hcore : (Source.QH H).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have hd : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).subgroupOf H = A ⊓ π.ker := by
    rw [s.Dgamma_eq_inf_core _ hUg hf]
    change ((c.Ugamma V₃).comap H.subtype ⊓ (Source.QH H).comap H.subtype) = _
    rw [show (Source.QH H).comap H.subtype = pCore 2 H from hcore, QuotientGroup.ker_mk']
    rfl
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hUg
  have hconj : A.map H.subtype = (q.ker.map H.subtype).map (MulAut.conj (c.gb : G)).toMonoidHom := by
    rw [map_subgroupOf_eq_of_le hUg, QuotientGroup.ker_mk', map_subgroupOf_eq_of_le s.le]
    rfl
  apply no_small_conjugate_filtration H.subtype H.subtype_injective (c.gb : G)
    π q A ((Source.VH H V).subgroupOf H) ((Source.HC H V₃).subgroupOf H) hconj
  · rw [QuotientGroup.ker_mk']
    exact comap_mono hUV
  · exact comap_mono hVC
  · intro h
    apply hDC
    intro x hx
    exact (hd.trans_le h) (show (⟨x, hUg (commutatorPreimage_le _ _ _ hx)⟩ : H) ∈
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).subgroupOf H from hx)
  · exact ha
  · rw [← hd]
    exact hm
  · rw [← hd, QuotientGroup.ker_mk']
    change 3 ≤ rank
      ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ ⊓ Source.UH H V₃).subgroupOf H)
    rw [rank_subgroupOf (inf_le_right.trans s.le)]
    exact hb
  · rw [QuotientGroup.ker_mk', rank_subgroupOf s.le]
    exact hu

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceFiltration
end
