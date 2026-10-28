module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionDefs
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import Theory.Quasithin.EvenCharacteristic

/-!
# Fixed subgroups and displacements of the actual automizer

Equal induced actions have the same centralizer inside B and the same
commutator with B. Sylow conjugacy in the original L then transports its
Sylow fixed subgroup to the distinguished intersection with T.

Source: Aschbacher--Smith, 6.1.11, printed p.670.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
variable {G : Type*} [Group G] {B A C L : Subgroup G}

theorem fixed_eq_of_induced_eq [IsElementaryAbelian 2 B]
    (hA : A ≤ normalizer (B : Set G)) (hC : C ≤ normalizer (B : Set G))
    (h : ChapterE.inducedAutomizer B A = ChapterE.inducedAutomizer B C) :
    B ⊓ centralizer (A : Set G) = B ⊓ centralizer (C : Set G) := by
  ext b
  simp only [mem_inf]
  by_cases hb : b ∈ B
  · simp only [hb,true_and]
    have hh := ChapterE.mem_fixedSpace_inducedAutomizer B A hA (Additive.ofMul ⟨b,hb⟩)
    rw [h] at hh
    exact hh.symm.trans (ChapterE.mem_fixedSpace_inducedAutomizer B C hC _)
  · simp only [hb,false_and]

theorem commutator_eq_of_induced_eq
    (hA : A ≤ normalizer (B : Set G)) (hC : C ≤ normalizer (B : Set G))
    (h : ChapterE.inducedAutomizer B A = ChapterE.inducedAutomizer B C) :
    ⁅B,A⁆ = ⁅B,C⁆ := by
  have hle (X Y : Subgroup G) (hX : X ≤ normalizer (B : Set G))
      (hXY : ChapterE.inducedAutomizer B X ≤ ChapterE.inducedAutomizer B Y) :
      ⁅X,B⁆ ≤ ⁅Y,B⁆ := by
    apply commutator_le.mpr
    intro x hx b hb
    have him : B.normalizerMonoidHom.rangeRestrict ⟨x,hX hx⟩ ∈
        ChapterE.inducedAutomizer B Y := hXY ⟨⟨x,hX hx⟩,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := him
    have heq := congrArg (fun a : ChapterE.Automizer B => (a.val ⟨b,hb⟩ : G)) he
    change (y : G) * b * (y : G)⁻¹ = x * b * x⁻¹ at heq
    have hh : ⁅x,b⁆ = ⁅(y : G),b⁆ := congrArg (· * b⁻¹) heq.symm
    rw [hh]
    exact commutator_mem_commutator hy hb
  rw [commutator_comm B A,commutator_comm B C]
  exact le_antisymm (hle A C hA h.le) (hle C A hC h.symm.le)

variable [Finite G]

theorem sylow_line_orbit (T : Sylow 2 G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hLB : L ≤ normalizer (B : Set G)) (P : Sylow 2 L) :
    ∃ l ∈ L, B ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G) =
      (B ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G)).map (MulAut.conj l).toMonoidHom := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  obtain ⟨l,hl⟩ := MulAction.exists_smul_eq L S P
  refine ⟨l,l.property,?_⟩
  have hmap : (P : Subgroup L).map L.subtype =
      ((T : Subgroup G) ⊓ L).map (MulAut.conj (l : G)).toMonoidHom := by
    rw [←hl]
    change ((S : Subgroup L).map (MulAut.conj l).toMonoidHom).map L.subtype = _
    rw [map_map]
    have he : L.subtype.comp (MulAut.conj l).toMonoidHom =
        (MulAut.conj (l : G)).toMonoidHom.comp L.subtype := rfl
    rw [he,←map_map,hS,subgroupOf_map_subtype,inf_comm]
  have hBn : B.map (MulAut.conj (l : G)).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp (hLB l.property)
  rw [map_inf _ _ _ (MulAut.conj (l : G)).injective,hBn]
  change B ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G) =
    B ⊓ (centralizer ((T : Subgroup G) ⊓ L : Set G)).map (MulAut.conj (l : G)).toMonoidHom
  exact (congrArg (fun X : Subgroup G => B ⊓ centralizer (X : Set G)) hmap).trans
    (congrArg (fun X : Subgroup G => B ⊓ X)
      (Theory.Quasithin.map_centralizer (MulAut.conj (l : G)) ((T : Subgroup G) ⊓ L))).symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
