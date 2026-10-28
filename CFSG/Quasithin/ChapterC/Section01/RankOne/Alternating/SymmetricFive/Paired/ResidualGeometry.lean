module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.Stable
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.ResidualGeometry
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Residual conjugate generation for the two symmetric-five factors

The two-residual is the literal product of the two alternating groups. A
pair of even five-cycles joins the marked transposition products to the full
actor product. The corresponding fixed codimensions are four and eight;
these are the two-conjugate inputs for Baumann's argument on the source pair.

Source: Aschbacher--Smith B.2.18, C.1.24 and E.2.3(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open BinaryPermutation ChapterB.Offenders FiveCentralExtension

private theorem prod_sup_prod {G H : Type*} [Group G] [Group H]
    (A B : Subgroup G) (C D : Subgroup H) :
    A.prod C ⊔ B.prod D = (A ⊔ B).prod (C ⊔ D) := by
  apply le_antisymm (sup_le (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right))
  rw [prod_le_iff,Subgroup.map_sup,Subgroup.map_sup]
  constructor
  · apply sup_le
    · rintro _ ⟨a,ha,rfl⟩; exact mem_sup_left ⟨ha,C.one_mem⟩
    · rintro _ ⟨b,hb,rfl⟩; exact mem_sup_right ⟨hb,D.one_mem⟩
  · apply sup_le
    · rintro _ ⟨c,hc,rfl⟩; exact mem_sup_left ⟨A.one_mem,hc⟩
    · rintro _ ⟨d,hd,rfl⟩; exact mem_sup_right ⟨B.one_mem,hd⟩

private theorem prod_map_conj (A B : Subgroup Sym) (g h : Sym) :
    (A.prod B).map (MulAut.conj (g,h)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).prod (B.map (MulAut.conj h).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩; exact ⟨⟨a.1,ha.1,rfl⟩,⟨a.2,ha.2,rfl⟩⟩
  · rintro ⟨⟨a,ha,he⟩,⟨b,hb,hf⟩⟩; exact ⟨(a,b),⟨ha,hb⟩,Prod.ext he hf⟩

theorem paired_residual : pResidual 2 (Sym × Sym) =
    (alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 5)) := by
  have hsingle : pResidual 2 Sym = alternatingGroup (Fin 5) :=
    Equiv.Perm.twoResidual_eq_alternating (Fin 5)
  apply le_antisymm
  · intro x hx
    constructor
    · exact hsingle ▸ map_pResidual_le 2 (MonoidHom.fst Sym Sym) (mem_map_of_mem _ hx)
    · exact hsingle ▸ map_pResidual_le 2 (MonoidHom.snd Sym Sym) (mem_map_of_mem _ hx)
  · rw [prod_le_iff,←hsingle]
    exact ⟨map_pResidual_le 2 _,map_pResidual_le 2 _⟩

theorem exists_residual_conjugate_transposition_product (a b : Sym) :
    ∃ g ∈ pResidual 2 (Sym × Sym),
      (((D 5).map (MulAut.conj a).toMonoidHom).prod
        ((D 5).map (MulAut.conj b).toMonoidHom)) ⊔
      ((((D 5).map (MulAut.conj a).toMonoidHom).prod
        ((D 5).map (MulAut.conj b).toMonoidHom)).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  refine ⟨(a * fiveCycle * a⁻¹,b * fiveCycle * b⁻¹),?_,?_⟩
  · rw [paired_residual]
    exact ⟨conjugate_fiveCycle_even a,conjugate_fiveCycle_even b⟩
  · rw [prod_map_conj,prod_sup_prod,two_conjugate_four_groups_generate,
      two_conjugate_four_groups_generate,top_prod_top]

theorem fixedCodim_product (A B : Subgroup Sym) :
    fixedCodim FivePair.action (A.prod B) =
      fixedCodim (coreRepresentation (Fin 5)) A + fixedCodim (coreRepresentation (Fin 5)) B := by
  rw [fixedCodim_prod]
  change Module.finrank (ZMod 2) (Core ⧸ fixedSpace
    ((coreRepresentation (Fin 5)).comp (MonoidHom.fst Sym Sym)) _) +
    Module.finrank (ZMod 2) (Core ⧸ fixedSpace
    ((coreRepresentation (Fin 5)).comp (MonoidHom.snd Sym Sym)) _) = _
  rw [fixedSpace_comp_map,fixedSpace_comp_map]
  have hf : (A.prod B).map (MonoidHom.fst Sym Sym) = A := by
    ext x
    exact ⟨fun ⟨a,ha,hx⟩ => hx ▸ ha.1,fun hx => ⟨(x,1),⟨hx,B.one_mem⟩,rfl⟩⟩
  have hs : (A.prod B).map (MonoidHom.snd Sym Sym) = B := by
    ext x
    exact ⟨fun ⟨a,ha,hx⟩ => hx ▸ ha.2,fun hx => ⟨(1,x),⟨A.one_mem,hx⟩,rfl⟩⟩
  rw [hf,hs]
  rfl

theorem fixedCodim_transposition_product (a b : Sym) :
    fixedCodim FivePair.action (((D 5).map (MulAut.conj a).toMonoidHom).prod
      ((D 5).map (MulAut.conj b).toMonoidHom)) = 4 := by
  rw [fixedCodim_product,fixedCodim_map_conj,fixedCodim_map_conj,
    Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl]

theorem fixedCodim_residual_product : fixedCodim FivePair.action (pResidual 2 (Sym × Sym)) = 8 := by
  rw [paired_residual,fixedCodim_product,fixedCodim_alternating]
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
