module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.BlockDisplacement
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The core of the actual commuting short factors

Multiplication K×L→KL may have a central kernel. Shortness puts that kernel
inside O₂(K)×O₂(L), so it is a two-group. Prime-core lifting through this
literal multiplication map identifies O₂(KL) with O₂(K)O₂(L), without
assuming that the original factors are disjoint.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {K L : Subgroup G}

theorem short_commuting_core_product (hK : IsShort K) (hL : IsShort L)
    (hKL : L ≤ centralizer (K : Set G)) :
    (K ⊔ L).pCoreIn 2 = K.pCoreIn 2 ⊔ L.pCoreIn 2 := by
  have hc (k : K) (l : L) : Commute (k : G) (l : G) := hKL l.property k k.property
  let f : K × L →* G := K.subtype.noncommCoprod L.subtype hc
  have hfr : f.range = K ⊔ L := (MonoidHom.noncommCoprod_range K.subtype L.subtype hc).trans
    (by rw [range_subtype,range_subtype])
  let N := K ⊔ L
  let g : K × L →* N := f.codRestrict N (fun z => show f z ∈ K ⊔ L from hfr ▸ (show f z ∈ f.range from ⟨z,rfl⟩))
  have hg : Function.Surjective g := by
    intro n
    obtain ⟨z,hz⟩ := (show (n : G) ∈ f.range from hfr.symm ▸ n.property)
    exact ⟨z,Subtype.ext hz⟩
  have hker : IsPGroup 2 g.ker := by
    apply (pCore_isPGroup (p := 2) (G := K × L)).to_le
    rw [pCore_prod]
    rintro ⟨k,l⟩ hz
    have he : (k : G)*(l : G)=1 := congrArg Subtype.val hz
    have hkL : (k : G) ∈ L := by
      rw [eq_inv_of_mul_eq_one_left he]
      exact L.inv_mem l.property
    have hlK : (l : G) ∈ K := by
      rw [eq_inv_of_mul_eq_one_right he]
      exact K.inv_mem k.property
    constructor
    · rw [← hK.centralizer_blockU]
      intro u _
      exact Subtype.ext (hKL hkL u u.property)
    · rw [← hL.centralizer_blockU]
      intro u _
      exact Subtype.ext ((le_centralizer_iff.mp hKL) hlK u u.property)
  have hmap : (pCore 2 (K × L)).map g = pCore 2 N := by
    rw [← g.comap_pCore_of_ker_isPGroup hg hker,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective g hg]
    exact le_top
  have he : (pCore 2 (K × L)).map f = N.pCoreIn 2 := by
    calc
      _ = ((pCore 2 (K × L)).map g).map N.subtype := by rw [map_map]; rfl
      _ = _ := by rw [hmap]; rfl
  rw [← he,pCore_prod]
  apply le_antisymm
  · rintro z ⟨⟨k,l⟩,hkhl,rfl⟩
    exact mul_mem_sup (mem_map_of_mem K.subtype hkhl.1) (mem_map_of_mem L.subtype hkhl.2)
  · apply sup_le
    · rintro _ ⟨k,hk,rfl⟩
      exact ⟨(k,1),⟨hk,one_mem _⟩,mul_one _⟩
    · rintro _ ⟨l,hl,rfl⟩
      exact ⟨(1,l),⟨one_mem _,hl⟩,one_mul _⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
