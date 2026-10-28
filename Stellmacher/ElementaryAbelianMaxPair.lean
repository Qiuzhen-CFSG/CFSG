module
public import Stellmacher.ElementaryAbelianMaxProduct
public import Stellmacher.ElementaryAbelianMaxOrder
/-! # The two maximum elementary subgroups in a Thompson product
Maximum elementary subgroups of S are exactly those of J(S). In a commuting
direct product, they split into maximum subgroups of its factors. Thus a
factor with exactly two maximum subgroups and an elementary centralizer
factor give exactly two maximum subgroups of the original S. Distinctness
is retained by the original disjoint factor inclusions.
Source application: Aschbacher--Smith 2.5.7, printed p.555.
-/
public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
variable {G:Type*} [Group G] [Finite G]
theorem maxFamily_thompson (S:Subgroup G) :
    elementaryAbelianMaxSubgroups (elementaryAbelianMaxJ S)=elementaryAbelianMaxSubgroups S := by
  have hJS : elementaryAbelianMaxJ S≤S:=sSup_le fun _ hA=>hA.1
  ext A
  constructor
  · intro hA
    obtain ⟨B,hB⟩:=elementaryAbelianMaxSubgroups_nonempty S
    refine ⟨hA.1.trans hJS,hA.2.1,?_⟩
    intro D hDS hD
    exact (hB.2.2 D hDS hD).trans (hA.2.2 B (le_sSup hB) hB.2.1)
  · intro hA
    exact ⟨le_sSup hA,hA.2.1,fun B hBJ hB=>hA.2.2 B (hBJ.trans hJS) hB⟩

theorem maxFamily_singleton (S:Subgroup G) [IsElementaryAbelian 2 S] :
    elementaryAbelianMaxSubgroups S={S} := by
  ext A
  constructor
  · intro hA
    exact Set.mem_singleton_iff.mpr (eq_of_le_of_card_ge hA.1 (hA.2.2 S le_rfl inferInstance))
  · rintro rfl
    exact ⟨le_rfl,inferInstance,fun B hB _=>Nat.card_le_card_of_injective
      (inclusion hB) (inclusion_injective hB)⟩

theorem maxFamily_eq_pair_of_cover (S V W:Subgroup G)
    (hV:V≤S) (hW:W≤S) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hc:Nat.card V=Nat.card W)
    (hcover:∀ A∈elementaryAbelianMaxSubgroups S,A≤V ∨ A≤W) :
    elementaryAbelianMaxSubgroups S={V,W} := by
  obtain ⟨A,hA⟩:=elementaryAbelianMaxSubgroups_nonempty S
  have hbound : Nat.card A≤Nat.card V := by
    rcases hcover A hA with hv | hw
    · exact Nat.card_le_card_of_injective (inclusion hv) (inclusion_injective hv)
    · rw [hc]
      exact Nat.card_le_card_of_injective (inclusion hw) (inclusion_injective hw)
  have hvmax : V∈elementaryAbelianMaxSubgroups S:=
    ⟨hV,inferInstance,fun B hBS hB=>(hA.2.2 B hBS hB).trans hbound⟩
  have hwmax : W∈elementaryAbelianMaxSubgroups S:=
    ⟨hW,inferInstance,fun B hBS hB=>(hvmax.2.2 B hBS hB).trans_eq hc⟩
  ext B
  constructor
  · intro hB
    rcases hcover B hB with hv | hw
    · exact Set.mem_insert_iff.mpr (Or.inl
        (eq_of_le_of_card_ge hv (hB.2.2 V hV inferInstance)))
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
        (eq_of_le_of_card_ge hw (hB.2.2 W hW inferInstance))))
  · rintro (rfl | rfl)
    · exact hvmax
    · exact hwmax

theorem maxFamily_pair_thompson_product (S K C V W:Subgroup G)
    (hJ:elementaryAbelianMaxJ S=K⊔C) (hd:Disjoint K C)
    (hc:K≤centralizer (C:Set G)) [IsElementaryAbelian 2 C]
    (hK:elementaryAbelianMaxSubgroups K={V,W}) :
    elementaryAbelianMaxSubgroups S={V⊔C,W⊔C} := by
  rw [←maxFamily_thompson S,hJ]
  ext A
  rw [maxFamily_sup_iff_of_disjoint_of_commuting K C hd hc A]
  simp only [hK,maxFamily_singleton C,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨B,rfl|rfl,D,rfl,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl|rfl)
    · exact ⟨V,Or.inl rfl,C,rfl,rfl⟩
    · exact ⟨W,Or.inr rfl,C,rfl,rfl⟩

omit [Finite G] in
theorem maxFamily_pair_equiv {X:Type*} [Group X]
    (K:Subgroup G) (e:X≃*K) (V W:Subgroup X)
    (h:elementaryAbelianMaxSubgroups (⊤:Subgroup X)={V,W}) :
    elementaryAbelianMaxSubgroups K=
      {V.map (K.subtype.comp e.toMonoidHom),W.map (K.subtype.comp e.toMonoidHom)} := by
  ext A
  rw [maxFamily_equiv_iff K e A]
  simp only [h,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨B,rfl|rfl,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl|rfl)
    · exact ⟨V,Or.inl rfl,rfl⟩
    · exact ⟨W,Or.inr rfl,rfl⟩

omit [Finite G] in
theorem sup_ne_of_disjoint_of_commuting (K C V W:Subgroup G)
    (hd:Disjoint K C) (hc:K≤centralizer (C:Set G))
    (hV:V≤K) (hW:W≤K) (hne:V≠W) : V⊔C≠W⊔C := by
  have hle (A B:Subgroup G) (hA:A≤K) (hB:B≤K) (he:A⊔C=B⊔C) : A≤B := by
    intro a ha
    have ha':a∈(B:Set G)*(C:Set G):=by
      rw [←coe_mul_of_right_le_normalizer_left B C
        ((le_centralizer_iff.mp (hB.trans hc)).trans (Subgroup.centralizer_le_normalizer _))]
      rw [←he]
      exact mem_sup_left ha
    obtain ⟨b,hb,c,hc',hbc⟩:=ha'
    have hcK:c∈K := by
      have ht:=K.mul_mem (K.inv_mem (hB hb)) (hA ha)
      rw [←hbc,inv_mul_cancel_left] at ht
      exact ht
    have hc1:c=1:=hd.le_bot ⟨hcK,hc'⟩
    have hba : b=a := by simpa only [hc1,mul_one] using hbc
    exact hba ▸ hb
  intro he
  exact hne (le_antisymm (hle V W hV hW he) (hle W V hW hV he.symm))

end Stellmacher

namespace Stellmacher
variable {G:Type*} [Group G] [Finite G]
theorem maxFamily_pair_thompson_equiv {X:Type*} [Group X]
    (S K C:Subgroup G) (e:X≃*K) (V W:Subgroup X)
    (hJ:elementaryAbelianMaxJ S=K⊔C) (hd:Disjoint K C)
    (hc:K≤centralizer (C:Set G)) [IsElementaryAbelian 2 C]
    (hX:elementaryAbelianMaxSubgroups (⊤:Subgroup X)={V,W}) (hne:V≠W) :
    let j:=K.subtype.comp e.toMonoidHom
    elementaryAbelianMaxSubgroups S={V.map j⊔C,W.map j⊔C} ∧
      V.map j⊔C≠W.map j⊔C := by
  dsimp only
  have hmap:=maxFamily_pair_equiv K e V W hX
  refine ⟨maxFamily_pair_thompson_product S K C _ _ hJ hd hc hmap,?_⟩
  apply sup_ne_of_disjoint_of_commuting K C _ _ hd hc
  · rintro _ ⟨v,hv,rfl⟩
    exact (e v).property
  · rintro _ ⟨v,hv,rfl⟩
    exact (e v).property
  · intro he
    apply hne
    exact Subgroup.map_injective (f:=K.subtype.comp e.toMonoidHom)
      (K.subtype_injective.comp e.injective) he
end Stellmacher
