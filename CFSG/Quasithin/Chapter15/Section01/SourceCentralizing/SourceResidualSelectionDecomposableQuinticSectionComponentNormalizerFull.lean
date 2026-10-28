module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.NormalOffenderClassification
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentSeparation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Full component normality from the classified offender normal closure

Complete B.5 permits at most two components in the actual normal closure
of a best offender. Every ambient conjugate of a component inside that
normal closure is still a component there. Its ambient conjugacy orbit
therefore has size at most two. Normalization by an actual Sylow two-subgroup
forces that orbit to have size one. No rank inequality for an arbitrary
quotient is used.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.SourceInduction
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite G] in
private theorem no_three_with_alignment (X Y A B C:Subgroup G)
    (hd:Disjoint X Y) (ha:A≠⊥) (hb:B≠⊥) (hc:C≠⊥)
    (hab:(A≤X∧B≤Y)∨(A≤Y∧B≤X))
    (hac:(A≤X∧C≤Y)∨(A≤Y∧C≤X))
    (hbc:(B≤X∧C≤Y)∨(B≤Y∧C≤X)) : False := by
  have hbot (D:Subgroup G) (hn:D≠⊥) (hX:D≤X) (hY:D≤Y) : False :=
    hn (le_bot_iff.mp ((le_inf hX hY).trans (disjoint_iff.mp hd).le))
  rcases hab with ⟨haX,hbY⟩ | ⟨haY,hbX⟩
  · rcases hac with ⟨_,hcY⟩ | ⟨haY,_⟩
    · rcases hbc with ⟨hbX,_⟩ | ⟨_,hcX⟩
      · exact hbot B hb hbX hbY
      · exact hbot C hc hcX hcY
    · exact hbot A ha haX haY
  · rcases hac with ⟨haX,_⟩ | ⟨_,hcX⟩
    · exact hbot A ha haX haY
    · rcases hbc with ⟨_,hcY⟩ | ⟨hbY,_⟩
      · exact hbot C hc hcX hcY
      · exact hbot B hb hbX hbY

omit [FiniteDimensional (ZMod 2) W] in
private theorem component_eq_one_of_two_of_adequate
    (ρ:Representation (ZMod 2) G W) (h:AdequateAlternative ρ)
    {A B C:Subgroup G} (hA:IsComponent G A) (hB:IsComponent G B)
    (hAB:A≠B) (hC:IsComponent G C) : C=A∨C=B := by
  by_cases hCA:C=A
  · exact Or.inl hCA
  by_cases hCB:C=B
  · exact Or.inr hCB
  exfalso
  rcases AdequateAlternative.product_rows_of_two_components ρ h hA hB hAB with hd|hd
  · obtain ⟨d⟩:=hd
    exact no_three_with_alignment d.first d.second A B C d.product.disjoint
      hA.isCComponent.ne_bot hB.isCComponent.ne_bot hC.isCComponent.ne_bot
      (d.component_alignment hA hB hAB) (d.component_alignment hA hC (fun he=>hCA he.symm))
      (d.component_alignment hB hC (fun he=>hCB he.symm))
  · obtain ⟨d⟩:=hd
    exact no_three_with_alignment d.first d.second A B C d.product.disjoint
      hA.isCComponent.ne_bot hB.isCComponent.ne_bot hC.isCComponent.ne_bot
      (d.component_alignment hA hB hAB) (d.component_alignment hA hC (fun he=>hCA he.symm))
      (d.component_alignment hB hC (fun he=>hCB he.symm))

/-- A Sylow-normalized moved component is normal, using the complete
classification of the actual best-offender normal closure. -/
theorem component_normal_of_sylow_normalizes_of_normalClosure_best
    (ρ:Representation (ZMod 2) G W) (hf:Function.Injective ρ)
    (hcore:pCore 2 G=⊥) (cover:SQTKQuotient KnownSimple.IsKnownSimple G)
    {A K:Subgroup G} (hA:IsBestOffender ρ A) (hK:IsComponent G K)
    (hKA:⁅K,A⁆=K) (S:Sylow 2 G) (hSN:(S:Subgroup G)≤normalizer (K:Set G)) :
    K.Normal := by
  classical
  let N:=normalClosure (A:Set G)
  obtain ⟨hKN,_,hKNc⟩:=moved_component_in_normalClosure ρ hf hK hA hKA
  have hclass:AdequateAlternative (ρ.comp N.subtype):=
    Or.inr (normalClosure_adequateAlternative ρ hf hcore cover hA)
  have hconj (g:G):K.map (MulAut.conj g).toMonoidHom≤N := by
    rintro _ ⟨k,hk,rfl⟩
    exact (inferInstance:N.Normal).conj_mem k (hKN hk) g
  by_contra hn
  have hex:∃g:G,K.map (MulAut.conj g).toMonoidHom≠K := by
    by_contra! hh
    exact hn (normal_iff_map_conj_eq.mpr hh)
  obtain ⟨g,hg⟩:=hex
  let L:=K.map (MulAut.conj g).toMonoidHom
  have hL:IsComponent G L:=hK.map_conj g
  have hKL:K.subgroupOf N≠L.subgroupOf N := by
    intro he
    have hh:=congrArg (map N.subtype) he
    rw [map_subgroupOf_eq_of_le hKN,map_subgroupOf_eq_of_le (hconj g)] at hh
    exact hg hh.symm
  have hpair (t:G):K.map (MulAut.conj t).toMonoidHom=K∨
      K.map (MulAut.conj t).toMonoidHom=L := by
    have hh:=component_eq_one_of_two_of_adequate (ρ.comp N.subtype) hclass
      hKNc (hL.subgroupOf (hconj g)) hKL ((hK.map_conj t).subgroupOf (hconj t))
    rcases hh with hh|hh
    · exact Or.inl (by
        have he:=congrArg (map N.subtype) hh
        change ((K.map (MulAut.conj t).toMonoidHom).subgroupOf N).map N.subtype =
          (K.subgroupOf N).map N.subtype at he
        rw [map_subgroupOf_eq_of_le (hconj t),map_subgroupOf_eq_of_le hKN] at he
        exact he)
    · exact Or.inr (by
        have he:=congrArg (map N.subtype) hh
        change ((K.map (MulAut.conj t).toMonoidHom).subgroupOf N).map N.subtype =
          (L.subgroupOf N).map N.subtype at he
        rw [map_subgroupOf_eq_of_le (hconj t),map_subgroupOf_eq_of_le (hconj g)] at he
        exact he)
  have hi:(normalizer (K:Set G)).index≤2 := by
    rw [←ncard_conjugates_eq_index_normalizer]
    have hs:(Set.range fun t:G=>K.map (MulAut.conj t).toMonoidHom)⊆{K,L} := by
      rintro _ ⟨t,rfl⟩
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hpair t
    exact (Set.ncard_le_ncard hs).trans_eq (Set.ncard_pair hg.symm)
  have hlo:1<(normalizer (K:Set G)).index :=
    (normalizer (K:Set G)).one_lt_index_of_ne_top
      (fun he=>hn (normalizer_eq_top_iff.mp he))
  have he:(normalizer (K:Set G)).index=2:=by omega
  have hdiv:=index_dvd_of_le hSN
  rw [he] at hdiv
  exact S.not_dvd_index hdiv

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
