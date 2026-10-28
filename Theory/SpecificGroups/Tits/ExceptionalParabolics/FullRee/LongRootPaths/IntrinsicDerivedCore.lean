module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.CollectedDerivedCore
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedActionCertificate

/-!
# The intrinsic derived subgroup of the actual second Ree core

The collected subgroup is normalized by the eight genuine core generators.
Their pairwise commutators lie in it, and its own generators are products
of those commutators. Hence it is exactly the derived subgroup of the actual
second core. Its center bound and the marked short-root membership survive
this intrinsic identification. Source: J.4.7, printed p.444.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.IntrinsicDerivedCore
open Subgroup ReeF4 RootRelations
open DerivedCoreCertificate DerivedOuterAction DerivedActionCertificate
open scoped commutatorElement

/-- The collected subgroup included through the canonical faithful embedding. -/
def D : Subgroup (Model 0) := CollectedDerivedCore.group.map atlasEmbedding

private theorem word_mem (n:Fin 64) : atlasEmbedding (word n)∈D :=
  mem_map_of_mem _ (CollectedDerivedCore.word_mem n)
private theorem gen_mem (i:Fin 6) : atlasEmbedding (gen i)∈D :=
  mem_map_of_mem _ (CollectedDerivedCore.gen_mem i)

private theorem root_mem_core (i:Fin 7) : atlasEmbedding (root i)∈secondCore := by
  fin_cases i <;> unfold root <;>
    exact generator_mem_secondCore _ (by decide) (by decide) (by decide)

private theorem gen_mem_core (i:Fin 6) : atlasEmbedding (gen i)∈secondCore := by
  have h:=root_mem_core
  fin_cases i
  · change atlasEmbedding (root 0*root 1*(root 2)^2)∈secondCore
    rw [map_mul,map_mul,map_pow]
    exact secondCore.mul_mem (secondCore.mul_mem (h 0) (h 1)) (secondCore.pow_mem (h 2) 2)
  · exact h 3
  · change atlasEmbedding (root 0*(root 4)^2)∈secondCore
    rw [map_mul,map_pow]
    exact secondCore.mul_mem (h 0) (secondCore.pow_mem (h 4) 2)
  · exact h 1
  · exact h 5
  · change atlasEmbedding ((root 2)^3*root 4)∈secondCore
    rw [map_mul,map_pow]
    exact secondCore.mul_mem (secondCore.pow_mem (h 2) 3) (h 4)

private theorem D_le_core : D≤secondCore := by
  rw [D,map_le_iff_le_comap,CollectedDerivedCore.group]
  apply (closure_le _).mpr
  intro a ha
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact gen_mem_core _

private theorem normalizes_of_gen (x:Model 0)
    (h:∀i:Fin 6,x*atlasEmbedding (gen i)*x⁻¹∈D) : x∈normalizer (D:Set (Model 0)) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap,D,map_le_iff_le_comap,CollectedDerivedCore.group]
    apply (closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact h _
  · rw [card_map_of_injective (MulAut.conj x).injective]

private theorem root_inv (i:Fin 7) : (root i)⁻¹=(root i)^3 := by
  calc (root i)⁻¹=(root i)⁻¹*1 := (mul_one _).symm
       _ = (root i)⁻¹*(root i)^4 := congrArg _ (root_four i).symm
       _ = (root i)^3 := by group

private theorem root_normalizes (i:Fin 7) :
    atlasEmbedding (root i)∈normalizer (D:Set (Model 0)) := by
  apply normalizes_of_gen
  intro j
  have hh:=congrArg atlasEmbedding (root_conjugates_collected i j)
  rw [← root_inv] at hh
  simp only [map_mul,map_inv] at hh
  rw [hh]
  exact word_mem (normalIndex i j)

private theorem q_acts_gen (i:Fin 6) :
    (MulAut.conj q) (atlasEmbedding (gen i))=atlasEmbedding (actedGen i) := by
  have h (j:Fin 7) : (MulAut.conj q) (atlasEmbedding (root j))=atlasEmbedding (actionWord j) :=
    q_conjugates_root j
  fin_cases i
  · change (MulAut.conj q) (atlasEmbedding (root 0*root 1*(root 2)^2))=
      atlasEmbedding (actionWord 0*actionWord 1*(actionWord 2)^2)
    simp only [map_mul,map_pow,h]
  · exact h 3
  · change (MulAut.conj q) (atlasEmbedding (root 0*(root 4)^2))=
      atlasEmbedding (actionWord 0*(actionWord 4)^2)
    simp only [map_mul,map_pow,h]
  · exact h 1
  · exact h 5
  · change (MulAut.conj q) (atlasEmbedding ((root 2)^3*root 4))=
      atlasEmbedding ((actionWord 2)^3*actionWord 4)
    simp only [map_mul,map_pow,h]

private theorem q_normalizes : q∈normalizer (D:Set (Model 0)) := by
  apply normalizes_of_gen
  intro i
  change (MulAut.conj q) (atlasEmbedding (gen i))∈D
  rw [q_acts_gen,outer_conjugates_collected]
  exact word_mem _

private theorem core_normalizes : secondCore≤normalizer (D:Set (Model 0)) := by
  rw [secondCore_eq_closure]
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact q_normalizes
  · exact root_normalizes 0
  · exact root_normalizes 1
  · exact root_normalizes 2
  · exact root_normalizes 3
  · exact root_normalizes 4
  · exact root_normalizes 5
  · exact root_normalizes 6

private theorem outer_commutator_eq (i:Fin 7) :
    ⁅q,atlasEmbedding (root i)⁆=atlasEmbedding (word (outerIndex i)) := by
  change (q*atlasEmbedding (root i)*q⁻¹)*(atlasEmbedding (root i))⁻¹=_
  rw [q_conjugates_root,← map_inv,root_inv,← map_mul,outer_commutator]

private theorem root_commutator_eq (i j:Fin 7) (hij:i<j) :
    ⁅atlasEmbedding (root i),atlasEmbedding (root j)⁆=
      atlasEmbedding (word (commutatorIndex i j)) := by
  rw [← map_commutatorElement]
  change atlasEmbedding (root i*root j*(root i)⁻¹*(root j)⁻¹)=_
  rw [root_inv,root_inv,root_commutator i j hij]

private theorem root_commutator_mem (i j:Fin 7) :
    ⁅atlasEmbedding (root i),atlasEmbedding (root j)⁆∈D := by
  rcases lt_trichotomy i j with h|rfl|h
  · rw [root_commutator_eq i j h]
    exact word_mem _
  · simp
  · have hi:⁅atlasEmbedding (root i),atlasEmbedding (root j)⁆=
        ⁅atlasEmbedding (root j),atlasEmbedding (root i)⁆⁻¹ := by group
    rw [hi,root_commutator_eq j i h]
    exact D.inv_mem (word_mem _)

private theorem core_generator_commutator (i j:Fin 8) : ⁅coreGenerator i,coreGenerator j⁆∈D := by
  have h0:coreGenerator 0=q := rfl
  have hs (k:Fin 7) : coreGenerator k.succ=atlasEmbedding (root k) := by fin_cases k <;> rfl
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp
    | succ j => rw [h0,hs,outer_commutator_eq]; exact word_mem _
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [hs,h0]
      have he:⁅atlasEmbedding (root i),q⁆=⁅q,atlasEmbedding (root i)⁆⁻¹ := by group
      rw [he,outer_commutator_eq]
      exact D.inv_mem (word_mem _)
    | succ j => rw [hs,hs]; exact root_commutator_mem i j


private theorem derived_le_D : ⁅secondCore,secondCore⁆≤D := by
  let J:=D.subgroupOf secondCore
  let : J.Normal:=normal_subgroupOf_of_le_normalizer core_normalizes
  let g (i:Fin 8) : secondCore := ⟨coreGenerator i, by
    rw [secondCore_eq_closure]
    exact subset_closure ⟨i,rfl⟩⟩
  have hg : closure (Set.range g)=⊤ := by
    apply map_injective secondCore.subtype_injective
    rw [MonoidHom.map_closure,← Set.range_comp,← MonoidHom.range_eq_map,range_subtype]
    exact secondCore_eq_closure.symm
  let f:=QuotientGroup.mk' J
  have hc : IsMulCommutative ((closure (Set.range g)).map f) := by
    rw [MonoidHom.map_closure]
    apply isMulCommutative_closure
    rintro _ ⟨x,⟨i,rfl⟩,rfl⟩ _ ⟨y,⟨j,rfl⟩,rfl⟩
    rw [← commutatorElement_eq_one_iff_mul_comm,← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (core_generator_commutator i j)
  have he : (_root_.commutator secondCore).map f=⊥ := by
    rw [_root_.commutator_def,← hg,map_commutator]
    exact commutator_self_eq_bot_iff.mpr hc
  have hl : _root_.commutator secondCore≤J := by
    simpa only [f,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  have hm:=map_mono (f:=secondCore.subtype) hl
  rwa [map_subtype_commutator,map_subgroupOf_eq_of_le D_le_core] at hm

private theorem D_le_derived : D≤⁅secondCore,secondCore⁆ := by
  let C:=⁅secondCore,secondCore⁆
  have ho (i:Fin 7) : atlasEmbedding (word (outerIndex i))∈C := by
    rw [← outer_commutator_eq]
    exact commutator_mem_commutator q_mem_secondCore (root_mem_core i)
  have hr (i j:Fin 7) (hij:i<j) : atlasEmbedding (word (commutatorIndex i j))∈C := by
    rw [← root_commutator_eq i j hij]
    exact commutator_mem_commutator (root_mem_core i) (root_mem_core j)
  have h0 : atlasEmbedding (gen 0)∈C := by
    simpa [outerIndex,word] using ho 3
  have h1 : atlasEmbedding (gen 1)∈C := by
    simpa [commutatorIndex,word] using hr 2 5 (by decide)
  have h2 : atlasEmbedding (gen 2)∈C := by
    have hh:atlasEmbedding (gen 1)*atlasEmbedding (gen 2)∈C := by
      simpa [outerIndex,word,map_mul] using ho 5
    exact (C.mul_mem_cancel_left h1).mp hh
  have h3 : atlasEmbedding (gen 3)∈C := by
    simpa [outerIndex,word] using ho 2
  have h4 : atlasEmbedding (gen 4)∈C := by
    rw [fourth_generator_witness,map_mul,map_mul]
    exact C.mul_mem (C.mul_mem (by simpa [outerIndex] using ho 3)
      (by simpa [commutatorIndex] using hr 4 6 (by decide)))
      (by simpa [outerIndex] using ho 6)
  have h5 : atlasEmbedding (gen 5)∈C := by
    rw [last_generator_witness,map_inv]
    exact C.inv_mem (by simpa [outerIndex] using ho 6)
  rw [D,map_le_iff_le_comap,CollectedDerivedCore.group]
  apply (closure_le _).mpr
  intro a ha
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
  · exact h5
  · exact h4
  · exact h3
  · exact h2
  · exact h1
  · exact h0

/-- The small collected subgroup is the intrinsic derived subgroup. -/
theorem D_eq_derived : D=⁅secondCore,secondCore⁆ := le_antisymm D_le_derived derived_le_D

/-- The derived subgroup of the actual second core has order sixty-four. -/
theorem derived_card : Nat.card (⁅secondCore,secondCore⁆ : Subgroup (Model 0))=64 := by
  rw [← D_eq_derived,D,card_map_of_injective atlasEmbedding_injective]
  exact CollectedDerivedCore.card_group

/-- Its center has order at most eight. -/
theorem derived_center_card : Nat.card (center (⁅secondCore,secondCore⁆ : Subgroup (Model 0)))≤8 := by
  rw [← D_eq_derived]
  let e:=CollectedDerivedCore.group.equivMapOfInjective atlasEmbedding atlasEmbedding_injective
  change Nat.card (center (CollectedDerivedCore.group.map atlasEmbedding))≤8
  rw [← Nat.card_congr (centerCongr e).toEquiv]
  exact CollectedDerivedCore.card_center_le

/-- The original short-root word lies in the center of this derived subgroup. -/
theorem short_mem_derived_center :
    shortCommutator∈(center (⁅secondCore,secondCore⁆ : Subgroup (Model 0))).map (⁅secondCore,secondCore⁆).subtype := by
  rw [← D_eq_derived]
  have hs : shortCommutator=atlasEmbedding (word 7) := by
    simpa only [shortCommutator,map_mul,map_inv] using congrArg atlasEmbedding short_word_eq
  have hc : CollectedDerivedCore.group≤centralizer ({word 7}:Set Atlas1600Group) := by
    rw [CollectedDerivedCore.group]
    apply (closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact mem_centralizer_singleton_iff.mpr (short_center_generator _).symm.eq
  rw [hs]
  refine ⟨⟨atlasEmbedding (word 7),word_mem 7⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  rintro ⟨x,hx⟩
  obtain ⟨a,ha,rfl⟩:=hx
  apply Subtype.ext
  change atlasEmbedding a*atlasEmbedding (word 7)=atlasEmbedding (word 7)*atlasEmbedding a
  exact (atlasEmbedding.map_mul a (word 7)).symm.trans
    ((congrArg atlasEmbedding (mem_centralizer_singleton_iff.mp (hc ha))).trans
      (atlasEmbedding.map_mul (word 7) a))

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.IntrinsicDerivedCore
