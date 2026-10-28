module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DerivedCoreCertificate
public import Theory.GroupTheory.CyclicExtension

/-!
# The collected 64-element subgroup and its center bound

Successive cyclic collection proves that the certified binary words exhaust
the specified subgroup. The last square lies in the preceding elementary
subgroup, so its exponent reduces to zero or one. The faithful point test
then bounds the center by eight elements. Source: the local root calculation
in J.4.7, printed p.444.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.CollectedDerivedCore
open Subgroup Theory.GroupTheory DerivedCoreCertificate
attribute [local irreducible] gen

/-- The candidate derived subgroup in the faithful Atlas marking. -/
def group : Subgroup Atlas1600Group := closure {gen 5,gen 4,gen 3,gen 2,gen 1,gen 0}

theorem gen_mem (i:Fin 6) : gen i∈group := by
  apply subset_closure
  fin_cases i <;> simp

private theorem gen_inv (i:Fin 6) : (gen i)⁻¹=(gen i)^3 := by
  have h4 : (gen i)^4=1 := by
    by_cases hi:i=5
    · simpa only [hi,if_true] using generator_power i
    · have h2 : (gen i)^2=1 := by simpa only [hi,if_false] using generator_power i
      rw [show (gen i)^4=((gen i)^2)^2 by rw [← pow_mul],h2,one_pow]
  calc
    (gen i)⁻¹ = (gen i)⁻¹*1 := (mul_one _).symm
    _ = (gen i)⁻¹*(gen i)^4 := congrArg _ h4.symm
    _ = (gen i)^3 := by group

private theorem conjugates_0 : ∀ b∈((∅:Set Atlas1600Group):Set Atlas1600Group),
    gen 0*b*(gen 0)⁻¹∈closure ((∅:Set Atlas1600Group):Set Atlas1600Group) := by
  simp

private theorem conjugates_1 : ∀ b∈({gen 0}:Set Atlas1600Group),
    gen 1*b*(gen 1)⁻¹∈closure ({gen 0}:Set Atlas1600Group) := by
  have hm0 : gen 0∈closure ({gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  intro b hb
  simp only [Set.mem_singleton_iff] at hb
  subst b
  rw [gen_inv,conjugate_eq,show conjugateIndex 1 0=1 by decide]
  have he : word 1=gen 0 := by norm_num [word]
  rw [he]
  exact hm0

private theorem conjugates_2 : ∀ b∈({gen 1,gen 0}:Set Atlas1600Group),
    gen 2*b*(gen 2)⁻¹∈closure ({gen 1,gen 0}:Set Atlas1600Group) := by
  have hm0 : gen 0∈closure ({gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm1 : gen 1∈closure ({gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  intro b hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl|rfl
  · rw [gen_inv,conjugate_eq,show conjugateIndex 2 1=2 by decide]
    have he : word 2=gen 1 := by norm_num [word]
    rw [he]
    exact hm1
  · rw [gen_inv,conjugate_eq,show conjugateIndex 2 0=1 by decide]
    have he : word 1=gen 0 := by norm_num [word]
    rw [he]
    exact hm0

private theorem conjugates_3 : ∀ b∈({gen 2,gen 1,gen 0}:Set Atlas1600Group),
    gen 3*b*(gen 3)⁻¹∈closure ({gen 2,gen 1,gen 0}:Set Atlas1600Group) := by
  have hm0 : gen 0∈closure ({gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm1 : gen 1∈closure ({gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm2 : gen 2∈closure ({gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  intro b hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl|rfl|rfl
  · rw [gen_inv,conjugate_eq,show conjugateIndex 3 2=4 by decide]
    have he : word 4=gen 2 := by norm_num [word]
    rw [he]
    exact hm2
  · rw [gen_inv,conjugate_eq,show conjugateIndex 3 1=2 by decide]
    have he : word 2=gen 1 := by norm_num [word]
    rw [he]
    exact hm1
  · rw [gen_inv,conjugate_eq,show conjugateIndex 3 0=1 by decide]
    have he : word 1=gen 0 := by norm_num [word]
    rw [he]
    exact hm0

private theorem conjugates_4 : ∀ b∈({gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group),
    gen 4*b*(gen 4)⁻¹∈closure ({gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := by
  have hm0 : gen 0∈closure ({gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm1 : gen 1∈closure ({gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm2 : gen 2∈closure ({gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm3 : gen 3∈closure ({gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  intro b hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl|rfl|rfl|rfl
  · rw [gen_inv,conjugate_eq,show conjugateIndex 4 3=8 by decide]
    have he : word 8=gen 3 := by norm_num [word]
    rw [he]
    exact hm3
  · rw [gen_inv,conjugate_eq,show conjugateIndex 4 2=4 by decide]
    have he : word 4=gen 2 := by norm_num [word]
    rw [he]
    exact hm2
  · rw [gen_inv,conjugate_eq,show conjugateIndex 4 1=2 by decide]
    have he : word 2=gen 1 := by norm_num [word]
    rw [he]
    exact hm1
  · rw [gen_inv,conjugate_eq,show conjugateIndex 4 0=1 by decide]
    have he : word 1=gen 0 := by norm_num [word]
    rw [he]
    exact hm0

private theorem conjugates_5 : ∀ b∈({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group),
    gen 5*b*(gen 5)⁻¹∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := by
  have hm0 : gen 0∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm1 : gen 1∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm2 : gen 2∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm3 : gen 3∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  have hm4 : gen 4∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := subset_closure (by simp)
  intro b hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl
  · rw [gen_inv,conjugate_eq,show conjugateIndex 5 4=20 by decide]
    have he : word 20=gen 2*gen 4 := by norm_num [word]
    rw [he]
    exact (Subgroup.mul_mem _ hm2 hm4)
  · rw [gen_inv,conjugate_eq,show conjugateIndex 5 3=9 by decide]
    have he : word 9=gen 0*gen 3 := by norm_num [word]
    rw [he]
    exact (Subgroup.mul_mem _ hm0 hm3)
  · rw [gen_inv,conjugate_eq,show conjugateIndex 5 2=4 by decide]
    have he : word 4=gen 2 := by norm_num [word]
    rw [he]
    exact hm2
  · rw [gen_inv,conjugate_eq,show conjugateIndex 5 1=2 by decide]
    have he : word 2=gen 1 := by norm_num [word]
    rw [he]
    exact hm1
  · rw [gen_inv,conjugate_eq,show conjugateIndex 5 0=1 by decide]
    have he : word 1=gen 0 := by norm_num [word]
    rw [he]
    exact hm0

/-- Every binary word lies in the specified collected subgroup. -/
theorem word_mem (n:Fin 64) : word n∈group := by
  unfold word
  repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.pow_mem
    | exact gen_mem _

/-- The collected words exhaust the group. -/
theorem word_surjective {x:Atlas1600Group} (hx:x∈group) :
    ∃ n:Fin 64,word n=x := by
  obtain ⟨h5,hh5,i5,he5⟩ := exists_mul_pow_of_mem_closure_insert
    {gen 4,gen 3,gen 2,gen 1,gen 0} (gen 5) 4 (by decide)
    (by simpa only [if_true] using generator_power (5:Fin 6)) conjugates_5 hx
  have hs : (gen 5)^2∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group) := by
    rw [last_square]
    repeat first
      | apply Subgroup.mul_mem
      | exact Subgroup.subset_closure (by simp)
  have hcol : ∃ y∈closure ({gen 4,gen 3,gen 2,gen 1,gen 0}:Set Atlas1600Group),
      ∃ a5:Fin 2,y*(gen 5)^a5.val=x := by
    fin_cases i5
    · exact ⟨h5,hh5,0,he5⟩
    · exact ⟨h5,hh5,1,he5⟩
    · refine ⟨h5*(gen 5)^2,Subgroup.mul_mem _ hh5 hs,0,?_⟩
      change (h5*(gen 5)^2)*1=x
      simpa only [mul_one] using he5
    · refine ⟨h5*(gen 5)^2,Subgroup.mul_mem _ hh5 hs,1,?_⟩
      change (h5*(gen 5)^2)*gen 5=x
      simpa only [pow_succ,mul_assoc] using he5
  obtain ⟨y5,hy5,a5,rfl⟩ := hcol
  obtain ⟨y4,hy4,a4,rfl⟩ := exists_mul_pow_of_mem_closure_insert
    {gen 3,gen 2,gen 1,gen 0} (gen 4) 2 (by decide)
    (by simpa only [show (4:Fin 6)≠5 by decide,if_false] using generator_power (4:Fin 6))
    conjugates_4 hy5
  obtain ⟨y3,hy3,a3,rfl⟩ := exists_mul_pow_of_mem_closure_insert
    {gen 2,gen 1,gen 0} (gen 3) 2 (by decide)
    (by simpa only [show (3:Fin 6)≠5 by decide,if_false] using generator_power (3:Fin 6))
    conjugates_3 hy4
  obtain ⟨y2,hy2,a2,rfl⟩ := exists_mul_pow_of_mem_closure_insert
    {gen 1,gen 0} (gen 2) 2 (by decide)
    (by simpa only [show (2:Fin 6)≠5 by decide,if_false] using generator_power (2:Fin 6))
    conjugates_2 hy3
  obtain ⟨y1,hy1,a1,rfl⟩ := exists_mul_pow_of_mem_closure_insert
    {gen 0} (gen 1) 2 (by decide)
    (by simpa only [show (1:Fin 6)≠5 by decide,if_false] using generator_power (1:Fin 6))
    conjugates_1 hy2
  obtain ⟨y0,hy0,a0,rfl⟩ := exists_mul_pow_of_mem_closure_insert
    (∅:Set Atlas1600Group) (gen 0) 2 (by decide)
    (by simpa only [show (0:Fin 6)≠5 by decide,if_false] using generator_power (0:Fin 6))
    conjugates_0 (by simpa using hy1)
  simp only [closure_empty,mem_bot] at hy0
  subst y0
  let n:Fin 64 := ⟨1*a0.val+2*a1.val+4*a2.val+8*a3.val+16*a4.val+32*a5.val,by omega⟩
  refine ⟨n,?_⟩
  have h0 : n.val/1%2=a0.val := by dsimp [n]; omega
  have h1 : n.val/2%2=a1.val := by dsimp [n]; omega
  have h2 : n.val/4%2=a2.val := by dsimp [n]; omega
  have h3 : n.val/8%2=a3.val := by dsimp [n]; omega
  have h4 : n.val/16%2=a4.val := by dsimp [n]; omega
  have h5 : n.val/32%2=a5.val := by dsimp [n]; omega
  change gen 0^(n.val%2)*gen 1^(n.val/2%2)*gen 2^(n.val/4%2)*
    gen 3^(n.val/8%2)*gen 4^(n.val/16%2)*gen 5^(n.val/32%2)=_
  have h0' : n.val%2=a0.val := by simpa only [Nat.div_one] using h0
  simp only [h0',h1,h2,h3,h4,h5,one_mul]

/-- Exact order, from exhaustion and faithful one-point separation. -/
theorem card_group : Nat.card group=64 := by
  let f:Fin 64→group := fun n=>⟨word n,word_mem n⟩
  have hb : Function.Bijective f := by
    refine ⟨fun a b h=>word_injective (congrArg Subtype.val h),?_⟩
    intro x
    obtain ⟨n,hn⟩ := word_surjective x.property
    exact ⟨n,Subtype.ext hn⟩
  exact (Nat.card_congr (Equiv.ofBijective f hb).symm).trans (Nat.card_fin 64)

/-- The center contains at most the first eight collected words. -/
theorem card_center_le : Nat.card (center group)≤8 := by
  have hex (x:center group) : ∃ n:Fin 8,word ⟨n.val,by omega⟩=(x.val:Atlas1600Group) := by
    obtain ⟨n,hn⟩ := word_surjective x.val.property
    have hc (i:Fin 6) : Commute (word n) (gen i) := by
      rw [hn]
      exact (congrArg Subtype.val (mem_center_iff.mp x.property ⟨gen i,gen_mem i⟩)).symm
    have hlt := center_candidate n (hc 3) (hc 5)
    exact ⟨⟨n.val,hlt⟩,hn⟩
  let f:center group→Fin 8 := fun x=>Classical.choose (hex x)
  have hf (x:center group) : word ⟨(f x).val,by omega⟩=(x.val:Atlas1600Group) :=
    Classical.choose_spec (hex x)
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hf x,← hf y]
    exact congrArg word (Fin.ext (congrArg (fun n:Fin 8=>n.val) h))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.CollectedDerivedCore
