module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SecondCore
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.AbelianNormalizer

/-!
# Root generators for the actual binary linear radical

The seven positive Parrott roots before s₈ and the outer root q lie in the
linear radical. The first 1024 faithful Sylow words give distinct derived
elements; multiplying by q supplies a disjoint outer coset. The known core
order 2048 therefore proves generation, without a new multiplication table.
Source: the root coordinates of F.4.27(4) used in J.4.7, printed p.444.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open InvolutionRootGeometry.BinaryDerivedFusion RootRelations

/-- The outer first root is in the actual second two-core. -/
theorem q_mem_secondCore : q∈secondCore := by
  rw [secondCore_eq_radical]
  change toSplitGroup 0 q∈splitRadical 0 .linear
  rw [q,fixedU_matrix]
  change quartetElement 0∈splitRadical 0 .linear
  have h (j:Fin 4) : IsRadicalRoot .linear (quartetRoots 0 j) := by
    have hh := ((rootBlocks (.radical .linear)).roots (.inr ((0:Fin 4),j))).property
    change IsRadicalRoot .linear _ at hh
    have he : quartetRoots 0 j=((rootBlocks (.radical .linear)).roots (.inr ((0:Fin 4),j))).val := by
      apply Subtype.ext
      change ((rootBlocks .positive).roots (.inr ((0:Fin 4),j))).val.val=_
      rw [rootBlocks_roots_val,rootBlocks_roots_val]
      rfl
    exact he.symm ▸ hh
  rw [quartetElement_eq]
  exact (splitRadical 0 .linear).mul_mem
    ((splitRadical 0 .linear).mul_mem (subset_closure ⟨_,1,h 0,rfl⟩)
      (subset_closure ⟨_,1,h 1,rfl⟩)) (subset_closure ⟨_,1,h 3,rfl⟩)

/-- The eight literal root generators, with the sole outer one first. -/
def coreGenerator (i:Fin 8) : Model 0 :=
  ![q,atlasEmbedding (Atlas.a .s1),atlasEmbedding (Atlas.a .s2),
    atlasEmbedding (Atlas.a .s3),atlasEmbedding (Atlas.a .s4),
    atlasEmbedding (Atlas.a .s5),atlasEmbedding (Atlas.a .s6),
    atlasEmbedding (Atlas.a .s7)] i

private def coreSpan : Subgroup (Model 0) := closure (Set.range coreGenerator)

private theorem coreSpan_le : coreSpan≤secondCore := by
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact q_mem_secondCore
  all_goals exact generator_mem_secondCore _ (by decide) (by decide) (by decide)

private def corePrefix (n:Fin 1024) : Model 0 :=
  atlasEmbedding (atlas1600SylowTwoNormalForm ⟨n.val,by omega⟩)

private theorem corePrefix_mem (n:Fin 1024) : corePrefix n∈coreSpan := by
  have h (i:Fin 8) : coreGenerator i∈coreSpan := subset_closure ⟨i,rfl⟩
  have h8 : n.val/1024%2=0 := by omega
  rw [corePrefix,atlas1600SylowTwoNormalForm_eq,h8]
  simp only [map_mul,map_pow,pow_zero,mul_one]
  exact coreSpan.mul_mem
    (coreSpan.mul_mem (coreSpan.mul_mem (coreSpan.mul_mem
      (coreSpan.mul_mem (coreSpan.mul_mem (coreSpan.pow_mem (h 1) _) (coreSpan.pow_mem (h 2) _))
        (coreSpan.pow_mem (h 3) _)) (coreSpan.pow_mem (h 4) _))
        (coreSpan.pow_mem (h 5) _)) (coreSpan.pow_mem (h 6) _)) (coreSpan.pow_mem (h 7) _)

private theorem corePrefix_injective : Function.Injective corePrefix := by
  intro a b h
  have hh := atlas1600SylowTwoNormalForm_injective (atlasEmbedding_injective h)
  exact Fin.ext (congrArg (fun z:Fin 2048 => z.val) hh)

private theorem corePrefix_derived (n:Fin 1024) : corePrefix n∈commutator (Model 0) := by
  rw [← atlasEmbedding_range]
  exact ⟨_,rfl⟩

private theorem q_not_derived : q∉commutator (Model 0) := fixedU_zero_not_mem

/-- The literal root family generates the full intrinsic second core. -/
theorem secondCore_eq_closure : secondCore=closure (Set.range coreGenerator) := by
  apply (eq_of_le_of_card_ge coreSpan_le ?_).symm
  have hq : q∈coreSpan := subset_closure ⟨0,rfl⟩
  let f : Fin 2 × Fin 1024 → coreSpan := fun a =>
    ⟨q^a.1.val * corePrefix a.2,coreSpan.mul_mem (coreSpan.pow_mem hq _) (corePrefix_mem _)⟩
  have hinj : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hv : q^i.val*corePrefix a=q^j.val*corePrefix b := congrArg Subtype.val he
    have hn (a b:Fin 1024) : q*corePrefix a≠corePrefix b := by
      intro hh
      apply q_not_derived
      have hm := (commutator (Model 0)).mul_mem (corePrefix_derived b)
        ((commutator (Model 0)).inv_mem (corePrefix_derived a))
      rw [← hh,mul_inv_cancel_right] at hm
      exact hm
    fin_cases i <;> fin_cases j <;> simp only [pow_zero,pow_one,one_mul] at hv
    · exact Prod.ext rfl (corePrefix_injective hv)
    · exact (hn b a hv.symm).elim
    · exact (hn a b hv).elim
    · exact Prod.ext rfl (corePrefix_injective (mul_left_cancel hv))
  have hc := Nat.card_le_card_of_injective f hinj
  have hcore : Nat.card secondCore=2048 := by
    rw [secondCore,card_map_of_injective second.subtype_injective,second_core_card]
  rw [hcore]
  simpa only [Nat.card_prod,Nat.card_fin] using hc

end Tits.ExceptionalParabolics.FullRee.LongRootPaths
