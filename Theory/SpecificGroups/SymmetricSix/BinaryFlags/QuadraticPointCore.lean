module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction.Transport
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry
/-!
# Quadratic subgroups of the six-letter point core

The even core of the point stabilizer is not quadratic on the actual
four-dimensional augmentation quotient: two double transpositions have a
nonzero double displacement. Its quadratic subgroups have order at most two,
so a quadratic subgroup of the full point core has order at most four.
If it has order four, a nontrivial even actor has equal moved and fixed
planes. Quadraticity identifies the whole moved space with that plane,
which is an actual point-stabilizer conjugate of the canonical plane.

Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
open NaturalGeometry Representation.BinaryOffender
private def lineA : S := swap01 * swap23
private def lineB : S := Equiv.swap 0 2 * Equiv.swap 1 3
private theorem lineA_mem : lineA ∈ pointCoreEven := by
  refine ⟨?_,by change Equiv.Perm.sign lineA = 1; decide⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp [lineA])
private theorem lineB_mem : lineB ∈ pointCoreEven := by
  refine ⟨?_,by change Equiv.Perm.sign lineB = 1; decide⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp [lineB])

private def evenWord (i : Fin 4) : S := ![1,lineA,lineB,lineA*lineB] i
private theorem evenWord_mem (i : Fin 4) : evenWord i ∈ pointCoreEven := by
  fin_cases i
  · exact one_mem _
  · exact lineA_mem
  · exact lineB_mem
  · exact mul_mem lineA_mem lineB_mem
private theorem evenWord_surjective : ∀h∈pointCoreEven, ∃i, evenWord i = h := by
  let f : Fin 4 → pointCoreEven := fun i => ⟨evenWord i,evenWord_mem i⟩
  have hi : Function.Injective f := by
    intro i j he
    have hh : evenWord i 0 = evenWord j 0 := congrArg (fun h:pointCoreEven=>h.val 0) he
    have cert : ∀i j:Fin 4, evenWord i 0 = evenWord j 0 → i=j := by decide +kernel
    exact cert i j hh
  have hb := hi.bijective_of_nat_card_le (by rw [pointCoreEven_card,Nat.card_fin])
  intro h hh
  obtain ⟨i,he⟩ := hb.2 ⟨h,hh⟩
  exact ⟨i,congrArg Subtype.val he⟩
private theorem even_nontrivial_conjugate (h : S) (hh : h ∈ pointCoreEven) (hn : h ≠ 1) :
    ∃g∈L1, g*lineA*g⁻¹=h := by
  obtain ⟨i,rfl⟩ := evenWord_surjective h hh
  fin_cases i
  · exact (hn rfl).elim
  · exact ⟨1,one_mem _,by simp [evenWord]⟩
  · refine ⟨cycle012^2, by decide, ?_⟩
    decide
  · refine ⟨cycle012, by decide, ?_⟩
    decide

def Quadratic (A : Subgroup S) : Prop :=
  ∀g∈A, ∀h∈A, ∀v:V,
    naturalRepresentation Ω g (naturalRepresentation Ω h v - v) = naturalRepresentation Ω h v - v

private theorem cross_displacement :
    naturalRepresentation Ω lineA (naturalRepresentation Ω lineB (pairVector 0 4) - pairVector 0 4) -
      (naturalRepresentation Ω lineB (pairVector 0 4) - pairVector 0 4) = pairVector 4 5 := by
  rw [map_sub,pairVector_map,pairVector_map,pairVector_map]
  change pairVector 3 4 - pairVector 1 4 - (pairVector 2 4 - pairVector 0 4) = pairVector 4 5
  apply Subtype.ext
  change (constants Ω).mkQ _ - (constants Ω).mkQ _ -
    ((constants Ω).mkQ _ - (constants Ω).mkQ _) = (constants Ω).mkQ _
  rw [← map_sub,← map_sub,← map_sub]
  apply (Submodule.Quotient.eq _).mpr
  have he : ((Pi.single (3:Ω) (1:ZMod 2) + Pi.single 4 1) -
      (Pi.single 1 1 + Pi.single 4 1) - ((Pi.single 2 1 + Pi.single 4 1) -
      (Pi.single 0 1 + Pi.single 4 1))) - (Pi.single 4 1 + Pi.single 5 1) = allOne Ω := by
    ext a
    fin_cases a <;> decide
  rw [he]
  exact Submodule.subset_span (by simp)

private theorem lineA_fixed : LinearMap.ker (naturalRepresentation Ω lineA - LinearMap.id) =
    canonicalPlane := by
  ext v
  rw [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]
  rcases vector_cases v with rfl | ⟨d,rfl⟩
  · simp
  · change naturalRepresentation Ω lineA (pairVector d.val.1 d.val.2) =
      pairVector d.val.1 d.val.2 ↔ pairVector d.val.1 d.val.2 ∈ canonicalPlane
    rw [pairVector_map,pairVector_eq_iff (lineA.injective.ne (ne_of_lt d.property))
      (ne_of_lt d.property),pairVector_mem_plane_iff (ne_of_lt d.property)]
    have cert : ∀i j:Ω, i<j →
        (pair (lineA i) (lineA j) = pair i j ↔ pair i j ∈ baseSyntheme) := by decide +kernel
    exact cert d.val.1 d.val.2 d.property

private theorem lineA_range : LinearMap.range (naturalRepresentation Ω lineA - LinearMap.id) =
    canonicalPlane := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v,rfl⟩
    rw [← lineA_fixed]
    simp only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero,map_sub]
    have hs : lineA*lineA=1 := by decide
    rw [← Module.End.mul_apply,← map_mul,hs,map_one,Module.End.one_apply]
    simp only [ZModModule.sub_eq_add,add_comm]
  · have h := (naturalRepresentation Ω lineA - LinearMap.id).finrank_range_add_finrank_ker
    rw [lineA_fixed,canonicalPlane_finrank,finrank_natural_even Ω (by decide)] at h
    change _ + 2 = 4 at h
    rw [canonicalPlane_finrank]
    exact Nat.add_right_cancel h

private theorem displacement_range_conjugate (g h : S) :
    LinearMap.range (naturalRepresentation Ω (g*h*g⁻¹) - LinearMap.id) =
      (LinearMap.range (naturalRepresentation Ω h - LinearMap.id)).map (naturalRepresentation Ω g) := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨naturalRepresentation Ω h (naturalRepresentation Ω g⁻¹ w) - naturalRepresentation Ω g⁻¹ w,
      ⟨naturalRepresentation Ω g⁻¹ w,rfl⟩,?_⟩
    change naturalRepresentation Ω g (naturalRepresentation Ω h (naturalRepresentation Ω g⁻¹ w) -
      naturalRepresentation Ω g⁻¹ w) = naturalRepresentation Ω (g*h*g⁻¹) w - w
    rw [map_sub]
    have hi : naturalRepresentation Ω g (naturalRepresentation Ω g⁻¹ w) = w := by
      rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [hi,map_mul,map_mul]
    rfl
  · rintro ⟨_,⟨w,rfl⟩,rfl⟩
    refine ⟨naturalRepresentation Ω g w,?_⟩
    change naturalRepresentation Ω (g*h*g⁻¹) (naturalRepresentation Ω g w) - naturalRepresentation Ω g w =
      naturalRepresentation Ω g (naturalRepresentation Ω h w-w)
    rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel_right,map_mul,Module.End.mul_apply,map_sub]

private theorem moved_of_even_actor (A : Subgroup S) (hquad : Quadratic A)
    (h : S) (hhA : h∈A) (hh : h∈pointCoreEven) (hn : h≠1) :
    ∃g∈L1, subspaceCommutator (naturalRepresentation Ω) ⊤ A =
      canonicalPlane.map (naturalRepresentation Ω g) := by
  obtain ⟨g,hg,rfl⟩ := even_nontrivial_conjugate h hh hn
  refine ⟨g,hg,?_⟩
  have hrange := displacement_range_conjugate g lineA
  rw [lineA_range] at hrange
  let h := g*lineA*g⁻¹
  let f := naturalRepresentation Ω h - LinearMap.id
  have hr : Module.finrank (ZMod 2) f.range = 2 := by
    rw [hrange]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation Ω).asGroupHom g)).finrank_map_eq canonicalPlane |>.trans canonicalPlane_finrank
  have hk : Module.finrank (ZMod 2) f.ker = 2 := by
    have hdim := f.finrank_range_add_finrank_ker
    rw [hr,finrank_natural_even Ω (by decide)] at hdim
    change 2 + _ = 4 at hdim
    exact Nat.add_left_cancel hdim
  have he : f.range = f.ker := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v,rfl⟩
      change naturalRepresentation Ω h (naturalRepresentation Ω h v-v) - (naturalRepresentation Ω h v-v)=0
      rw [hquad h hhA h hhA v,sub_self]
    · exact hr.trans hk.symm
  apply le_antisymm
  · rw [← hrange,he]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,_,rfl⟩
    change naturalRepresentation Ω h (naturalRepresentation Ω k v-v) - (naturalRepresentation Ω k v-v)=0
    rw [hquad h hhA k hk v,sub_self]
  · rw [← hrange]
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨h,hhA,v,Submodule.mem_top,rfl⟩

theorem evenCore_not_quadratic : ¬ Quadratic pointCoreEven := by
  intro h
  have hh := h lineA lineA_mem lineB lineB_mem (pairVector 0 4)
  have he := cross_displacement
  rw [hh,sub_self] at he
  exact pairVector45_ne_zero he.symm

theorem even_quadratic_card_le_two (A : Subgroup S) (hA : A ≤ pointCoreEven)
    (hquad : Quadratic A) : Nat.card A ≤ 2 := by
  have hd : Nat.card A ∣ 4 := pointCoreEven_card ▸ card_dvd_of_le hA
  have hn : Nat.card A ≠ 4 := by
    intro hc
    have he : A = pointCoreEven := Subgroup.eq_of_le_of_card_ge hA (by rw [hc,pointCoreEven_card])
    exact evenCore_not_quadratic (he ▸ hquad)
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  by_contra h
  have hc : Nat.card A = 3 := by omega
  rw [hc] at hd
  norm_num at hd

theorem quadratic_card_le_four (A : Subgroup S) (hA : A ≤ pointCore)
    (hquad : Quadratic A) : Nat.card A ≤ 4 := by
  let B := A ⊓ alternatingGroup Ω
  have hb : Nat.card B ≤ 2 := even_quadratic_card_le_two B
    (inf_le_inf hA le_rfl) (fun g hg h hh v => hquad g hg.1 h hh.1 v)
  have hi : (alternatingGroup Ω).relIndex A ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    exact (alternatingGroup.index_eq_two (α := Ω)) ▸ relIndex_dvd_index_of_normal (alternatingGroup Ω) A
  have hc := (B.subgroupOf A).card_mul_index
  have he : Nat.card (B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe (show B ≤ A from inf_le_left)).toEquiv
  rw [he] at hc
  have hi' : (B.subgroupOf A).index = (alternatingGroup Ω).relIndex A :=
    inf_relIndex_left A (alternatingGroup Ω)
  rw [hi'] at hc
  calc Nat.card A = Nat.card B * (alternatingGroup Ω).relIndex A := hc.symm
       _ ≤ 2*2 := Nat.mul_le_mul hb hi
       _ = 4 := rfl

theorem quadratic_four_moved_plane (A : Subgroup S) (hA : A ≤ pointCore)
    (hquad : Quadratic A) (hcard : Nat.card A = 4) :
    ∃g∈L1, subspaceCommutator (naturalRepresentation Ω) ⊤ A =
      canonicalPlane.map (naturalRepresentation Ω g) := by
  let B := A ⊓ alternatingGroup Ω
  have hn : B ≠ ⊥ := by
    intro hb
    have hi : (alternatingGroup Ω).relIndex A ≤ 2 := by
      apply Nat.le_of_dvd (by decide)
      exact (alternatingGroup.index_eq_two (α := Ω)) ▸ relIndex_dvd_index_of_normal (alternatingGroup Ω) A
    have hc := (B.subgroupOf A).card_mul_index
    have he : Nat.card (B.subgroupOf A) = Nat.card B :=
      Nat.card_congr (subgroupOfEquivOfLe (show B ≤ A from inf_le_left)).toEquiv
    have hi' : (B.subgroupOf A).index = (alternatingGroup Ω).relIndex A :=
      inf_relIndex_left A (alternatingGroup Ω)
    rw [he,hi',hb,Nat.card_unique,one_mul,hcard] at hc
    omega
  obtain ⟨h,hh,hne⟩ := (B.bot_or_exists_ne_one).resolve_left hn
  exact moved_of_even_actor A hquad h hh.1 ⟨hA hh.1,hh.2⟩ hne
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
