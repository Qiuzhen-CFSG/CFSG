module
public import CFSG.Quasithin.ChapterE.Section04.InvariantSubmodule
public import Theory.Representation.BinaryPermutation.ThreeTensor
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.ElementaryAbelian.Injective

/-!
# The fixed-space parameter of a tensor with the binary three-point core

For an elementary two-subgroup, a nontrivial projection to S₃ has image
of order two. A common fixed vector in the first factor makes its kernel
an index-two subgroup with strictly more fixed vectors in the tensor.
If that projection is trivial, the tensor contains an invariant copy of
the first factor. Thus a ≤ 1 for the first factor implies a ≤ 1 for the
whole tensor. The doubled A₅ normalizer is the concrete application.
Source: Aschbacher–Smith, E.3.8–9 and 12.4.1, printed pp.232,812.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation TensorProduct
namespace CFSG.Quasithin.ChapterE

private theorem family_top {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A : Subgroup G} {k : ℕ}
    (hA : A ∈ fixedSpaceFamily ρ k) :
    (⊤ : Subgroup A) ∈ fixedSpaceFamily (ρ.comp A.subtype) k := by
  let := hA.2.1.2
  refine ⟨hA.1,⟨?_,IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype Subtype.val_injective⟩,?_⟩
  · intro he
    have hm := congrArg (Subgroup.map A.subtype) he
    apply hA.2.1.1
    simpa only [←MonoidHom.range_eq_map,Subgroup.range_subtype,Subgroup.map_bot] using hm
  · intro B _ hb
    have hi := B.relIndex_map_map_of_injective (⊤ : Subgroup A) A.subtype_injective
    simp only [←MonoidHom.range_eq_map,Subgroup.range_subtype] at hi
    have he := hA.2.2 (B.map A.subtype) (map_subtype_le B) (hi ▸ hb)
    simpa only [fixedSpace_comp_map,←MonoidHom.range_eq_map,Subgroup.range_subtype] using he

private theorem three_card_le_two {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (f : A →* Equiv.Perm (Fin 3)) : Nat.card f.range ≤ 2 := by
  have hp : IsPGroup 2 f.range := (IsElementaryAbelian.isPGroup 2 A).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd := card_subgroup_dvd_card f.range
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc,hn] at hd
  have hle : n ≤ 1 := by
    by_contra! hh
    have hbad : 4 ∣ 6 := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ n)) hd
    norm_num at hbad
  rw [hn]
  exact (Nat.pow_le_pow_right (by decide) hle).trans_eq (by decide)

private theorem three_moved (g : Equiv.Perm (Fin 3)) (hg : g ≠ 1) :
    ∃ w : core (Fin 3), coreRepresentation (Fin 3) g w ≠ w := by
  let : DecidablePred (· ∈ core (Fin 3)) := fun v =>
    inferInstanceAs (Decidable ((∑ i, v i) = (0 : ZMod 2)))
  let : Fintype (core (Fin 3)) := Subtype.fintype _
  revert g
  decide

private theorem tmul_left_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) (hv : v ≠ 0) : Function.Injective (fun w : core (Fin 3) => v ⊗ₜ[ZMod 2] w) := by
  intro w z he
  have hp := congrArg (ThreeTensor.pairEquiv (V := V)) he
  simp only [ThreeTensor.pairEquiv_tmul] at hp
  have h0 : w.val 0 = z.val 0 := (smul_left_injective (R := ZMod 2) hv) (congrArg Prod.fst hp)
  have h1 : w.val 1 = z.val 1 := (smul_left_injective (R := ZMod 2) hv) (congrArg Prod.snd hp)
  apply Subtype.ext
  have hw := w.property
  have hz := z.property
  rw [mem_core,Fin.sum_univ_three] at hw hz
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · change w.val 2 = z.val 2
    linear_combination hw - hz - h0 - h1

/-- A nontrivial three-point projection separates fixed spaces at its kernel. -/
private theorem tensor_not_family_of_outer
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) G V)
    (A : Subgroup (G × Equiv.Perm (Fin 3)))
    (hA : A ∈ fixedSpaceFamily (ThreeTensor.action ρ) 2)
    (hout : ∃ a ∈ A, a.2 ≠ 1) : False := by
  let := hA.2.1.2
  let f : A →* Equiv.Perm (Fin 3) := (MonoidHom.snd _ _).comp A.subtype
  let s : A →* G := (MonoidHom.fst _ _).comp A.subtype
  have hp := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide : ringChar (ZMod 2) ≠ 0)
    (by rwa [ringChar.eq (ZMod 2) 2]) (ρ.comp s)
  let B := f.ker
  have hi : Nat.log 2 (B.relIndex ⊤) < 2 := by
    rw [relIndex_top_right,Subgroup.index_ker]
    have hh := Nat.log_mono_right (b := 2) (three_card_le_two f)
    exact lt_of_le_of_lt hh (by decide)
  have he := (family_top _ hA).2.2 B le_top hi
  obtain ⟨a,ha,hat⟩ := hout
  obtain ⟨w,hw⟩ := three_moved a.2 hat
  have hB : v ⊗ₜ[ZMod 2] w ∈ fixedSpace ((ThreeTensor.action ρ).comp A.subtype) B := by
    intro b
    change ThreeTensor.action ρ b.val.val (v ⊗ₜ[ZMod 2] w) = _
    rw [ThreeTensor.action_tmul]
    have hb : b.val.val.2 = 1 := b.property
    have hvf : ρ b.val.val.1 v = v := hfix b.val
    rw [hb,hvf,map_one,Module.End.one_apply]
  have hh := (he.symm ▸ hB) (⟨⟨a,ha⟩,mem_top _⟩ : (⊤ : Subgroup A))
  change ThreeTensor.action ρ a (v ⊗ₜ[ZMod 2] w) = _ at hh
  rw [ThreeTensor.action_tmul,show ρ a.1 v = v from hfix ⟨a,ha⟩] at hh
  exact hw (tmul_left_injective v hv hh)

/-- Tensoring with the three-point core preserves a ≤ 1. -/
theorem moduleA_threeTensor_le_one
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) G V) (ha : moduleA ρ ≤ 1) :
    moduleA (ThreeTensor.action ρ) ≤ 1 := by
  apply (moduleA_le_iff_next_family_empty _ 1).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  by_cases hout : ∃ a ∈ A, a.2 ≠ 1
  · exact tensor_not_family_of_outer ρ A hA hout
  push Not at hout
  let f : A →* G := (MonoidHom.fst _ _).comp A.subtype
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact Prod.ext he ((hout a a.property).trans (hout b b.property).symm)
  let i : V →ₗ[ZMod 2] (V ⊗[ZMod 2] core (Fin 3)) :=
    ThreeTensor.pairEquiv.symm.toLinearMap.comp (LinearMap.inl (ZMod 2) V V)
  have hi : Function.Injective i :=
    ThreeTensor.pairEquiv.symm.injective.comp (fun _ _ he => congrArg Prod.fst he)
  have hie (a : A) (v : V) : i ((ρ.comp f) a v) =
      ((ThreeTensor.action ρ).comp A.subtype) a (i v) := by
    apply ThreeTensor.pairEquiv.injective
    have he : a.val = (a.val.1,1) := Prod.ext rfl (hout a a.property)
    change ThreeTensor.pairEquiv (ThreeTensor.pairEquiv.symm (ρ (f a) v,0)) =
      ThreeTensor.pairEquiv (ThreeTensor.action ρ a.val (i v))
    rw [he,ThreeTensor.pairEquiv_equivariant]
    simp only [i,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply,LinearMap.inl_apply]
    change (ρ (f a) v,0) = (ρ (f a) v,ρ (f a) 0)
    rw [map_zero]
  have hm := (moduleA_le_of_equivariant_embedding ((ThreeTensor.action ρ).comp A.subtype)
    (ρ.comp f) i hi hie).trans ((moduleA_comp_le ρ f hf).trans ha)
  have hl := (le_moduleA_of_mem _ (family_top _ hA)).trans hm
  norm_num at hl
end CFSG.Quasithin.ChapterE
