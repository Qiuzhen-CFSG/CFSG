module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.Transport
public import Theory.GroupTheory.ComponentLocalOrbitFactors.SubnormalProduct
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SemidirectPerfect
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Short subnormal subgroups of binary affine powers

A short group embedded subnormally in a finite power of the actual binary
affine group in dimension three or four is isomorphic to one affine factor.
The affine group is perfect by natural-module displacements and has simple
quotient by its translation two-core. Subnormal commutator absorption therefore
puts a whole coordinate factor in the embedded short group.

That factor is normal and perfect. Its image modulo the short group's two-core
cannot be trivial or central, since a nontrivial perfect finite group is neither
a two-group nor abelian. The quasisimple-or-order-three clause of C.1.7 makes
this image the whole quotient. Two-perfection then removes the two-group
supplement. The argument needs no nonempty-index assumption: the nonzero
short module excludes a trivial image, and hence excludes the empty power.

The final consumer transports the actual intrinsic quotients and conjugation
module along the resulting affine isomorphism.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the end-node
calculation in 2.3.9(7), printed pp.525–526, with short groups and block types
as in C.1.7 and C.1.12, printed pp.123–124.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes
open Subgroup ChapterC Theory.GroupTheory SemidirectProduct

private theorem affine_perfect {d : ℕ} (hd : 3 ≤ d) : Group.IsPerfect (Affine d) := by
  let : Group.IsPerfect (BinaryLinear.GL (Vector d)) :=
    BinaryLinear.linearGroup_isPerfect d hd
  let : Group.IsPerfect (SL d) := Group.IsPerfect.ofSurjective
    (f := (slEquivLinear d).symm.toMonoidHom) (slEquivLinear d).symm.surjective
  apply Atlas.GroupTheory.semidirect_isPerfect_of_action_differences
  intro w
  obtain ⟨g, v, hv⟩ := BinaryNaturalDual.VectorStabilizers.exists_natural_displacement
    (V := Vector d) (by simpa using (show 2 ≤ d by omega)) (Multiplicative.toAdd w)
  refine ⟨(slEquivLinear d).symm g, Multiplicative.ofAdd v, ?_⟩
  apply Multiplicative.toAdd.injective
  change Matrix.mulVec _ v + -v = _
  rw [← sub_eq_add_neg, ← slEquivLinear_apply]
  rwa [MulEquiv.apply_symm_apply]

private theorem affine_simple_quotient {d : ℕ} (hd : 3 ≤ d) :
    IsSimpleGroup (Affine d ⧸ pCore 2 (Affine d)) := by
  let : NeZero d := ⟨by omega⟩
  let : IsSimpleGroup (PSL d) := Atlas.psl_simple_high_rank d hd
  let : IsSimpleGroup (SL d) := (slEquivPSL d).isSimpleGroup
  exact (affineCoreQuotientEquiv d).isSimpleGroup

private theorem short_normal_perfect_eq_top {D : Type*} [Group D]
    (hD : IsShort D) (N : Subgroup D) [N.Normal] [Group.IsPerfect N]
    (hne : N ≠ ⊥) : N = ⊤ := by
  let : Finite D := hD.finite
  let : Nontrivial N := (N.nontrivial_iff_ne_bot).mpr hne
  let q := QuotientGroup.mk' (pCore 2 D)
  let M := N.map q
  let : M.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect M := Group.IsPerfect.map q
  have hMne : M ≠ ⊥ := by
    intro hz
    have hle : N ≤ pCore 2 D := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz
    exact Group.IsPerfect.not_isNilpotent N (pCore_isPGroup.to_le hle).isNilpotent
  have hM : M = ⊤ := by
    rcases hD.quotient with hq | hq
    · let := hq
      rcases IsQuasisimple.normal_le_center_or_eq_top M with hc | ht
      · let : IsMulCommutative M := .of_setLike_mul_comm
          (fun a _ b hb => mem_center_iff.mp (hc hb) a)
        exact (hMne M.eq_bot_of_subsingleton).elim
      · exact ht
    · let : IsCyclic (D ⧸ pCore 2 D) := isCyclic_of_prime_card hq
      exact (hMne M.eq_bot_of_subsingleton).elim
  have hs : N ⊔ pCore 2 D = ⊤ := by
    have he := congrArg (Subgroup.comap q) hM
    simpa [M, q, sup_comm] using he
  have him : (pCore 2 D).map (QuotientGroup.mk' N) = ⊤ := by
    have he := congrArg (Subgroup.map (QuotientGroup.mk' N)) hs
    simpa [Subgroup.map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using he
  have hp : IsPGroup 2 (D ⧸ N) := by
    have hh : IsPGroup 2 ((pCore 2 D).map (QuotientGroup.mk' N)) :=
      pCore_isPGroup.map _
    rw [him] at hh
    exact hh.of_equiv topEquiv
  exact hD.twoPerfect N inferInstance hp

private theorem power_short_equiv {d r : ℕ} (hd : 3 ≤ d)
    {D : Type*} [Group D] (hD : IsShort D)
    (f : D →* (Fin r → Affine d)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) : Nonempty (D ≃* Affine d) := by
  classical
  let : Finite (Affine d) := Finite.of_equiv
    (Multiplicative (Vector d) × SL d) SemidirectProduct.equivProd.symm
  let : Group.IsPerfect (Affine d) := affine_perfect hd
  let : IsSimpleGroup (Affine d ⧸ pCore 2 (Affine d)) := affine_simple_quotient hd
  have hne : f.range ≠ ⊥ := by
    intro hz
    have hone (x : D) : x = 1 := by
      apply hf
      have hh : f x ∈ f.range := ⟨x, rfl⟩
      simpa only [hz, mem_bot, map_one] using hh
    have hh : blockU D = ⊥ := eq_bot_iff.mpr (fun x _ => mem_bot.mpr (hone x))
    have hi := hD.irreducible.1
    simp only [hh, bot_inf_eq] at hi
    exact lt_irrefl _ hi
  obtain ⟨i, hi⟩ := exists_mulSingle_mem_of_isSubnormal_isPPerfect
    (pCore 2 (Affine d)) pCore_isPGroup f.range hs
    (hD.twoPerfect.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hne
  let t : Affine d →* (Fin r → Affine d) := MonoidHom.mulSingle (fun _ : Fin r => Affine d) i
  let s : Affine d →* D := (MonoidHom.ofInjective hf).symm.toMonoidHom.comp
    (t.codRestrict f.range hi)
  have hfs (a : Affine d) : f (s a) = t a := MonoidHom.apply_ofInjective_symm hf _
  have hsi : Function.Injective s := by
    intro a b hab
    have he := congrArg (fun x => f x i) hab
    simpa only [hfs, t, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] using he
  let : s.range.Normal := ⟨by
    rintro _ ⟨a, rfl⟩ x
    refine ⟨f x i * a * (f x i)⁻¹, hf ?_⟩
    simp only [map_mul, map_inv, hfs]
    funext j
    by_cases hij : j = i
    · subst j
      simp [t]
    · simp [t, Pi.mulSingle_eq_of_ne hij]⟩
  let : Group.IsPerfect s.range := Group.IsPerfect.range s
  have hsne : s.range ≠ ⊥ := by
    intro hz
    have htriv (a : Affine d) : a = 1 := by
      apply hsi
      have hh : s a ∈ s.range := ⟨a, rfl⟩
      simpa only [hz, mem_bot, map_one] using hh
    have hbot : (⊤ : Subgroup (Affine d)) ≤ pCore 2 (Affine d) := by
      intro a _
      rw [htriv a]
      exact one_mem _
    have : Subsingleton (Affine d ⧸ pCore 2 (Affine d)) :=
      (QuotientGroup.subsingleton_iff).mpr (top_unique hbot)
    exact not_subsingleton (Affine d ⧸ pCore 2 (Affine d)) inferInstance
  have hstop := short_normal_perfect_eq_top hD s.range hsne
  exact ⟨(MulEquiv.ofBijective s ⟨hsi, MonoidHom.range_eq_top.mp hstop⟩).symm⟩

/-- A short subnormal group in a finite power of the genuine binary affine
model is one affine factor. This includes the empty-power case. -/
theorem affine_equiv_of_short_subnormal_power {d r : ℕ} (hd : d = 3 ∨ d = 4)
    {D : Type*} [Group D] (hD : IsShort D)
    (f : D →* (Fin r → Affine d)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) : Nonempty (D ≃* Affine d) :=
  power_short_equiv (by omega) hD f hf hs

/-- The affine-power identification supplies the actual natural block module
on the original short-group carrier, as required by the end-node consumer. -/
theorem linearTwoBlock_of_short_subnormal_affine_power {d r : ℕ}
    (hd : d = 3 ∨ d = 4) {D : Type*} [Group D] (hD : IsShort D)
    (f : D →* (Fin r → Affine d)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) : IsLinearTwoBlock D d := by
  obtain ⟨e⟩ := affine_equiv_of_short_subnormal_power hd hD f hf hs
  exact linearTwoBlock_of_affine_equiv (by omega) hD e

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes
end
