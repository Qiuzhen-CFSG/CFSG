module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Flags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.AutomorphismOvergroupRadical
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Perfect radical-free images of binary-five Sylow overgroups

A full Sylow overgroup is an actual flag stabilizer. Its two-core is killed
in any radical-free image, leaving its product of diagonal binary linear
groups. Each block is either solvable or perfect; the normal solvable block
images vanish, and the remaining images generate a perfect group.

Consequently an action containing the inner automorphisms of a centerless
simple perfect group, with solvable outer group, has only inner image if
it factors through such a Sylow overgroup with two-group kernel.

Source application: Aschbacher--Smith 10.2.9, printed p.752. This proves
the quotient-action obstruction without assuming a marked parabolic type.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace BinaryLinear
open OuterCyclic SmallParabolicLevi SmallParabolicLevi.TwoNodes FiveFlagGeometry
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem small_solvable (n : ℕ) (hn : n ≤ 2) : Group.IsSolvable (LinearGroup n) := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have hc : Nat.card (LinearGroup n) = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
    simp
  rw [hc] at hd
  interval_cases n
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num [Fin.prod_univ_two] at hd
    have hh := hp.dvd_mul.mp (show p ∣ 2*3 from hd)
    exact hh.elim
      (fun h => Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
      (fun h => Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one))

private theorem pi_radical_free_perfect {ι : Type*} [Finite ι]
    (A : ι → Type*) [∀ i, Group (A i)]
    (hA : ∀ i, Group.IsSolvable (A i) ∨ Group.IsPerfect (A i))
    {B : Type*} [Group B] (f : (∀ i, A i) →* B) (hf : Function.Surjective f)
    (hr : solvableRadical B = ⊥) : Group.IsPerfect B := by
  classical
  constructor
  apply top_unique
  rintro b _
  obtain ⟨x,rfl⟩ := hf b
  change x ∈ (commutator B).comap f
  apply pi_mem_of_mulSingle_mem
  intro i
  let s := MonoidHom.mulSingle A i
  let g := f.comp s
  have hn : s.range.Normal := by
    constructor
    rintro y ⟨a,rfl⟩ z
    refine ⟨z i * a * (z i)⁻¹,?_⟩
    ext j
    by_cases hj : j = i
    · subst j; simp [s]
    · simp [s,Pi.mulSingle_eq_of_ne hj]
  rcases hA i with hs | hp
  · let := hs
    have hgs : Group.IsSolvable g.range := Group.isSolvable_of_surjective g.rangeRestrict_surjective
    have hgn : g.range.Normal := by
      rw [MonoidHom.range_comp]
      exact hn.map f hf
    have hb : g.range ≤ ⊥ := hr ▸ le_solvableRadical g.range hgn hgs
    have he : g (x i) = 1 := hb ⟨x i,rfl⟩
    change g (x i) ∈ commutator B
    rw [he]
    exact one_mem _
  · let := hp
    let : Group.IsPerfect g.range := Group.IsPerfect.range g
    have hg : g.range ≤ commutator B := by
      rw [←g.range.commutator_eq_self]
      exact commutator_mono le_top le_top
    exact hg ⟨x i,rfl⟩

/-- Radical-free images of actual binary-five flags are perfect. -/
theorem flag_radical_free_image_perfect (b : FiveBasis) (cuts : Set (Fin 4))
    {Q : Type*} [Group Q] (f : flagStabilizer b cuts →* Q)
    (hf : Function.Surjective f) (hr : solvableRadical Q = ⊥) : Group.IsPerfect Q := by
  let d := flagDiagonalAction b cuts
  have hk : d.ker ≤ f.ker := by
    rw [ker_flagDiagonalAction]
    have hn := (inferInstance : (pCore 2 (flagStabilizer b cuts)).Normal).map f hf
    let : Group.IsNilpotent (pCore 2 (flagStabilizer b cuts)) := pCore_isNilpotent
    have hs : Group.IsSolvable ((pCore 2 (flagStabilizer b cuts)).map f) :=
      Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
    have hh := le_solvableRadical _ hn hs
    rw [hr,le_bot_iff,Subgroup.map_eq_bot_iff] at hh
    exact hh
  let g : (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (cutLabel cuts) k)) →* Q :=
    d.liftOfSurjective (flagDiagonalAction_surjective b cuts) ⟨f,hk⟩
  have hg (x : flagStabilizer b cuts) : g (d x) = f x :=
    d.liftOfRightInverse_comp_apply _ _ _ x
  apply pi_radical_free_perfect _ ?_ g ?_ hr
  · intro k
    let n := Module.finrank (ZMod 2) (BlockSpace (cutLabel cuts) k)
    let a : BlockSpace (cutLabel cuts) k ≃ₗ[ZMod 2] Space n :=
      LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun (ZMod 2)).symm
    let e := linearGroupCongr a
    by_cases hn : n ≤ 2
    · let := small_solvable n hn
      exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    · let := linearGroup_isPerfect n (by omega)
      exact Or.inr (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · intro q
    obtain ⟨x,rfl⟩ := hf q
    exact ⟨d x,hg x⟩

/-- A radical-free quotient of a full-Sylow overgroup of SL5(2) is perfect. -/
theorem sylow_overgroup_radical_free_image_perfect
    (S : Sylow 2 (LinearGroup 5)) (P : Subgroup (LinearGroup 5))
    (hSP : (S : Subgroup (LinearGroup 5)) ≤ P)
    {Q : Type*} [Group Q] (f : P →* Q) (hf : Function.Surjective f)
    (hr : solvableRadical Q = ⊥) : Group.IsPerfect Q := by
  obtain ⟨b,cuts,hP⟩ := isFlagParabolic_of_sylow_le S P hSP
  subst P
  exact flag_radical_free_image_perfect b cuts f hf hr
end BinaryLinear

namespace BinaryLinear
open OuterCyclic
/-- A quotient action of a full-Sylow overgroup with prime-group kernel
cannot add outer automorphisms to a simple perfect inner subgroup. -/
theorem sylow_overgroup_quotient_action_inner
    {E Q : Type*} [Group E] [Group Q] [Finite E] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q]
    (hz : center Q = ⊥) [Group.IsSolvable (MulAut.Outer Q)]
    (f : E →* LinearGroup 5) (hf : Function.Surjective f) (S : Sylow 2 E)
    (K : Subgroup E) (hSK : (S : Subgroup E) ≤ K)
    (a : K →* MulAut Q) (hi : MulAut.innerSubgroup Q ≤ a.range)
    (hk : IsPGroup 2 (f.comp K.subtype).ker) (ha : pCore 2 K ≤ a.ker) :
    a.range ≤ MulAut.innerSubgroup Q := by
  let g := f.comp K.subtype
  have hker : g.rangeRestrict.ker ≤ a.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact (show g.ker ≤ pCore 2 K from le_sSup ⟨inferInstance,hk⟩).trans ha
  let b : g.range →* MulAut Q := g.rangeRestrict.liftOfSurjective
    g.rangeRestrict_surjective ⟨a,hker⟩
  have hb (x : K) : b (g.rangeRestrict x) = a x :=
    g.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ x
  have hba : b.range = a.range := by
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      obtain ⟨k,rfl⟩ := g.rangeRestrict_surjective x
      rw [hb]
      exact ⟨k,rfl⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨g.rangeRestrict x,hb x⟩
  have hS : ((S.mapSurjective hf : Sylow 2 (LinearGroup 5)) :
      Subgroup (LinearGroup 5)) ≤ g.range := by
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨⟨s,hSK hs⟩,rfl⟩
  have hr := MulAut.radical_free_of_inner_le hz b.range (hba.symm ▸ hi)
  let : Group.IsPerfect b.range := sylow_overgroup_radical_free_image_perfect
    (S.mapSurjective hf) g.range hS b.rangeRestrict b.rangeRestrict_surjective hr
  rw [←hba]
  exact le_of_isPerfect_of_solvable_quotient _ _
end BinaryLinear
