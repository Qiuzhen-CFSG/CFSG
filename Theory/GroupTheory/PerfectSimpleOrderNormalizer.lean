module
public import Theory.GroupTheory.PerfectMinimalSimpleTwoNormalizer
public import Theory.GroupTheory.PerfectSimpleImageKernel
public import Theory.GroupTheory.SimpleSectionOrder

/-!
# A simple quotient filling a normalized automorphism image

Let a perfect group F have a simple quotient Q with soluble kernel.
A nontrivial action of F on Q is inner when Out(Q) is soluble. The inner
lift has soluble kernel, so its image order is divisible by |Q| and hence
fills Q. A p-subgroup normalized by that image lies in the p-core of an
automorphism overgroup containing Inn(Q); that core is trivial.

The quotient and action maps remain distinct. The source application is the
constrained A₈ star row in Aschbacher--Smith 4.2.13/4.4.6 and 12.1.9,
printed pp.612,620,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace MulAut

/-- A perfect group with a soluble-kernel quotient Q cannot act nontrivially
on Q while normalizing a nontrivial p-subgroup of its automorphism group. -/
theorem perfect_simple_quotient_normalizer_p_eq_bot
    {F Q : Type*} [Group F] [Finite F] [Group.IsPerfect F]
    [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    [Group.IsSolvable (Outer Q)] (hz : center Q = ⊥)
    (q : F →* Q) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (a : F →* MulAut Q) (hne : a ≠ 1)
    {p : ℕ} [Fact p.Prime] (U : Subgroup (MulAut Q)) (hU : IsPGroup p U)
    (hAU : a.range ≤ normalizer (U : Set (MulAut Q))) : U = ⊥ := by
  let A := a.range
  let : Group.IsPerfect A := Group.IsPerfect.range a
  obtain ⟨f,hf,hconj⟩ := perfect_subgroup_exists_inner_lift A hz
  let r := f.comp a.rangeRestrict
  have hrne : r ≠ 1 := by
    intro he
    apply hne
    apply MonoidHom.ext
    intro x
    have hh : f (a.rangeRestrict x) = f 1 :=
      (DFunLike.congr_fun he x).trans f.map_one.symm
    exact congrArg A.subtype (hf hh)
  let : Group.IsSolvable r.ker := solvable_ker_of_nontrivial_hom_of_simple_quotient q hq r hrne
  let : Group.IsSolvable r.rangeRestrict.ker := (MonoidHom.ker_rangeRestrict r).symm ▸ inferInstance
  have hd := SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable Q) q hq r.rangeRestrict
  have hr : r.range = ⊤ := Subgroup.eq_top_of_card_eq _ (le_antisymm
    (Nat.card_le_card_of_injective r.range.subtype r.range.subtype_injective)
    (Nat.le_of_dvd Nat.card_pos hd))
  have hi : ∀ x : Q, conj x ∈ A := by
    intro x
    obtain ⟨y,hy⟩ := (show x ∈ r.range from hr ▸ mem_top x)
    rw [←hy]
    change conj (f (a.rangeRestrict y)) ∈ A
    rw [hconj]
    exact (a.rangeRestrict y).property
  have hcore : pCore p Q = ⊥ := by
    rcases (inferInstance : (pCore p Q).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hp : IsPGroup p Q := IsPGroup.of_equiv
        (pCore_isPGroup (p := p) (G := Q)) ((MulEquiv.subgroupCongr ht).trans topEquiv)
      let := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  let J := A ⊔ U
  have hj : pCore p J = ⊥ := automorphism_core_eq_bot p
    (conj_injective_of_center_eq_bot hz) hcore J (fun x => mem_sup_left (hi x))
  have hu : U ≤ J.pCoreIn p := le_pCoreIn_of_normalizes hU le_sup_right
    (sup_le hAU U.le_normalizer)
  unfold Subgroup.pCoreIn at hu
  rw [hj,Subgroup.map_bot] at hu
  exact bot_unique hu

end MulAut
