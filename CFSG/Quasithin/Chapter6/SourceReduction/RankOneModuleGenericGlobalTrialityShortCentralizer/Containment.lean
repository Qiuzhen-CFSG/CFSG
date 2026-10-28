module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Comparison
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Action

/-!
# The original ambient triality short-root centralizer bound

Commuting-class incidence identifies the total fixed-coset count with the
number of ambient long-root involutions in C_G(t). F.4.40 puts each such
involution into the designated Sylow subgroup contained in N_G(L), so each
fixes a coset and therefore fixes exactly one. The characteristic elementary
plane and its nonsolvable central Levi action then contradict I.8.5 under
proper containment. This proves F.4.42 in the actual C_G(t), retaining the
original comparison and all parameters m=n>1, including q=4.

Source: Aschbacher--Smith F.4.40 and the nonunitary case of F.4.42,
printed pp.294--295; application 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary TrialityCompletionFusion
variable {G : Type*} [Group G] [Finite G]

/-- Every long-class involution in the actual short centralizer fixes exactly
one coset of its intersection with the original N_G(L). -/
theorem Preparation.triality_short_long_unique_fixed
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse) :
    let P := binaryParameters m hm
    let t := (e.right.symm (shortElement P rfl)).val
    let z := (e.right.symm (longElement P rfl)).val
    let C := centralizer ({t} : Set G)
    let X := (normalizer (L : Set G)).subgroupOf C
    ∀ x : C, IsConj z x.val → ∃! q : C ⧸ X, x • q=q := by
  let P := binaryParameters m hm
  let t := (e.right.symm (shortElement P rfl)).val
  let z := (e.right.symm (longElement P rfl)).val
  let C := centralizer ({t} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf C
  let p : C → Prop := fun x => IsConj z x.val
  obtain ⟨R,hR⟩ := d.triality_short_centralizer_sylow h hH hp m hm e
  have hTN : (T : Subgroup G) ≤ normalizer (L : Set G) := by
    rw [←d.triality_sourceS_eq_sylow h hH hp m hm (Or.inr ⟨e⟩)]
    exact (le_sup_right.trans le_sup_left).trans
      (d.triality_normalizer_local_data h hH hp m hm e).left_le
  have hRX : (R : Subgroup C) ≤ X := by
    rw [hR]
    exact fun x hx => hTN hx
  have hz : orderOf z = 2 := (Subgroup.orderOf_coe _).trans
    ((e.right.symm.orderOf_eq _).trans (triality_pinned_root_orders m hm).1)
  apply UniqueFixedCoset.unique_of_class_count X p
  · intro g x
    have hc : IsConj x.val (g*x*g⁻¹).val := isConj_iff.mpr ⟨g.val,rfl⟩
    exact ⟨fun h => h.trans hc.symm,fun h => h.trans hc⟩
  · intro x hx
    have hx2 : orderOf x = 2 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hx
      have he := (MulAut.conj g).orderOf_eq z
      change orderOf (g*z*g⁻¹) = orderOf z at he
      rw [hg] at he
      exact (Subgroup.orderOf_coe x).symm.trans (he.trans hz)
    obtain ⟨w,hw⟩ := R.exists_isConj_of_orderOf_eq_prime_pow
      (x := x) (n := 1) (by simpa using hx2)
    obtain ⟨g,hg⟩ := isConj_iff.mp hw
    refine ⟨QuotientGroup.mk g⁻¹,(UniqueFixedCoset.fixed_iff X x g⁻¹).mpr ?_⟩
    simp only [inv_inv]
    change g*x*g⁻¹ ∈ X
    rw [show g*x*g⁻¹=w.val from hg]
    exact hRX w.property
  · exact d.triality_short_long_class_count h hH hp m hm e

/-- F.4.42 for the actual prepared triality row and its given short-root marker. -/
theorem Preparation.triality_short_centralizer_le_normalizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse) :
    centralizer ({(e.right.symm (shortElement (binaryParameters m hm) rfl)).val} : Set G) ≤
      normalizer (L : Set G) := by
  let P := binaryParameters m hm
  let f := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
    e.left.symm.toMonoidHom
  let v := f (TrialityShortAction.short P rfl)
  obtain ⟨hv,hz,_,hc⟩ := d.triality_short_centralizer_of_long_unique_fixed h hH hp m hm e
  have hu := d.triality_short_long_unique_fixed h hH hp m hm e
  dsimp only at hu
  change ∀ x : centralizer ({(e.right.symm (shortElement P rfl)).val} : Set G),
    IsConj (e.right.symm (longElement P rfl)).val x.val →
      ∃! q : centralizer ({(e.right.symm (shortElement P rfl)).val} : Set G) ⧸
        (normalizer (L : Set G)).subgroupOf _, x • q=q at hu
  rw [←hv] at hu
  have hfix := hu (TrialityShortAction.longMark rfl f) (by rw [hz])
  have hh := hc hfix
  rwa [hv] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
