module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.CyclicNormalCentralizer

/-!
# The action of a perfect group on a small noncentral odd core

A supercritical subgroup detects the nontrivial action. Rank one would make
that core cyclic and hence centralized by a perfect group. At rank two,
A.1.29 gives an actual surjection onto a prime-field SL₂ group. Only the
rank of this particular prime core is needed; no global strong quasithinness
assumption occurs.

Source: Aschbacher–Smith A.1.21, A.1.25 and A.1.29, applied in A.2.12,
printed pp.35–36. The supercritical calculation follows the already proved
A.3.6 prime-support argument with its precise local rank hypothesis.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.RankActions
namespace CFSG.Quasithin.ChapterA.Section02
variable {A : Type*} [Group A] [Finite A]

/-- A perfect actor cannot have nontrivial image in the supercritical p-kernel. -/
private theorem noncentral_supercritical [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (S : Subgroup A) [S.Characteristic] (hS : IsPGroup p S)
    (X : Subgroup S) (hX : IsSupercriticalPSubgroup p X)
    (hn : ¬ S ≤ center A) : ¬ X.map S.subtype ≤ center A := by
  let : X.Characteristic := hX.characteristic
  intro hc
  let a : A →* MulAut S := MulAut.conjNormal
  have hrange : a.range ≤ (MulAut.characteristic X).ker := by
    rintro _ ⟨g, rfl⟩
    apply MonoidHom.mem_ker.mpr
    ext x
    change g * ((x : S) : A) * g⁻¹ = ((x : S) : A)
    have hx : ((x : S) : A) ∈ X.map S.subtype := mem_map.mpr ⟨x, x.property, rfl⟩
    rw [mem_center_iff.mp (hc hx) g, mul_inv_cancel_right]
  have hpg : IsPGroup p a.range := (hX.isPGroup_restriction_kernel hS hp).to_le hrange
  let : Group.IsNilpotent a.range := hpg.isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hne
    exact Group.IsPerfect.not_isNilpotent a.range inferInstance
  apply hn
  intro x hx
  apply mem_center_iff.mpr
  intro g
  have he := congrArg (fun f : a.range => ((f : MulAut S) ⟨x,hx⟩ : A))
    (Subsingleton.elim (a.rangeRestrict g) 1)
  change g * x * g⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- Keep the congruence information in the actual supercritical action models. -/
theorem perfect_core_action_models [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hcore : primeRank p (pCore p A) ≤ 2) (hn : ¬ pCore p A ≤ center A) :
    3 < p ∧
      ((∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p), Function.Surjective f) ∨
        ((p % 5 = 1 ∨ p % 5 = 4) ∧
          ∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), Function.Surjective f)) := by
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := hp; omega
  obtain ⟨X, hX⟩ := (pCore_isPGroup (p := p) (G := A)).exists_supercriticalPSubgroup hp2
  let : X.Characteristic := hX.characteristic
  let P := X.map (pCore p A).subtype
  let e : X ≃* P := X.equivMapOfInjective _ (pCore p A).subtype_injective
  have hP : IsPGroup p P := (pCore_isPGroup.to_subgroup X).map (pCore p A).subtype
  have hnc : ¬ P ≤ center A := noncentral_supercritical hp _ pCore_isPGroup X hX hn
  have ho : omega₁ P (p := p) = ⊤ := by
    apply top_unique
    intro y _
    apply Subgroup.subset_closure
    change y ^ (p ^ 1) = 1
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [pow_one, ← map_pow, map_one] using congrArg e (hX.pow_eq_one x)
  have hc : _root_.commutator P ≤ center P := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    apply mem_center_iff.mpr
    intro z
    apply e.symm.injective
    have hh := mem_center_iff.mp (hX.derived_le_center
      (commutator_mem_commutator (mem_top (e.symm x)) (mem_top (e.symm y)))) (e.symm z)
    simpa only [map_mul, map_commutatorElement] using hh
  have hr : primeRank p P = 2 := by
    have hle : primeRank p (pCore p A) ≤ 2 :=
      hcore
    have hgt : 1 < primeRank p (pCore p A) := by
      by_contra! hh
      let : IsCyclic (pCore p A) := pCore_isPGroup.isCyclic_of_odd_of_elementary_card_le hp
        (fun E hE => by
          let : IsElementaryAbelian p E := hE
          exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hh E)
      have hz : (⊤ : Subgroup A) ≤ centralizer (pCore p A : Set A) := by
        simpa only [Group.IsPerfect.commutator_eq_top] using
          commutator_le_centralizer_of_isCyclic_normal (pCore p A)
      apply hn
      intro x hx
      apply mem_center_iff.mpr
      intro g
      exact (hz (mem_top g) x hx).symm
    rw [← primeRank_congr p e, hX.primeRank_eq_of_le_two pCore_isPGroup hp hle]
    omega
  have hnon : ⁅P, (⊤ : Subgroup A)⁆ ≠ ⊥ := fun h =>
    hnc (commutator_top_right_eq_bot_iff_le_center.mp h)
  refine ⟨three_lt_of_perfect_action P ⊤ hp2 hP ho hc hr hnon, ?_⟩
  have hm := CFSG.Quasithin.ChapterA.lemma_A_1_29_1 P ⊤ hp hP ho hc hr hnon
  have step {r : ℕ}
      (j : ((⊤ : Subgroup A) ⧸ frattiniCentralizer P ⊤) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) :
      ∃ f : A →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r), Function.Surjective f := by
    let q : A →* (⊤ : Subgroup A) := topEquiv.symm.toMonoidHom
    exact ⟨j.toMonoidHom.comp ((QuotientGroup.mk' (frattiniCentralizer P ⊤)).comp q),
      j.surjective.comp ((QuotientGroup.mk'_surjective _).comp topEquiv.symm.surjective)⟩
  exact hm.imp (fun hj => step hj.some) (fun ⟨hm, hj⟩ => ⟨hm, step hj.some⟩)

end CFSG.Quasithin.ChapterA.Section02
