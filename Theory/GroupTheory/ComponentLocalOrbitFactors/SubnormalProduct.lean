module

public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.Commutator.SubnormalAbsorption
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Subnormal p-perfect subgroups of direct powers

Let K be finite and perfect with simple quotient by a normal p-subgroup.
Every nontrivial subnormal p-perfect subgroup of K is K: its image in the
simple quotient is nontrivial, and the subnormal p-supplement theorem then
identifies it with the p-residual of K.

A nontrivial subgroup of a direct power has a nontrivial coordinate image.
For a subnormal p-perfect subgroup that image is K. Commutators with the
corresponding coordinate factor generate that factor, so subnormal
commutator absorption places the factor in the subgroup.

This is the abstract product calculation needed for the large Ree case of
Aschbacher–Smith, 2.3.9(7), combined manuscript (1 March 2004), printed p.526.
The actual component-orbit embeddings are constructed by the importing module.
-/

namespace Subgroup
open scoped commutatorElement

private theorem perfect_isPPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] (p : ℕ) [Fact p.Prime] : IsPPerfect p G := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (G ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- A nontrivial subnormal p-perfect subgroup of a finite perfect group with
simple quotient by a normal p-subgroup is the whole group. -/
public theorem eq_top_of_isSubnormal_isPPerfect_of_simple_quotient {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] {p : ℕ} [Fact p.Prime]
    (Q : Subgroup G) [Q.Normal] [IsSimpleGroup (G ⧸ Q)]
    (hQ : IsPGroup p Q) (N : Subgroup G) (hs : N.IsSubnormal)
    (hp : IsPPerfect p N) (hne : N ≠ ⊥) : N = ⊤ := by
  let q := QuotientGroup.mk' Q
  rcases (hs.map (QuotientGroup.mk'_surjective Q)).eq_bot_or_top_of_isSimpleGroup
      inferInstance with hz | ht
  · have hNQ : N ≤ Q := by
      simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp hz
    have hquot : IsPGroup p (N ⧸ (⊥ : Subgroup N)) :=
      (hQ.to_le hNQ).of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _)
    have hbot : (⊥ : Subgroup N) = ⊤ := hp _ inferInstance hquot
    apply (hne _).elim
    apply le_bot_iff.mp
    intro x hx
    have hh : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := hbot.symm ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hh)
  · have hprod : ∀ g : G, ∃ n ∈ N, ∃ r ∈ Q, n * r = g := by
      intro g
      obtain ⟨n, hn, he⟩ := mem_map.mp (show q g ∈ N.map q by rw [ht]; trivial)
      exact ⟨n, hn, n⁻¹ * g, QuotientGroup.eq.mp he, mul_inv_cancel_left n g⟩
    have he := pResidual_eq_of_subnormal_product N Q hs hp hQ hprod
    rw [(pResidual_eq_top_iff p G).mpr (perfect_isPPerfect p)] at he
    exact he.symm

/-- A nontrivial subnormal p-perfect subgroup of a direct power contains one
coordinate factor when the finite perfect factor is simple modulo a normal p-subgroup. -/
public theorem exists_mulSingle_mem_of_isSubnormal_isPPerfect {K ι : Type*} [DecidableEq ι] [Group K] [Finite K]
    [Group.IsPerfect K] {p : ℕ} [Fact p.Prime]
    (Q : Subgroup K) [Q.Normal] [IsSimpleGroup (K ⧸ Q)]
    (hQ : IsPGroup p Q) (B : Subgroup (ι → K)) (hs : B.IsSubnormal)
    (hp : IsPPerfect p B) (hne : B ≠ ⊥) :
    ∃ i : ι, ∀ x : K, Pi.mulSingle i x ∈ B := by
  classical
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra! hh
    exact hne (eq_bot_iff.mpr fun b hb => mem_bot.mpr (hh b hb))
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 1 := by
    by_contra! hh
    exact hb1 (funext hh)
  let ev : (ι → K) →* K := Pi.evalMonoidHom (fun _ : ι => K) i
  have hev : Function.Surjective ev := fun x => ⟨fun _ => x, rfl⟩
  have himage : B.map ev = ⊤ := by
    apply eq_top_of_isSubnormal_isPPerfect_of_simple_quotient Q hQ _ (hs.map hev)
      (hp.of_surjective (ev.subgroupMap B) (ev.subgroupMap_surjective B))
    intro hz
    have hh := mem_map_of_mem ev hb
    rw [hz, mem_bot] at hh
    exact hi hh
  let f : K →* (ι → K) := MonoidHom.mulSingle (fun _ : ι => K) i
  have hcomm : (_root_.commutator K).map f ≤ ⁅f.range, B⁆ := by
    rw [map_le_iff_le_comap, _root_.commutator_def, commutator_le]
    intro x _ y _
    obtain ⟨c, hc, hci⟩ := mem_map.mp (show y ∈ B.map ev by rw [himage]; trivial)
    change f ⁅x, y⁆ ∈ ⁅f.range, B⁆
    have he : f ⁅x, y⁆ = ⁅f x, c⁆ := by
      ext j
      by_cases hij : i = j
      · subst j
        simpa [f, ev, commutatorElement_def] using congrArg (fun z => x * z * x⁻¹ * z⁻¹) hci.symm
      · simp [f, commutatorElement_def, Pi.mulSingle_eq_of_ne (Ne.symm hij)]
    rw [he]
    exact commutator_mem_commutator ⟨x, rfl⟩ hc
  have hstable : f.range ≤ ⁅f.range, B⁆ := by
    simpa only [Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map] using hcomm
  exact ⟨i, fun x => le_of_isSubnormal_of_le_commutator f.range B hs hstable ⟨x, rfl⟩⟩

end Subgroup
