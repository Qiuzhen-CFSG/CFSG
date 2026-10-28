module
public import Theory.GroupTheory.NormalizerActionFixer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Faithful normalizer actions with trivial prime core

If a p-subgroup A normalizes J, its centralizer of J is normalized by A and
centralized by J. It therefore lies in the p-core of J A. Triviality of that
core makes the literal normalizer action of A on J faithful.

Source application: Aschbacher–Smith, Lemma 2.4.34, printed p.548, the faithful
Sylow action on the commuting component pair.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- The pointwise kernel lies in the generated group’s prime core. -/
theorem inf_centralizer_eq_bot_of_sup_pCore_eq_bot {p : ℕ}
    (A J : Subgroup G) (hA : IsPGroup p A)
    (hn : A ≤ normalizer (J : Set G))
    (ho : pCore p (J ⊔ A : Subgroup G) = ⊥) :
    A ⊓ centralizer (J : Set G) = ⊥ := by
  let Q := A ⊓ centralizer (J : Set G)
  have hAQ : A ≤ normalizer (Q : Set G) :=
    (le_inf A.le_normalizer (hn.trans (normalizer_le_normalizer_centralizer J))).trans
      inf_normalizer_le_normalizer_inf
  have hJQ : J ≤ normalizer (Q : Set G) :=
    (le_centralizer_iff.mp (show Q ≤ centralizer (J : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hh := le_pCoreIn_of_normalizes (hA.to_le (show Q ≤ A from inf_le_left))
    ((show Q ≤ A from inf_le_left).trans (show A ≤ J ⊔ A from le_sup_right))
    (sup_le hJQ hAQ)
  rw [pCoreIn,ho,map_bot] at hh
  exact bot_unique hh

/-- The literal normalizer action is faithful when the generated prime core is trivial. -/
theorem normalizer_action_injective_of_sup_pCore_eq_bot {p : ℕ}
    (A J : Subgroup G) (hA : IsPGroup p A)
    (hn : A ≤ normalizer (J : Set G))
    (ho : pCore p (J ⊔ A : Subgroup G) = ⊥) :
    Function.Injective (J.normalizerMonoidHom.comp (inclusion hn)) := by
  apply (J.normalizerMonoidHom.comp (inclusion hn)).ker_eq_bot_iff.mp
  rw [normalizer_action_ker_comap]
  apply eq_bot_iff.mpr
  intro a ha
  have hb := inf_centralizer_eq_bot_of_sup_pCore_eq_bot A J hA hn ho
  have hm : (a : G) ∈ A ⊓ centralizer (J : Set G) := ⟨a.property,ha⟩
  rw [hb] at hm
  exact Subtype.ext (mem_bot.mp hm)


/-- The whole generated group acts faithfully when the normal factor is
centerless and the generated prime core is trivial. -/
theorem join_normalizer_action_injective_of_pCore_eq_bot {p : ℕ}
    (A J : Subgroup G) (hA : IsPGroup p A)
    (hn : A ≤ normalizer (J : Set G)) (hZ : center J = ⊥)
    (ho : pCore p (J ⊔ A : Subgroup G) = ⊥) :
    Function.Injective
      (J.normalizerMonoidHom.comp (inclusion (sup_le J.le_normalizer hn))) := by
  let I := J ⊔ A
  let N := J.subgroupOf I
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le J.le_normalizer hn)
  have hgen : N ⊔ A.subgroupOf I = ⊤ := by
    apply map_injective I.subtype_injective
    rw [map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ← MonoidHom.range_eq_map,range_subtype]
  have hquot : IsPGroup p (I ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (A.subgroupOf I) hA.comap_subtype hgen
  let α : I →* MulAut J := J.normalizerMonoidHom.comp (inclusion (sup_le J.le_normalizer hn))
  let f : α.ker →* I ⧸ N := (QuotientGroup.mk' N).comp α.ker.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro q hq
    have hqJ : ((q : I) : G) ∈ J := (QuotientGroup.eq_one_iff (N := N) (q : I)).mp hq
    have hqC : ((q : I) : G) ∈ centralizer (J : Set G) := by
      exact (normalizer_action_ker_comap J I (sup_le J.le_normalizer hn)).le q.property
    have hz : (⟨((q : I) : G),hqJ⟩ : J) ∈ center J := by
      apply mem_center_iff.mpr
      intro j
      exact Subtype.ext (hqC j j.property)
    rw [hZ] at hz
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun j : J => (j : G)) (mem_bot.mp hz)
  have hp : IsPGroup p α.ker := hquot.of_injective f hf
  apply α.ker_eq_bot_iff.mp
  exact bot_unique ((show α.ker ≤ pCore p I from le_sSup ⟨inferInstance,hp⟩).trans ho.le)

end Subgroup
