module

public import Theory.PGroupCore
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber

/-!
# Faithful actions in extensions with p-group quotient

For a centerless normal subgroup K, its centralizer embeds in H/K. If the
quotient is a p-group, the normal centralizer therefore lies in Oₚ(H).
When that core is trivial, conjugation on K is faithful. Transport through
an actual equivalence K ≃ A then transfers two-signalizer vanishing from
Aut(A) to H, keeping the marked subgroup of K.

This is the general extension step used for PSL₃(5) in Aschbacher–Smith,
proof of 1.3.8, printed p.513. It makes no assumption that H acts by inner
automorphisms and does not prove the separate model vanishing hypothesis.
-/

public section

open Subgroup

namespace Subgroup

theorem centralizer_le_pCore_of_centerless_quotient
    {H : Type*} [Group H] (p : ℕ) (K : Subgroup H) [K.Normal]
    (hZ : center K = ⊥) (hquot : IsPGroup p (H ⧸ K)) :
    centralizer (K : Set H) ≤ pCore p H := by
  let C := centralizer (K : Set H)
  let f : C →* H ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxK : (x : H) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
    have hxZ : (⟨x, hxK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact x.property y y.property
    have hx1 : (⟨x, hxK⟩ : K) = 1 := by simpa only [hZ, mem_bot] using hxZ
    apply mem_bot.mpr
    apply Subtype.ext
    exact congrArg (fun k : K => (k : H)) hx1
  exact le_sSup ⟨inferInstance, hquot.of_injective f hf⟩

theorem normalConjThrough_injective_of_centerless_quotient
    {H A : Type*} [Group H] [Group A] (p : ℕ)
    (K : Subgroup H) [K.Normal] (e : K ≃* A)
    (hZ : center A = ⊥) (hquot : IsPGroup p (H ⧸ K))
    (hcore : pCore p H = ⊥) : Function.Injective (normalConjThrough K e) := by
  have hKZ : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : e x ∈ center A := (centerCongr e ⟨x, hx⟩).property
    have he1 : e x = 1 := by simpa only [hZ, mem_bot] using he
    exact mem_bot.mpr (e.injective (he1.trans e.map_one.symm))
  have hC : centralizer (K : Set H) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore]
    exact centralizer_le_pCore_of_centerless_quotient p K hKZ hquot
  exact (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K hC)

theorem normalConjThrough_map (H A : Type*) [Group H] [Group A]
    (K : Subgroup H) [K.Normal] (e : K ≃* A) (Q : Subgroup K) :
    (Q.map K.subtype).map (normalConjThrough K e) =
      (Q.map e.toMonoidHom).map (MulAut.conj : A →* MulAut A) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro q
  exact normalConjThrough_coe K e q

theorem twoSignalizer_eq_bot_of_model
    {H A : Type*} [Group H] [Group A]
    (K : Subgroup H) [K.Normal] (e : K ≃* A)
    (hZ : center A = ⊥) (hquot : IsPGroup 2 (H ⧸ K))
    (hcore : pCore 2 H = ⊥) (Q : Subgroup K)
    (hmodel : ∀ U : Subgroup (MulAut A), IsPGroup 2 U →
      (Q.map e.toMonoidHom).map (MulAut.conj : A →* MulAut A) ≤ normalizer (U : Set (MulAut A)) →
      U = ⊥)
    (S : Subgroup H) (hS : IsPGroup 2 S)
    (hn : Q.map K.subtype ≤ normalizer (S : Set H)) : S = ⊥ := by
  let f := normalConjThrough K e
  have hf := normalConjThrough_injective_of_centerless_quotient 2 K e hZ hquot hcore
  apply (S.map_eq_bot_iff_of_injective hf).mp
  apply hmodel _ (hS.map f)
  rw [← normalConjThrough_map H A K e Q]
  exact (map_mono hn).trans (S.le_normalizer_map f)

end Subgroup
