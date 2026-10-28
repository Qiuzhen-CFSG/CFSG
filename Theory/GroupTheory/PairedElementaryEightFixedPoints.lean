module
public import Theory.GroupTheory.PairNormalizerIndex
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# Distinct fixed subgroups in an action on two elementary eights

An elementary group of order sixteen acting faithfully on a disjoint pair
of elementary groups of order eight cannot have the same fixed subgroup
for each nonidentity actor. If an actor exchanges the factors, its index-two
factor stabilizer has a nonidentity actor and a nonidentity fixed vector in
the first factor. Constancy would make that vector fixed by the exchanger,
contradicting disjointness. Thus both factors are invariant.

The conjugation action on either factor has nontrivial kernel, since 16 does
not divide |GL₃(2)|=168. Constancy then makes every actor centralize both
factors, contradicting faithfulness on their join.

Source application: Aschbacher--Smith 10.3.2, printed p.756. This formulation
uses the actual factor embeddings and centralizers; no recognition of the
full automizer of the join is needed.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem point_centralizes_of_conjugation_eq_one
    (A U : Subgroup G) (hAN : A ≤ normalizer (U : Set G))
    {a : A} (ha : (U.normalizerMonoidHom.comp (inclusion hAN)) a = 1) :
    (a : G) ∈ centralizer (U : Set G) := by
  intro u hu
  have hh := congrArg (fun f : MulAut U => (f ⟨u,hu⟩ : G)) ha
  change (a : G) * u * (a : G)⁻¹ = u at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem centralizes_of_uniform_fixed_eight
    (A U V : Subgroup G) [IsElementaryAbelian 2 U]
    (hA : Nat.card A = 16) (hU : Nat.card U = 8)
    (hUV : U ≤ V) (hAN : A ≤ normalizer (U : Set G))
    (hfixed : ∀ a ∈ A, a ≠ 1 →
      V ⊓ centralizer ({a} : Set G) = V ⊓ centralizer (A : Set G)) :
    A ≤ centralizer (U : Set G) := by
  let f : A →* MulAut U := U.normalizerMonoidHom.comp (inclusion hAN)
  have hk : f.ker ≠ ⊥ := by
    intro he
    have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp he
    have hd := card_dvd_of_injective f hi
    rw [hA,card_mulAut_of_elementary_eight U hU] at hd
    norm_num at hd
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hk
  have hane : ((a : A) : G) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
  have haC : ((a : A) : G) ∈ centralizer (U : Set G) :=
    point_centralizes_of_conjugation_eq_one A U hAN a.property
  have hUC : U ≤ centralizer (A : Set G) := by
    intro u hu
    have hh : u ∈ V ⊓ centralizer ({((a : A) : G)} : Set G) :=
      ⟨hUV hu, mem_centralizer_singleton_iff.mpr (haC u hu)⟩
    rw [hfixed _ (a : A).property hane] at hh
    exact hh.2
  exact le_centralizer_iff.mp hUC

/-- A faithful elementary sixteen-group permuting two disjoint elementary
eights has distinct nonidentity fixed subgroups on their join. -/
theorem not_uniform_fixed_pair_eight
    (A U W : Subgroup G) [IsElementaryAbelian 2 A]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 W]
    (hA : Nat.card A = 16) (hU : Nat.card U = 8) (hW : Nat.card W = 8)
    (hd : Disjoint U W)
    (hpairU : ∀ a ∈ A, U.map (MulAut.conj a).toMonoidHom = U ∨
      U.map (MulAut.conj a).toMonoidHom = W)
    (hpairW : ∀ a ∈ A, W.map (MulAut.conj a).toMonoidHom = U ∨
      W.map (MulAut.conj a).toMonoidHom = W)
    (hfaith : A ⊓ centralizer ((U ⊔ W : Subgroup G) : Set G) = ⊥)
    (hfixed : ∀ a ∈ A, a ≠ 1 →
      (U ⊔ W) ⊓ centralizer ({a} : Set G) =
        (U ⊔ W) ⊓ centralizer (A : Set G)) : False := by
  have hUbot : U ≠ ⊥ := by intro h; rw [h,card_bot] at hU; omega
  have hAN : A ≤ normalizer (U : Set G) := by
    by_contra hn
    obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
    have hmove : U.map (MulAut.conj t).toMonoidHom ≠ U :=
      fun h => htn (mem_normalizer_iff_map_conj_eq.mpr h)
    have hswap := (hpairU t ht).resolve_left hmove
    let B := A ⊓ normalizer (U : Set G)
    have hi : B.relIndex A = 2 := by
      rw [show B = A ⊓ normalizer (U : Set G) from rfl,inf_relIndex_left]
      exact normalizer_relIndex_eq_two_of_pair A U W hpairU t ht hmove
    have hBbot : B ≠ ⊥ := by
      intro h
      rw [h,relIndex_bot_left,hA] at hi
      omega
    obtain ⟨b,hb⟩ := ne_bot_iff_exists_ne_one.mp hBbot
    have hbne : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
    have hfix := inf_centralizer_ne_bot_of_pGroups B U
      ((IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left)
      (IsElementaryAbelian.isPGroup 2 U) inf_le_right hUbot
    obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hfix
    have huC : (u : G) ∈ centralizer (A : Set G) := by
      have hh : (u : G) ∈ (U ⊔ W) ⊓ centralizer ({(b : G)} : Set G) :=
        ⟨(show U ≤ U ⊔ W from le_sup_left) u.property.1,
          mem_centralizer_singleton_iff.mpr (u.property.2 b b.property).symm⟩
      rw [hfixed b b.property.1 hbne] at hh
      exact hh.2
    have htu : (MulAut.conj t) (u : G) = u := by
      change t * (u : G) * t⁻¹ = u
      rw [huC t ht,mul_inv_cancel_right]
    have huW : (u : G) ∈ W := by
      rw [← hswap, ← htu]
      exact mem_map_of_mem _ u.property.1
    exact hu (Subtype.ext (hd.le_bot ⟨u.property.1,huW⟩))
  have hAW : A ≤ normalizer (W : Set G) := by
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    rcases hpairW a ha with he | he
    · have heU := mem_normalizer_iff_map_conj_eq.mp (hAN ha)
      have hWU : W = U := map_injective (MulAut.conj a).injective (he.trans heU.symm)
      exact (hUbot (by simpa only [hWU,inf_idem] using hd.eq_bot)).elim
    · exact he
  have hACU : A ≤ centralizer (U : Set G) :=
    centralizes_of_uniform_fixed_eight A U (U ⊔ W) hA hU le_sup_left hAN hfixed
  have hACW : A ≤ centralizer (W : Set G) :=
    centralizes_of_uniform_fixed_eight A W (U ⊔ W) hA hW le_sup_right hAW hfixed
  have hACV : A ≤ centralizer ((U ⊔ W : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hACU)
      (le_centralizer_iff.mp hACW))
  have hAbot : A = ⊥ := by rw [← inf_of_le_left hACV,hfaith]
  rw [hAbot,card_bot] at hA
  omega

end Subgroup
