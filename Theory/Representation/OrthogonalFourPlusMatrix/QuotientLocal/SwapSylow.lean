module

public import Theory.Representation.OrthogonalFourPlusMatrix.QuotientLocal.DiagonalCore
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Sylow saturation of a marked component exchange

For a finite centerless quasisimple group S, a Sylow two-subgroup of
Aut(S × S) containing the factor swap is J ≀ C₂ for a Sylow two-subgroup J
of Aut(S). Indeed, project its factor-preserving part to one coordinate;
the swap identifies the two projections. Enlarge that projection to J and
apply Sylow maximality to the resulting wreath two-group. Restriction to
the fixed diagonal then proves maximality in the swap centralizer.

For S = A₅, the inner automorphisms have index two in Aut(S) = S₅. Every
overgroup of the inner square containing the swap therefore meets the full
swap centralizer in a normal subgroup of index at most two. Extend the
specified Sylow to the full automorphism group, restrict its centralizer
Sylow along this normal inclusion, and pull back through the faithful
action. These operations preserve the original Sylow and marked element.
No classification of outer overgroups or finite enumeration is needed.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, using the component
exchange in 14.4.2(3), printed pp.1006–1007, and G.11.2(7). This module
proves the group calculation used in the local Sylow step, independently
of the natural orthogonal representation.
-/

public section

open Subgroup Theory.GroupTheory
namespace ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
variable {S : Type*} [Group S]

private def pairAut : (MulAut S × MulAut S) →* MulAut (S × S) where
  toFun ab := ab.1.prodCongr ab.2
  map_one' := by ext x <;> rfl
  map_mul' _ _ := rfl

private theorem pairAut_injective : Function.Injective (pairAut (S := S)) := by
  intro a b h
  apply Prod.ext
  · ext s
    exact congrArg Prod.fst (MulEquiv.congr_fun h (s,1))
  · ext s
    exact congrArg Prod.snd (MulEquiv.congr_fun h (1,s))

private theorem pair_swap_mul (a b c d : MulAut S) :
    (pairAut (a,b) * swap) * (pairAut (c,d) * swap) = pairAut (a*d,b*c) := rfl

private def wreath (J : Subgroup (MulAut S)) : Subgroup (MulAut (S × S)) where
  carrier := {f | (∃ a ∈ J, ∃ b ∈ J, f = pairAut (a,b)) ∨
    (∃ a ∈ J, ∃ b ∈ J, f = pairAut (a,b) * swap)}
  one_mem' := Or.inl ⟨1,J.one_mem,1,J.one_mem,rfl⟩
  mul_mem' := by
    rintro f g (⟨a,ha,b,hb,rfl⟩ | ⟨a,ha,b,hb,rfl⟩)
      (⟨c,hc,d,hd,rfl⟩ | ⟨c,hc,d,hd,rfl⟩)
    · exact Or.inl ⟨a*c,J.mul_mem ha hc,b*d,J.mul_mem hb hd,rfl⟩
    · exact Or.inr ⟨a*c,J.mul_mem ha hc,b*d,J.mul_mem hb hd,rfl⟩
    · exact Or.inr ⟨a*d,J.mul_mem ha hd,b*c,J.mul_mem hb hc,rfl⟩
    · exact Or.inl ⟨a*d,J.mul_mem ha hd,b*c,J.mul_mem hb hc,rfl⟩
  inv_mem' := by
    rintro f (⟨a,ha,b,hb,rfl⟩ | ⟨a,ha,b,hb,rfl⟩)
    · exact Or.inl ⟨a⁻¹,J.inv_mem ha,b⁻¹,J.inv_mem hb,rfl⟩
    · exact Or.inr ⟨b⁻¹,J.inv_mem hb,a⁻¹,J.inv_mem ha,rfl⟩

private theorem pair_pow (a b : MulAut S) (n : ℕ) :
    pairAut (a,b) ^ n = pairAut (a^n,b^n) := (map_pow pairAut (a,b) n).symm

private theorem pair_pow_two_power (J : Subgroup (MulAut S)) (hJ : IsPGroup 2 J)
    (a b : MulAut S) (ha : a ∈ J) (hb : b ∈ J) :
    ∃ n : ℕ, pairAut (a,b) ^ (2^n) = 1 := by
  obtain ⟨m,hm⟩ := hJ ⟨a,ha⟩
  obtain ⟨n,hn⟩ := hJ ⟨b,hb⟩
  refine ⟨m+n, ?_⟩
  rw [pair_pow]
  have hma : a ^ (2^m) = 1 := congrArg Subtype.val hm
  have hnb : b ^ (2^n) = 1 := congrArg Subtype.val hn
  have ha' : a ^ (2^(m+n)) = 1 := by rw [pow_add, pow_mul, hma, one_pow]
  have hb' : b ^ (2^(m+n)) = 1 := by rw [Nat.add_comm m n, pow_add, pow_mul, hnb, one_pow]
  rw [ha',hb']
  rfl

private theorem wreath_isPGroup (J : Subgroup (MulAut S)) (hJ : IsPGroup 2 J) :
    IsPGroup 2 (wreath J) := by
  rintro ⟨f, (⟨a,ha,b,hb,rfl⟩ | ⟨a,ha,b,hb,rfl⟩)⟩
  · obtain ⟨n,hn⟩ := pair_pow_two_power J hJ a b ha hb
    exact ⟨n, Subtype.ext hn⟩
  · obtain ⟨n,hn⟩ := pair_pow_two_power J hJ (a*b) (b*a) (J.mul_mem ha hb) (J.mul_mem hb ha)
    refine ⟨n+1, Subtype.ext ?_⟩
    change (pairAut (a,b) * swap) ^ (2^(n+1)) = 1
    rw [pow_succ, Nat.mul_comm (2^n) 2, pow_mul, pow_two, pair_swap_mul]
    exact hn

private def diagonalLift : MulAut S →* SwapCentralizer S where
  toFun a := ⟨pairAut (a,a), by
    apply mem_centralizer_singleton_iff.mpr
    rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem diagonalAction_surjective : Function.Surjective (diagonalAction (S := S)) :=
  fun a => ⟨diagonalLift a,rfl⟩
variable [Finite S] [IsQuasisimple S]

private theorem mem_wreath_iff (hZ : center S = ⊥) (J : Subgroup (MulAut S))
    (f : SwapCentralizer S) : f.val ∈ wreath J ↔ diagonalAction f ∈ J := by
  have hcoord (a b : MulAut S)
      (h : f.val = pairAut (a,b) ∨ f.val = pairAut (a,b) * swap) :
      diagonalAction f = a ∧ b = a := by
    constructor
    · ext s
      rcases h with h | h <;>
        change (f.val (s,s)).1 = a s <;> rw [h] <;> rfl
    · ext s
      have hh := diagonal_fixed f s
      rcases h with h | h <;> rw [h] at hh <;> exact hh
  constructor
  · rintro (⟨a,ha,b,hb,h⟩ | ⟨a,ha,b,hb,h⟩)
    · rwa [(hcoord a b (.inl h)).1]
    · rwa [(hcoord a b (.inr h)).1]
  · intro hf
    rcases AutomorphismSquare.normal_form hZ f.val with ⟨a,b,h⟩ | ⟨a,b,h⟩
    · obtain ⟨he,hba⟩ := hcoord a b (.inl h)
      subst b
      rw [he] at hf
      exact Or.inl ⟨a,hf,a,hf,h⟩
    · obtain ⟨he,hba⟩ := hcoord a b (.inr h)
      subst b
      rw [he] at hf
      exact Or.inr ⟨a,hf,a,hf,h⟩

private theorem sylow_eq_wreath (hZ : center S = ⊥)
    (P : Sylow 2 (MulAut (S × S))) (hi : swap ∈ P) :
    ∃ J : Sylow 2 (MulAut S), (P : Subgroup _) = wreath (J : Subgroup (MulAut S)) := by
  -- The swap identifies the two coordinate projections of the base intersection.
  let B := (P : Subgroup (MulAut (S × S))).comap pairAut
  let J := B.map (MonoidHom.fst (MulAut S) (MulAut S))
  have hJ : IsPGroup 2 J :=
    (P.isPGroup'.comap_of_injective pairAut pairAut_injective).map _
  obtain ⟨R,hJR⟩ := hJ.exists_le_sylow
  have hc (a b : MulAut S) (hab : pairAut (a,b) ∈ P) : a ∈ R ∧ b ∈ R := by
    constructor
    · exact hJR ⟨(a,b),hab,rfl⟩
    · apply hJR
      refine ⟨(b,a), ?_,rfl⟩
      change pairAut (b,a) ∈ P
      have hh := P.mul_mem (P.mul_mem hi hab) hi
      exact hh
  refine ⟨R, (P.is_maximal' (wreath_isPGroup _ R.isPGroup') ?_).symm⟩
  intro f hf
  rcases AutomorphismSquare.normal_form hZ f with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩
  · obtain ⟨ha,hb⟩ := hc a b hf
    exact Or.inl ⟨a,ha,b,hb,rfl⟩
  · have hab : pairAut (a,b) ∈ P := P.mul_mem hf hi
    obtain ⟨ha,hb⟩ := hc a b hab
    exact Or.inr ⟨a,ha,b,hb,rfl⟩

/-- The specified Sylow containing the pure exchange has a Sylow intersection
with its full automorphism-group centralizer. -/
theorem swap_centralizer_sylow (hZ : center S = ⊥)
    (P : Sylow 2 (MulAut (S × S))) (hi : swap ∈ P) :
    ∃ R : Sylow 2 (SwapCentralizer S),
      (R : Subgroup _) = (P : Subgroup _).subgroupOf (SwapCentralizer S) := by
  obtain ⟨J,hJ⟩ := sylow_eq_wreath hZ P hi
  refine ⟨⟨(P : Subgroup _).subgroupOf (SwapCentralizer S),
    P.isPGroup'.comap_subtype, ?_⟩,rfl⟩
  intro R hR hPR
  have hJR : (J : Subgroup _) ≤ R.map diagonalAction := by
    intro a ha
    refine ⟨diagonalLift a, hPR ?_,rfl⟩
    change (diagonalLift a).val ∈ (P : Subgroup _)
    rw [hJ, mem_wreath_iff hZ]
    exact ha
  have hmap := J.is_maximal' (hR.map diagonalAction) hJR
  apply le_antisymm _ hPR
  intro f hf
  change f.val ∈ (P : Subgroup _)
  rw [hJ,mem_wreath_iff hZ]
  rw [← hmap]
  exact mem_map_of_mem _ hf

local notation "Factor" => alternatingGroup (Fin 5)

private instance : IsQuasisimple Factor where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem factor_center : center Factor = ⊥ :=
  alternatingGroup.center_eq_bot (by simp)

private theorem inner_index :
    (MulAut.conj : Factor →* MulAut Factor).range.index = 2 := by
  have hinj := conj_injective_of_center_eq_bot factor_center
  have hc : Nat.card (MulAut.conj : Factor →* MulAut Factor).range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    rw [nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hA : Nat.card (MulAut Factor) = 120 := by
    rw [← Nat.card_congr
      Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have h := (MulAut.conj : Factor →* MulAut Factor).range.card_mul_index
  rw [hc,hA] at h
  omega

private theorem range_centralizer_normal (A : Subgroup (MulAut (Factor × Factor)))
    (hinner : (MulAut.conj : Factor × Factor →* MulAut (Factor × Factor)).range ≤ A)
    (hi : swap ∈ A) : (A.subgroupOf (SwapCentralizer Factor)).Normal := by
  let N := (MulAut.conj : Factor →* MulAut Factor).range
  have hN : N.comap diagonalAction ≤ A.subgroupOf (SwapCentralizer Factor) := by
    intro f hf
    have hf' := (mem_wreath_iff factor_center N f).mpr hf
    change f.val ∈ A
    rcases hf' with ⟨a,⟨s,hs⟩,b,⟨t,ht⟩,h⟩ | ⟨a,⟨s,hs⟩,b,⟨t,ht⟩,h⟩
    · rw [h,← hs,← ht]
      exact hinner ⟨(s,t),rfl⟩
    · rw [h,← hs,← ht]
      exact A.mul_mem (hinner ⟨(s,t),rfl⟩) hi
  -- The preimage of the inner automorphisms already has index two.
  have hd : (A.subgroupOf (SwapCentralizer Factor)).index ∣ 2 := by
    have h := index_dvd_of_le hN
    rw [N.index_comap_of_surjective diagonalAction_surjective,inner_index] at h
    exact h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · rw [index_eq_one.mp h]
    infer_instance
  · exact normal_of_index_eq_two h

/-- A faithful overgroup of the inner A₅ square has a Sylow intersection
with the centralizer of its marked component swap. Both P and i are retained. -/
theorem exists_swap_centralizer_sylow {Q : Type*} [Group Q] [Finite Q]
    (ρ : Q →* MulAut (Factor × Factor)) (hρ : Function.Injective ρ)
    (hinner : (MulAut.conj : Factor × Factor →* MulAut (Factor × Factor)).range ≤ ρ.range)
    (P : Sylow 2 Q) (i : Q) (hiP : i ∈ P) (hi : ρ i = swap) :
    ∃ R : Sylow 2 (centralizer ({i} : Set Q)),
      (R : Subgroup _) = (P : Subgroup Q).subgroupOf (centralizer ({i} : Set Q)) := by
  -- Extend P while retaining its exact preimage under the original action.
  obtain ⟨U,hU⟩ := P.exists_comap_eq_of_injective hρ
  have hiU : swap ∈ U := by
    rw [← hi]
    change i ∈ (U : Subgroup _).comap ρ
    rw [hU]
    exact hiP
  obtain ⟨R,hR⟩ := swap_centralizer_sylow factor_center U hiU
  let A := ρ.range.subgroupOf (SwapCentralizer Factor)
  let _ : A.Normal := range_centralizer_normal ρ.range hinner ⟨i,hi⟩
  obtain ⟨T,hT⟩ := R.exists_subgroupOf_eq_of_normal A
  let f : centralizer ({i} : Set Q) →* A := {
    toFun x := ⟨⟨ρ x, by
      apply mem_centralizer_singleton_iff.mpr
      rw [← hi, ← map_mul, ← map_mul]
      exact congrArg ρ (mem_centralizer_singleton_iff.mp x.property)⟩, ⟨x,rfl⟩⟩
    map_one' := Subtype.ext (Subtype.ext ρ.map_one)
    map_mul' x y := Subtype.ext (Subtype.ext (ρ.map_mul x y)) }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (hρ (congrArg (fun a : A => (a.val : MulAut (Factor × Factor))) h))
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨q,hq⟩ := x.property
    have hqc : q ∈ centralizer ({i} : Set Q) := by
      apply mem_centralizer_singleton_iff.mpr
      apply hρ
      rw [map_mul,map_mul,hi,hq]
      exact mem_centralizer_singleton_iff.mp x.val.property
    exact ⟨⟨q,hqc⟩, Subtype.ext (Subtype.ext hq)⟩
  refine ⟨T.comapOfInjective f hf (by rw [f.range_eq_top_of_surjective hsurj]; exact le_top), ?_⟩
  change (T : Subgroup A).comap f = _
  rw [hT,hR]
  ext x
  change ρ x.val ∈ U ↔ x.val ∈ P
  change x.val ∈ (U : Subgroup _).comap ρ ↔ x.val ∈ P
  rw [hU]
  rfl

end ClassicalOrthogonal.FourPlusMatrix.QuotientLocal
