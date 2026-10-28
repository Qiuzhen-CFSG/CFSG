module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Two-rank of automorphisms of a simple-group square

For a finite centerless quasisimple group `S`, every automorphism of `S × S`
acts separately on the two coordinate factors or interchanges them. This is
proved from the normal-kernel dichotomy for endomorphisms of `S`: a nontrivial
coordinate map is bijective, and the commuting other factor has central image.

The factor-preserving automorphisms form the image of the injective product
map `Aut(S) × Aut(S) → Aut(S × S)`. For an abelian subgroup containing a
factor-interchanging element, its factor-preserving subgroup has index at most
two. Its action on the first factor is faithful: commutation with the
interchanging element determines the second factor action. These two branches
give ranks at most `2r` and `r + 1`, respectively. For `r > 0` both are at most
`2r`. The elementary-abelian characterization of prime rank completes the proof.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, G.9.3, printed p.356 (PDF p.367).
-/

open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory.AutomorphismSquare
variable {S : Type*} [Group S]

private def diagonal : (MulAut S × MulAut S) →* MulAut (S × S) where
  toFun ab := ab.1.prodCongr ab.2
  map_one' := by ext x <;> rfl
  map_mul' := by intros; rfl

private theorem diagonal_injective : Function.Injective (diagonal (S := S)) := by
  intro a b h
  apply Prod.ext
  · apply MulEquiv.ext
    intro x
    exact congrArg Prod.fst (DFunLike.congr_fun h (x, 1))
  · apply MulEquiv.ext
    intro x
    exact congrArg Prod.snd (DFunLike.congr_fun h (1, x))

private def swap : MulAut (S × S) := MulEquiv.prodComm

private def leftMap (f : MulAut (S × S)) : S →* S :=
  (MonoidHom.fst S S).comp (f.toMonoidHom.comp (MonoidHom.inl S S))

private def rightMap (f : MulAut (S × S)) : S →* S :=
  (MonoidHom.snd S S).comp (f.toMonoidHom.comp (MonoidHom.inr S S))

private lemma map_pair (f : MulAut (S × S)) (x y : S) :
    f (x, y) = f (x, 1) * f (1, y) := by
  rw [← map_mul]
  simp

private lemma cross_commute (f : MulAut (S × S)) (x y : S) :
    f (x, 1) * f (1, y) = f (1, y) * f (x, 1) := by
  rw [← map_mul, ← map_mul]
  simp

variable [Finite S]

private lemma diagonal_of_right_fst (hZ : center S = ⊥) (f : MulAut (S × S))
    (hf : ∀ y, (f (1, y)).1 = 1) : ∃ a b : MulAut S, f = diagonal (a, b) := by
  have hi : Function.Injective (rightMap f) := by
    intro x y h
    have hh : f (1, x) = f (1, y) := Prod.ext (by rw [hf, hf]) h
    exact congrArg Prod.snd (f.injective hh)
  have hs := (Finite.injective_iff_surjective).mp hi
  have hleft : ∀ x, (f (x, 1)).2 = 1 := by
    intro x
    apply mem_bot.mp
    rw [← hZ, mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hs z
    exact (congrArg Prod.snd (cross_commute f x y)).symm
  have hi' : Function.Injective (leftMap f) := by
    intro x y h
    have hh : f (x, 1) = f (y, 1) := Prod.ext h (by rw [hleft, hleft])
    exact congrArg Prod.fst (f.injective hh)
  let a := MulEquiv.ofBijective (leftMap f) ⟨hi', Finite.surjective_of_injective hi'⟩
  let b := MulEquiv.ofBijective (rightMap f) ⟨hi, hs⟩
  refine ⟨a, b, ?_⟩
  ext ⟨x, y⟩
  · change (f (x, y)).1 = (f (x, 1)).1
    rw [map_pair]
    simp [hf]
  · change (f (x, y)).2 = (f (1, y)).2
    rw [map_pair]
    simp [hleft]

private lemma endomorphism_dichotomy [IsQuasisimple S] (hZ : center S = ⊥) (f : S →* S) :
    Function.Bijective f ∨ f = 1 := by
  rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with h | h
  · have hi : Function.Injective f := f.ker_eq_bot_iff.mp (bot_unique (hZ ▸ h))
    exact Or.inl ⟨hi, Finite.surjective_of_injective hi⟩
  · exact Or.inr (MonoidHom.ker_eq_top_iff.mp h)

/-- Automorphisms preserve or interchange the two actual coordinate factors.
The two factor maps are automorphisms of `S`, not abstract family labels. -/
public theorem normal_form [IsQuasisimple S] (hZ : center S = ⊥) (f : MulAut (S × S)) :
    (∃ a b : MulAut S, f = a.prodCongr b) ∨
    (∃ a b : MulAut S, f = a.prodCongr b * (MulEquiv.prodComm : MulAut (S × S))) := by
  rcases endomorphism_dichotomy hZ (leftMap f) with h | h
  · left
    apply diagonal_of_right_fst hZ f
    intro y
    apply mem_bot.mp
    rw [← hZ, mem_center_iff]
    intro z
    obtain ⟨x, rfl⟩ := h.surjective z
    exact congrArg Prod.fst (cross_commute f x y)
  · right
    have hf : ∀ x, (f (x, 1)).1 = 1 := fun x => DFunLike.congr_fun h x
    obtain ⟨a, b, hab⟩ := diagonal_of_right_fst hZ (f * swap) (by
      intro y
      exact hf y)
    refine ⟨a, b, ?_⟩
    ext ⟨x, y⟩
    · exact congrArg Prod.fst (DFunLike.congr_fun hab (y, x))
    · exact congrArg Prod.snd (DFunLike.congr_fun hab (y, x))

omit [Finite S] in
private lemma swapped_mul_swapped (a b c d : MulAut S) :
    (diagonal (a, b) * swap) * (diagonal (c, d) * swap) = diagonal (a * d, b * c) := by
  rfl

omit [Finite S] in
private lemma diagonal_eq_one_of_commute (a b c d : MulAut S) (ha : a = 1)
    (hc : diagonal (a, b) * (diagonal (c, d) * swap) =
      (diagonal (c, d) * swap) * diagonal (a, b)) : diagonal (a, b) = 1 := by
  have hb : b = 1 := by
    ext y
    apply c.injective
    have hh := congrArg Prod.fst (DFunLike.congr_fun hc (1, y))
    change a (c y) = c (b y) at hh
    rw [ha] at hh
    exact hh.symm
  rw [ha, hb]
  exact diagonal.map_one

private noncomputable def coordinates : (diagonal (S := S)).range ≃* (MulAut S × MulAut S) :=
  (MonoidHom.ofInjective diagonal_injective).symm

omit [Finite S] in
private lemma coordinates_spec (f : (diagonal (S := S)).range) : diagonal (coordinates f) = f :=
  MonoidHom.apply_ofInjective_symm diagonal_injective f

private lemma abelian_subgroup_bound [IsQuasisimple S] (hZ : center S = ⊥)
    (E : Subgroup (MulAut (S × S))) [IsMulCommutative E]
    (hr : 0 < primeRank 2 (MulAut S)) :
    primeRank 2 E ≤ 2 * primeRank 2 (MulAut S) := by
  -- The subgroup fixing both coordinate factors.
  let H := (diagonal (S := S)).range
  by_cases hE : E ≤ H
  · let f : E →* MulAut S × MulAut S := coordinates.toMonoidHom.comp (inclusion hE)
    have hf : Function.Injective f := coordinates.injective.comp (inclusion_injective hE)
    have h := primeRank_le_of_injective 2 f hf
    rw [primeRank_prod_eq_add] at h
    omega
  · obtain ⟨g, hgE, hgH⟩ := SetLike.not_le_iff_exists.mp hE
    obtain ⟨c, d, hg⟩ : ∃ c d : MulAut S, g = diagonal (c, d) * swap := by
      rcases normal_form hZ g with ⟨c, d, hg⟩ | h
      · exact (hgH ⟨(c, d), hg.symm⟩).elim
      · exact h
    let C : Subgroup E := H.comap E.subtype
    let lift : C →* H :=
      (E.subtype.comp C.subtype).codRestrict H (fun x => x.property)
    let f : C →* MulAut S := (MonoidHom.fst _ _).comp (coordinates.toMonoidHom.comp lift)
    -- In the centralizer of an interchange, one coordinate determines both.
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff f).mp
      apply bot_unique
      intro x hx
      apply mem_bot.mpr
      let ab := coordinates (lift x)
      have hxval : diagonal ab = (x.1 : MulAut (S × S)) := coordinates_spec (lift x)
      have ha : ab.1 = 1 := hx
      have hc : diagonal ab * (diagonal (c, d) * swap) =
          (diagonal (c, d) * swap) * diagonal ab := by
        rw [hxval, ← hg]
        exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm x.1 ⟨g, hgE⟩)
      have he := diagonal_eq_one_of_commute ab.1 ab.2 c d ha hc
      apply Subtype.ext
      apply Subtype.ext
      exact hxval.symm.trans he
    have hindex : C.index ≤ 2 ^ 1 := by
      apply Nat.le_of_dvd (by decide)
      apply C.index_dvd_two_iff.mpr
      refine ⟨⟨g, hgE⟩, ?_⟩
      intro x
      rcases normal_form hZ (x : MulAut (S × S)) with ⟨a, b, hx⟩ | ⟨a, b, hx⟩
      · right
        exact ⟨(a, b), hx.symm⟩
      · left
        change (x : MulAut (S × S)) = diagonal (a, b) * swap at hx
        change (x : MulAut (S × S)) * g ∈ H
        rw [hx, hg, swapped_mul_swapped]
        exact ⟨(a * d, b * c), rfl⟩
    have h1 := primeRank_le_add_of_index_le C hindex
    have h2 := primeRank_le_of_injective 2 f hf
    omega

/-- The automorphism group of a square has two-rank at most twice that of a
finite centerless quasisimple factor, provided that factor rank is positive. -/
public theorem rank_bound [IsQuasisimple S] (hZ : center S = ⊥)
    (hr : 0 < primeRank 2 (MulAut S)) :
    primeRank 2 (MulAut (S × S)) ≤ 2 * primeRank 2 (MulAut S) := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  have hb := abelian_subgroup_bound hZ E hr
  have htop : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p x.val) }
  have hc := (primeRank_le_iff_elementary_card_le E).mp hb ⊤ htop
  simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv] using hc

end Theory.GroupTheory.AutomorphismSquare
