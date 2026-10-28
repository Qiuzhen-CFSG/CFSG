module
public import Theory.SpecificGroups.PSL2.SylowIntersections
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Theory.GroupAction.PrimeDegreeCoprimeIndex

/-!
# Cubic elements in nontransitive field-four root subgroups

Suppose a finite group acts transitively on five points, with a surjection
to SL₂(4) whose kernel fixes every point. A nontransitive subgroup meeting
two distinct root groups nontrivially contains an element of order three.

Adjoining the quotient kernel preserves nontransitivity. The prime-degree
index argument then makes the quotient image have order dividing twelve.
Distinct binary roots have trivial intersection, so their two nontrivial
intersections cannot lie in a two-group. Three therefore divides the image
order, and Cauchy's theorem produces a cubic in the original subgroup.
No faithfulness of the original action or splitting of its kernel is assumed.

Source: the subgroup step in DGS, Groups and Graphs (1985), (10.8), p.161.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem roots_not_pgroup (R T : Sylow 2 SL(2,F)) (hne : R≠T)
    (A B N : Subgroup SL(2,F)) (hAR : A≤R) (hBT : B≤T)
    (hAN : A≤N) (hBN : B≤N) (hA : A≠⊥) (hB : B≠⊥) : ¬IsPGroup 2 N := by
  intro hp
  obtain ⟨U,hU⟩ := hp.exists_le_sylow
  have eq_of (V : Sylow 2 SL(2,F)) (D : Subgroup SL(2,F))
      (hDV : D≤V) (hDN : D≤N) (hD : D≠⊥) : V=U := by
    let e := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    let V' := V.mapSurjective (f:=e.toMonoidHom) e.surjective
    let U' := U.mapSurjective (f:=e.toMonoidHom) e.surjective
    have hh : V'=U' := Theory.PSL2.sylow_eq_of_inf_ne_bot V' U' (by
      change (V:Subgroup SL(2,F)).map e.toMonoidHom⊓
        (U:Subgroup SL(2,F)).map e.toMonoidHom≠⊥
      rw [←map_inf (V:Subgroup SL(2,F)) (U:Subgroup SL(2,F)) e.toMonoidHom e.injective]
      intro hz
      have hz' := (map_eq_bot_iff_of_injective _ e.injective).mp hz
      exact hD (le_bot_iff.mp (hz' ▸ le_inf hDV (hDN.trans hU))))
    apply Sylow.ext
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    exact congrArg Sylow.toSubgroup hh
  exact hne ((eq_of R A hAR hAN hA).trans (eq_of T B hBT hBN hB).symm)

/-- A nontransitive subgroup of a degree-five action with a field-four
rank-one quotient, meeting distinct roots nontrivially, contains a cubic. -/
theorem exists_cubic_of_nontransitive_roots
    {M X : Type*} [Group M] [Finite M] [MulAction M X] [Finite X]
    [MulAction.IsPretransitive M X]
    (hF : Nat.card F=4) (hX : Nat.card X=5)
    (q : M →* SL(2,F)) (hq : Function.Surjective q)
    (hk : ∀ k∈q.ker, ∀ x : X, k • x=x)
    (C : Subgroup M) (hnt : ¬MulAction.IsPretransitive C X)
    (R T : Sylow 2 SL(2,F)) (hne : R≠T)
    (A B : Subgroup SL(2,F)) (hAR : A≤R) (hBT : B≤T)
    (hAC : A≤C.map q) (hBC : B≤C.map q) (hA : A≠⊥) (hB : B≠⊥) :
    ∃ d∈C, orderOf d=3 := by
  let N := C.map q
  have hn : ¬IsPGroup 2 N := roots_not_pgroup R T hne A B N hAR hBT hAC hBC hA hB
  have hnt' : ¬MulAction.IsPretransitive (↥(C⊔q.ker)) X := by
    intro ht
    let := ht
    apply hnt
    constructor
    intro x y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (↥(C⊔q.ker)) x y
    have hprod : (g:M)∈(C:Set M)*(q.ker:Set M) := by
      rw [←coe_mul_of_left_le_normalizer_right C q.ker (by rw [normalizer_eq_top]; exact le_top)]
      exact g.property
    obtain ⟨c,hc,k,hk',he⟩ := hprod
    refine ⟨⟨c,hc⟩,?_⟩
    change (g:M) • x=y at hg
    rw [←he,mul_smul,hk k hk' x] at hg
    exact hg
  have hfive : 5∣N.index := by
    have hi : N.index=(C⊔q.ker).index := by
      rw [show N=C.map q from rfl,index_map,q.range_eq_top_of_surjective hq,index_top,mul_one]
    rw [hi]
    by_contra hh
    exact hnt' (MulAction.isPretransitive_of_prime_card_of_coprime_index
      (by decide) hX _ ((Nat.prime_five.coprime_iff_not_dvd).mpr hh))
  have hcard : Nat.card SL(2,F)=60 := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
    decide
  have hN : Nat.card N∣12 := by
    obtain ⟨i,hi⟩ := hfive
    have hh := N.index_mul_card
    rw [hcard,hi] at hh
    refine ⟨i,?_⟩
    nlinarith
  have hthree : 3∣Nat.card N := by
    by_contra hh
    apply hn
    apply IsPGroup.of_card_dvd_pow (n:=2)
    exact (Nat.coprime_comm.mpr (Nat.prime_three.coprime_iff_not_dvd.mpr hh)).dvd_of_dvd_mul_left hN
  have hdiv : Nat.card N∣Nat.card C := by
    let f : C →* SL(2,F) := q.comp C.subtype
    have hr : f.range=N := by simp only [f,MonoidHom.range_comp,range_subtype]; rfl
    rw [←hr,←index_ker]
    exact f.ker.index_dvd_card
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨d,hd⟩ := exists_prime_orderOf_dvd_card' (G:=C) 3 (hthree.trans hdiv)
  exact ⟨d,d.property,(orderOf_injective C.subtype C.subtype_injective d).trans hd⟩
end Matrix.SpecialLinearGroup
