module
public import Theory.GroupTheory.FourProductRadical
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Centralizer kernels of a cubic plane in two four-groups

A self-centralizing four-group normalizing a cubic subgroup has kernel of
order two on that subgroup. For a cubic plane in a square whose coordinate
images are cyclic, both projections have order three. Applying the kernel
calculation in both coordinates gives a centralizer of order four.

Source application: Aschbacher--Smith 10.2.5, printed p.748, through the
literal containing quotient in BinaryThreeAction/OddSmallCoreSize.
-/

public noncomputable section
open Subgroup

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A self-centralizing four-group has a kernel of order two on a normalized cubic. -/
theorem four_cubic_kernel_card (S A : Subgroup G) [IsKleinFour S]
    (hself : centralizer (S : Set G) = S)
    (hA : Nat.card A = 3) (hn : S ≤ normalizer (A : Set G)) :
    Nat.card (S ⊓ centralizer (A : Set G) : Subgroup G) = 2 := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  let f : S →* MulAut A := A.normalizerMonoidHom.comp (inclusion hn)
  have ha : Nat.card (MulAut A) = 2 := by
    rw [IsCyclic.card_mulAut,hA]
    decide
  have hd : Nat.card f.range ∣ 2 := ha ▸ f.range.card_subgroup_dvd_card
  have hr : Nat.card f.range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · have hz : f.range = ⊥ := card_eq_one.mp he
      have hcentral : S ≤ centralizer (A : Set G) := by
        intro s hs a ha'
        have hh : f ⟨s,hs⟩ = 1 := by
          have hh : f ⟨s,hs⟩ ∈ f.range := ⟨⟨s,hs⟩,rfl⟩
          rwa [hz,mem_bot] at hh
        have hh' := congrArg (fun g : MulAut A => g ⟨a,ha'⟩) hh
        have hh'' : s * a * s⁻¹ = a := congrArg Subtype.val hh'
        exact (mul_inv_eq_iff_eq_mul.mp hh'').symm
      have hAS : A ≤ S := hself ▸ le_centralizer_iff.mp hcentral
      have hdiv := card_dvd_of_le hAS
      rw [hA,IsKleinFour.card_four] at hdiv
      norm_num at hdiv
    · exact he
  have hk := f.ker.card_mul_index
  rw [index_ker,hr,IsKleinFour.card_four (G := S)] at hk
  have hmap : f.ker.map S.subtype = S ⊓ centralizer (A : Set G) := by
    ext s
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,?_⟩
      have he : f x = 1 := hx
      intro a ha'
      have hh := congrArg (fun g : MulAut A => g ⟨a,ha'⟩) he
      have hh' : (x : G) * a * (x : G)⁻¹ = a := congrArg Subtype.val hh
      exact (mul_inv_eq_iff_eq_mul.mp hh').symm
    · intro hx
      refine ⟨⟨s,hx.1⟩,?_,rfl⟩
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      change s * (a : G) * s⁻¹ = a
      rw [←hx.2 a a.property,mul_inv_cancel_right]
  rw [←hmap,card_map_of_injective S.subtype_injective]
  omega

end Theory.GroupTheory


namespace Theory.GroupTheory
variable {Q : Type*} [Group Q] [Finite Q]

/-- Both cyclic projections of an elementary cubic plane have order three. -/
theorem cubic_plane_projection_cards (P : Subgroup (Q × Q))
    [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    [IsCyclic (P.map (MonoidHom.fst Q Q))]
    [IsCyclic (P.map (MonoidHom.snd Q Q))] :
    Nat.card (P.map (MonoidHom.fst Q Q)) = 3 ∧
      Nat.card (P.map (MonoidHom.snd Q Q)) = 3 := by
  let A := P.map (MonoidHom.fst Q Q)
  let B := P.map (MonoidHom.snd Q Q)
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map _
  have ha : Nat.card A ∣ 3 := by
    rw [←IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 3 A
  have hb : Nat.card B ∣ 3 := by
    rw [←IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 3 B
  have hle : P ≤ A.prod B := fun x hx =>
    ⟨mem_map_of_mem _ hx,mem_map_of_mem _ hx⟩
  have hc := card_le_of_le hle
  rw [hP,Nat.card_congr (prodEquiv A B).toEquiv,Nat.card_prod] at hc
  rcases (Nat.dvd_prime Nat.prime_three).mp ha with ha | ha <;>
    rcases (Nat.dvd_prime Nat.prime_three).mp hb with hb | hb
  all_goals first | exact ⟨ha,hb⟩ | (rw [ha,hb] at hc; norm_num at hc)

/-- The product of the two four-groups centralizes exactly four elements of itself
against the normalized cubic plane. -/
theorem four_product_cubic_kernel_card
    (V W : Subgroup Q) [IsKleinFour V] [IsKleinFour W]
    (hv : centralizer (V : Set Q) = V) (hw : centralizer (W : Set Q) = W)
    (P : Subgroup (Q × Q)) [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    [IsCyclic (P.map (MonoidHom.fst Q Q))]
    [IsCyclic (P.map (MonoidHom.snd Q Q))]
    (hn : V.prod W ≤ normalizer (P : Set (Q × Q))) :
    Nat.card (V.prod W ⊓ centralizer (P : Set (Q × Q)) : Subgroup (Q × Q)) = 4 := by
  let A := P.map (MonoidHom.fst Q Q)
  let B := P.map (MonoidHom.snd Q Q)
  obtain ⟨ha,hb⟩ := cubic_plane_projection_cards P hP
  have hVA : V ≤ normalizer (A : Set Q) := by
    intro x hx
    exact le_normalizer_map (MonoidHom.fst Q Q)
      (mem_map_of_mem _ (hn (show (x,1) ∈ V.prod W from ⟨hx,W.one_mem⟩)))
  have hWB : W ≤ normalizer (B : Set Q) := by
    intro x hx
    exact le_normalizer_map (MonoidHom.snd Q Q)
      (mem_map_of_mem _ (hn (show (1,x) ∈ V.prod W from ⟨V.one_mem,hx⟩)))
  have he : V.prod W ⊓ centralizer (P : Set (Q × Q)) =
      (V ⊓ centralizer (A : Set Q)).prod (W ⊓ centralizer (B : Set Q)) := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨hx.1.1,?_⟩,⟨hx.1.2,?_⟩⟩
      · rintro y ⟨p,hp,rfl⟩
        exact congrArg Prod.fst (hx.2 p hp)
      · rintro y ⟨p,hp,rfl⟩
        exact congrArg Prod.snd (hx.2 p hp)
    · intro hx
      refine ⟨⟨hx.1.1,hx.2.1⟩,fun p hp => ?_⟩
      exact Prod.ext (hx.1.2 _ (mem_map_of_mem _ hp))
        (hx.2.2 _ (mem_map_of_mem _ hp))
  rw [he,Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,
    four_cubic_kernel_card V A hv ha hVA,four_cubic_kernel_card W B hw hb hWB]

end Theory.GroupTheory
