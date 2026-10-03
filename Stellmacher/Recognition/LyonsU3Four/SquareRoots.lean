module

public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Stellmacher.Recognition.LyonsU3Four.ElementOrders

/-!
# Square roots of the Sylow-center involutions

The normalizer acts transitively on the three nonidentity elements of the
center, so these elements have equally many square roots. Squaring maps the
64-element Sylow subgroup to its four-element center; the identity fiber is
the center itself. Thus each of the other three fibers has twenty elements.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
printed p. 372. These counts are the input to the exclusions of seven and nine.
-/

namespace Stellmacher.Recognition.LyonsU3Four

public theorem center_nonidentity_exists_mulAut
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {x y : S}
    (hx : x ∈ Subgroup.center S) (hy : y ∈ Subgroup.center S)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ a : MulAut S, a x = y := by
  obtain ⟨n, hn, he⟩ := centerImage_nonidentity_normalizer_conjugate S h
    (show (x : G) ∈ centerImage S from ⟨x, hx, rfl⟩)
    (show (y : G) ∈ centerImage S from ⟨y, hy, rfl⟩)
    (fun he => hx1 (Subtype.ext he)) (fun he => hy1 (Subtype.ext he))
  refine ⟨(S : Subgroup G).normalizerMonoidHom ⟨n⁻¹, Subgroup.inv_mem _ hn⟩, ?_⟩
  apply Subtype.ext
  change n⁻¹ * (x : G) * (n⁻¹)⁻¹ = (y : G)
  simpa only [inv_inv] using he

public theorem square_roots_card_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {x y : S}
    (hx : x ∈ Subgroup.center S) (hy : y ∈ Subgroup.center S)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    Nat.card {s : S // s ^ 2 = x} = Nat.card {s : S // s ^ 2 = y} := by
  obtain ⟨a, ha⟩ := center_nonidentity_exists_mulAut S h hx hy hx1 hy1
  apply Nat.card_congr (Equiv.subtypeEquiv a.toEquiv _)
  intro s
  change s ^ 2 = x ↔ (a s) ^ 2 = y
  rw [← map_pow, ← ha]
  exact a.injective.eq_iff.symm

public theorem square_one_card
    {G : Type*} [Group G] (S : Sylow 2 G) (h : SylowStructure S) :
    Nat.card {s : S // s ^ 2 = 1} = 4 := by
  have he : {s : S // s ^ 2 = 1} ≃ Subgroup.center S :=
    Equiv.subtypeEquiv (Equiv.refl S) (fun s => by
      constructor
      · exact square_one_mem_center S h
      · intro hs
        let _ := h.center_elementary
        exact elemPow_eq_one_of_isElementaryAbelian (p := 2) s hs)
  exact (Nat.card_congr he).trans h.center_card

public theorem square_roots_card
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {z : S}
    (hz : z ∈ Subgroup.center S) (hz1 : z ≠ 1) :
    Nat.card {s : S // s ^ 2 = z} = 20 := by
  classical
  let _ := Fintype.ofFinite S
  let _ := Fintype.ofFinite (Subgroup.center S)
  let q : S → Subgroup.center S := fun s => ⟨s ^ 2, square_mem_center S h s⟩
  have hf (w : Subgroup.center S) :
      Nat.card {s : S // q s = w} = Nat.card {s : S // s ^ 2 = (w : S)} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl S) _)
    intro s
    exact Subtype.ext_iff
  have hs : Nat.card S = ∑ w : Subgroup.center S,
      Nat.card {s : S // s ^ 2 = (w : S)} := by
    calc
      Nat.card S = Nat.card ((w : Subgroup.center S) × {s : S // q s = w}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv q)).symm
      _ = _ := by
        rw [Nat.card_sigma]
        exact Finset.sum_congr rfl (fun w _ => hf w)
  have he (w : Subgroup.center S) :
      Nat.card {s : S // s ^ 2 = (w : S)} =
        if w = 1 then 4 else Nat.card {s : S // s ^ 2 = z} := by
    split_ifs with hw
    · subst w
      exact square_one_card S h
    · exact square_roots_card_eq S h w.property hz
        (fun he => hw (Subtype.ext he)) hz1
  simp_rw [he] at hs
  have hc : Fintype.card (Subgroup.center S) = 4 := by
    rw [← Nat.card_eq_fintype_card, h.center_card]
  rw [h.card] at hs
  simp only [Finset.sum_ite, Finset.filter_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_singleton, nsmul_eq_mul,
    Finset.filter_ne', Finset.card_erase_of_mem, Finset.card_univ, hc] at hs
  omega

end Stellmacher.Recognition.LyonsU3Four
