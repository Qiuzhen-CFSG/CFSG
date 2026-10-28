module

public import Theory.SpecificGroups.CyclicTwoSymmetricFourSylow
public import Theory.Frattini.BinarySquares
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.SylowCentralizerNonfusion
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Stellmacher.OmegaOneCenterMap

/-!
# The central four-group and Burnside nonfusion in 15.4.13

In C₂ × D₈ the squares form a subgroup of order two, which is the Frattini
subgroup. The center is the elementary four-group. An automorphism fixes the
unique nonidentity square and can only interchange the two remaining central
involutions. Thus its square acts trivially on the center. The center action
of an ambient Sylow normalizer has two-group image, and its Sylow subgroup
already acts trivially, so the whole image is trivial. Burnside fusion now
separates all three nonidentity elements of the actual omega-center.

Only the small element calculations on the sixteen-element carrier are finite
kernel checks; no automorphism group is enumerated. The supplied Sylow group
and its embedding in G are retained throughout.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 15.4.13, printed p.1161, first two sentences of the proof.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry
abbrev Two := Multiplicative (ZMod 2)
abbrev SylowModel := Two × DihedralGroup 4
private def c : SylowModel := (Multiplicative.ofAdd 1, 1)
private def z : SylowModel := (1, .r 2)
private def r : SylowModel := (1, .r 1)

private theorem square_cases : ∀ x : SylowModel, x ^ 2 = 1 ∨ x ^ 2 = z := by decide +kernel
private theorem center_cases : ∀ x : SylowModel, x ∈ center SylowModel →
    x = 1 ∨ x = c ∨ x = z ∨ x = c * z := by decide +kernel
private theorem z_ne_one : z ≠ 1 := by decide
private theorem c_ne_one : c ≠ 1 := by decide
private theorem c_ne_z : c ≠ z := by decide
private theorem square_r : r ^ 2 = z := by decide
private theorem square_z : z ^ 2 = 1 := by decide
private theorem center_exp : ∀ x : SylowModel, x ∈ center SylowModel → x ^ 2 = 1 := by
  decide +kernel
private theorem center_card : Nat.card (center SylowModel) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem aut_z (f : MulAut SylowModel) : f z = z := by
  have hs := square_cases (f r)
  rw [← map_pow, square_r] at hs
  exact hs.resolve_left (fun h => z_ne_one (f.map_eq_one_iff.mp h))

private theorem aut_center_square (f : MulAut SylowModel) (x : SylowModel)
    (hx : x ∈ center SylowModel) : f (f x) = x := by
  have hz := aut_z f
  have hfc : f c = c ∨ f c = c * z := by
    have hc : c ∈ center SylowModel := by decide
    rcases center_cases (f c) ((centerCongr f ⟨c, hc⟩).property) with h | h | h | h
    · exact (c_ne_one (f.map_eq_one_iff.mp h)).elim
    · exact Or.inl h
    · exact (c_ne_z (f.injective (h.trans hz.symm))).elim
    · exact Or.inr h
  have hcc : f (f c) = c := by
    rcases hfc with h | h
    · rw [h, h]
    · rw [h, map_mul, h, hz]
      exact (by decide : (c * z) * z = c)
  rcases center_cases x hx with rfl | rfl | rfl | rfl
  · simp
  · exact hcc
  · rw [hz, hz]
  · rw [map_mul, map_mul, hcc, hz, hz]

private def squares : Subgroup SylowModel where
  carrier := {x | x = 1 ∨ x = z}
  one_mem' := Or.inl rfl
  mul_mem' := by
    change ∀ a b : SylowModel, (a = 1 ∨ a = z) → (b = 1 ∨ b = z) →
      a * b = 1 ∨ a * b = z
    decide +kernel
  inv_mem' := by decide +kernel
private instance : DecidablePred (· ∈ squares) := fun x =>
  inferInstanceAs (Decidable (x = 1 ∨ x = z))
private theorem frattini_model : frattini SylowModel = squares := by
  have hp : IsPGroup 2 SylowModel := IsPGroup.of_card (n := 4) (by
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, DihedralGroup.card])
  rw [hp.frattini_eq_closure_squares]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨y, rfl⟩
    exact square_cases y
  · rintro x (rfl | rfl)
    · exact one_mem _
    · exact subset_closure ⟨r, square_r⟩
private theorem frattini_card : Nat.card (frattini SylowModel) = 2 := by
  rw [frattini_model, Nat.card_eq_fintype_card]
  decide +kernel


variable {P : Type*} [Group P]

theorem center_pow_two (e : P ≃* SylowModel) (x : P) (hx : x ∈ center P) :
    x ^ 2 = 1 := by
  apply e.injective
  simpa only [map_pow, map_one] using center_exp (e x) ((centerCongr e ⟨x, hx⟩).property)

theorem center_card_four (e : P ≃* SylowModel) : Nat.card (center P) = 4 :=
  (Nat.card_congr (centerCongr e).toEquiv).trans center_card

theorem frattini_card_two (e : P ≃* SylowModel) : Nat.card (frattini P) = 2 := by
  rw [← card_map_of_injective (K := frattini P) (f := e.toMonoidHom) e.injective, frattini_map_equiv e]
  exact frattini_card

theorem center_aut_square (e : P ≃* SylowModel) (f : MulAut P)
    (x : P) (hx : x ∈ center P) : f (f x) = x := by
  have h := aut_center_square (MulAut.congr e f) (e x)
    ((centerCongr e ⟨x, hx⟩).property)
  apply e.injective
  simpa using h

variable {G : Type*} [Group G]

theorem normalizer_fixes_center [Finite G] (T : Sylow 2 G) (e : T ≃* SylowModel)
    (g : normalizer (T : Set G)) (x : T) (hx : x ∈ center T) :
    (g : G) * (x : G) * (g : G)⁻¹ = (x : G) := by
  let f : normalizer (T : Set G) →* MulAut (center T) :=
    (MulAut.characteristic (center T)).comp (T : Subgroup G).normalizerMonoidHom
  have hp : IsPGroup 2 f.range := by
    rintro ⟨a, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (f n) ^ 2 = 1
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change ((T : Subgroup G).normalizerMonoidHom n)
      (((T : Subgroup G).normalizerMonoidHom n) y.val) = y.val
    exact center_aut_square e ((T : Subgroup G).normalizerMonoidHom n) y.val y.property
  let S : Sylow 2 (normalizer (T : Set G)) := T.subtype le_normalizer
  let Q := S.mapSurjective f.rangeRestrict_surjective
  have htop : (⊤ : Subgroup f.range) ≤ Q := (hp.to_subgroup ⊤).le_sylow_of_normal Q
  obtain ⟨s, hs, he⟩ := htop (show f.rangeRestrict g ∈ (⊤ : Subgroup f.range) from mem_top _)
  have he' : f s = f g := congrArg Subtype.val he
  have hf : f g (⟨x, hx⟩ : center T) = f s (⟨x, hx⟩ : center T) := by rw [he']
  have hv := congrArg (fun y : center T => ((y : T) : G)) hf
  change (g : G) * (x : G) * (g : G)⁻¹ = (s : G) * (x : G) * (s : G)⁻¹ at hv
  rw [hv]
  have hc : (s : G) * (x : G) = (x : G) * (s : G) :=
    congrArg Subtype.val (mem_center_iff.mp hx (⟨s, hs⟩ : T))
  rw [hc, mul_inv_cancel_right]

theorem central_nonfusion [Finite G] (T : Sylow 2 G) (e : T ≃* SylowModel)
    (a b : T) (ha : a ∈ center T) (hb : b ∈ center T)
    (h : IsConj (a : G) (b : G)) : a = b := by
  have hcent (x : T) (hx : x ∈ center T) : (x : G) ∈ centralizer (T : Set G) := by
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx (⟨y, hy⟩ : T))
  apply Subtype.ext
  exact (T.eq_of_isConj_of_normalizer_le_centralizer a b (hcent a ha) (hcent b hb)
    (by
      intro g hg
      rw [mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp (normalizer_fixes_center T e ⟨g, hg⟩ a ha)))
    h).symm


private def pairEmbedding : Two × Two →* SylowModel where
  toFun x := (x.1, if x.2 = 1 then 1 else .r 2)
  map_one' := by decide
  map_mul' := by decide +kernel
private theorem pairEmbedding_injective : Function.Injective pairEmbedding := by decide +kernel
private theorem pairEmbedding_range : pairEmbedding.range = center SylowModel := by
  ext x
  change (∃ y, pairEmbedding y = x) ↔ x ∈ center SylowModel
  revert x
  decide +kernel

theorem center_equiv_four (e : P ≃* SylowModel) : Nonempty (center P ≃* Two × Two) :=
  ⟨(centerCongr e).trans ((MonoidHom.ofInjective pairEmbedding_injective).trans
    (MulEquiv.subgroupCongr pairEmbedding_range)).symm⟩

theorem omegaCenter_eq_center_image (T : Sylow 2 G) (e : T ≃* SylowModel) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) = (center T).map (T : Subgroup G).subtype := by
  ext x
  rw [Stellmacher.mem_omegaOneCenterAmbient_iff]
  constructor
  · rintro ⟨hx, _, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, congrArg Subtype.val (center_pow_two e y hy), ?_⟩
    intro q hq
    exact congrArg Subtype.val (mem_center_iff.mp hy (⟨q, hq⟩ : T))

/-- Omega-center membership is exactly centrality in the supplied Sylow group. -/
theorem mem_omegaCenter_iff (T : Sylow 2 G) (e : T ≃* SylowModel) (x : T) :
    (x : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ↔ x ∈ center T := by
  rw [omegaCenter_eq_center_image T e]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.val_injective he) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem omegaCenter_equiv_four (T : Sylow 2 G) (e : T ≃* SylowModel) :
    Nonempty (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≃* Two × Two) := by
  obtain ⟨eZ⟩ := center_equiv_four e
  exact ⟨(MulEquiv.subgroupCongr (omegaCenter_eq_center_image T e)).trans
    (((center T).equivMapOfInjective (T : Subgroup G).subtype Subtype.val_injective).symm.trans eZ)⟩

theorem exists_three_central_involutions [Finite G] (T : Sylow 2 G) (e : T ≃* SylowModel) :
    ∃ a b d : T, orderOf a = 2 ∧ orderOf b = 2 ∧ orderOf d = 2 ∧
      a ∈ center T ∧ b ∈ center T ∧ d ∈ center T ∧
      (∀ x : T, x ∈ center T ↔ x = 1 ∨ x = a ∨ x = b ∨ x = d) ∧
      ¬ IsConj (a : G) (b : G) ∧ ¬ IsConj (a : G) (d : G) ∧
      ¬ IsConj (b : G) (d : G) := by
  have ho (x : SylowModel) (h2 : x ^ 2 = 1) (hn : x ≠ 1) : orderOf (e.symm x) = 2 := by
    rw [e.symm.orderOf_eq]
    exact orderOf_eq_prime h2 hn
  have hc (x : SylowModel) (hx : x ∈ center SylowModel) : e.symm x ∈ center T :=
    (centerCongr e.symm ⟨x, hx⟩).property
  have hca := hc c (by decide)
  have hcb := hc z (by decide)
  have hcd := hc (c * z) (by decide)
  refine ⟨e.symm c, e.symm z, e.symm (c * z), ho c (by decide) c_ne_one,
    ho z square_z z_ne_one, ho (c * z) (by decide) (by decide), hca, hcb, hcd, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      rcases center_cases (e x) ((centerCongr e ⟨x, hx⟩).property) with h | h | h | h
      · exact Or.inl (e.map_eq_one_iff.mp h)
      · exact Or.inr (Or.inl ((e.eq_symm_apply).mpr h))
      · exact Or.inr (Or.inr (Or.inl ((e.eq_symm_apply).mpr h)))
      · exact Or.inr (Or.inr (Or.inr ((e.eq_symm_apply).mpr h)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_mem _
      · exact hca
      · exact hcb
      · exact hcd
  · intro h
    exact c_ne_z (e.symm.injective (central_nonfusion T e _ _ hca hcb h))
  · intro h
    exact (by decide : c ≠ c * z) (e.symm.injective (central_nonfusion T e _ _ hca hcd h))
  · intro h
    exact (by decide : z ≠ c * z) (e.symm.injective (central_nonfusion T e _ _ hcb hcd h))

end CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry
