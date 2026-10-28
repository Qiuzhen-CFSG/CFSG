module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.ResidualProduct.Generation
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
public import Theory.GroupTheory.PCoreImage

/-!
# The residual product at the end of 15.3.40

Let `A = O²(Y₊ ∩ L)` be the component actor after orienting the definite
planes `U = V₁`, `W = V₂`. Given the actual equivalence `A ≃* A₄`, the
order-four plane exhausts `A ∩ O₂(YT)`. Thus the action on the two-core has
only this noncentral support. The three-subgroups argument in `CoreAction`
proves that `A` commutes with its actual conjugate by the plane-interchanger.
This unpacks the source's single noncentral two-chief-factor argument without
assuming normality of `A` in `Y`.

The independent plane images generate the order-nine action quotient. Its
kernel modulo `O₂(Y)` is trivial in the elementary-nine alternative of
15.3.7, and the center, hence Frattini subgroup, in the extraspecial alternative.
Frattini non-generation and two-perfectness therefore give `Y = A Aᵗ`.
Multiplication constructs the A₄-square equivalence. Its order excludes the
extraspecial order-27 quotient. Finally, `|Y₊/O₂(Y₊)| = 9` rules out case (2)
of 15.3.10, since its actor centralizes the first plane, and gives `Y = Y₊`.

These are conditional local results. The map `f` is anchored by its exact
joint-plane centralizer kernel, so an unrelated abstract group of order nine
cannot serve as the action quotient. `QuotientAlternatives` retains the
actual two-core quotient and the image of this same kernel. The full earlier
source statements, the rank-one model equivalence, and the contradiction
with 15.3.9 belong to the source-theorem assembly owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.7,
15.3.10--12 (printed pp.1122--1125), 15.3.36--37 (p.1135), and the last
paragraph of 15.3.40 (p.1138).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.ResidualProduct
variable {G D : Type*} [Group G] [Group D]

private theorem map_centralizes {A B : Subgroup G} (f : G →* D)
    (h : A ≤ centralizer (B : Set G)) :
    A.map f ≤ centralizer (B.map f : Set D) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [← map_commutator, commutator_eq_bot_iff_le_centralizer.mpr h, Subgroup.map_bot]

private theorem alternating_four_card {A : Subgroup G} (e : A ≃* alternatingGroup (Fin 4)) :
    Nat.card A = 12 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

private theorem alternating_four_center {A : Subgroup G} (e : A ≃* alternatingGroup (Fin 4)) :
    center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  apply e.injective
  have hh : e a ∈ center (alternatingGroup (Fin 4)) := by
    rw [mem_center_iff]
    intro b
    obtain ⟨c, rfl⟩ := e.surjective b
    simpa only [map_mul] using congrArg e (mem_center_iff.mp ha c)
  rw [alternatingGroup.center_eq_bot (by simp)] at hh
  simpa using hh

/-- Exact quotient clauses of 15.3.7 used in the residual-product argument. -/
@[expose] def QuotientAlternatives (Y : Subgroup G) {D : Type*} [Group D] (f : Y →* D) : Prop :=
  (IsElementaryAbelian 3 (Y ⧸ pCore 2 Y) ∧ Nat.card (Y ⧸ pCore 2 Y) = 9 ∧
    f.ker.map (QuotientGroup.mk' (pCore 2 Y)) = ⊥) ∨
  (IsExtraspecial 3 (Y ⧸ pCore 2 Y) ∧ Nat.card (Y ⧸ pCore 2 Y) = 27 ∧
    f.ker.map (QuotientGroup.mk' (pCore 2 Y)) = center (Y ⧸ pCore 2 Y))

private theorem kernel_le_frattini [Finite G] {Y : Subgroup G} (f : Y →* D)
    (h : QuotientAlternatives Y f) :
    f.ker.map (QuotientGroup.mk' (pCore 2 Y)) ≤ frattini (Y ⧸ pCore 2 Y) := by
  rcases h with ⟨_, _, hk⟩ | ⟨he, _, hk⟩
  · rw [hk]; exact bot_le
  · let := he
    rw [hk, IsExtraspecial.frattini_eq_center_three]

private theorem image_top_of_nine_dvd [Finite G] [Finite D]
    (f : G →* D) (H : Subgroup G) (hker : IsPGroup 2 f.ker)
    (hH : 9 ∣ Nat.card H) (hD : Nat.card D = 9) : H.map f = ⊤ := by
  let g := f.comp H.subtype
  have hg : IsPGroup 2 g.ker := hker.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hg
  have hcard : Nat.card H = 2 ^ n * Nat.card g.range := by
    rw [← g.ker.card_mul_index, index_ker, hn]
  rw [hcard] at hH
  have hcop : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
  have hd : 9 ∣ Nat.card g.range := hcop.dvd_mul_left.mp hH
  have hr : g.range = H.map f := by simp [g, MonoidHom.range_comp]
  rw [hr] at hd
  exact eq_of_le_of_card_ge le_top (by
    simpa [hD] using Nat.le_of_dvd (Nat.card_pos (α := H.map f)) hd)

/-- The final residual-product step of 15.3.40, conditional on its earlier
local inputs and the actual oriented component model.

* `f`, `hk`, `hD`, and `hquot` are the joint-plane action and quotient clauses
  of 15.3.7; in particular the kernel is the actual `C_Y(U ⊔ W)`.
* `hcase` is Hypothesis 15.3.10 and `hplus9` is the quotient clause of
  15.3.37(2), retained before any identification of `Y` with `Y₊`.
* `hY`, `hT` come from the residual construction and its T-invariance.
  The core/plane bounds come from `O₂(YT) = C_T(V)`, with self-centralization
  inherited from characteristic two in `M`.
* `hSA`, `hAU`, `hAW` are the oriented actor geometry in the first two
  paragraphs of 15.3.40. The actor is literally `componentFactor Yplus L`;
  in case (2) it is not identified with the full plane-centralizer residual.
* `t` is the given element of `T − S`, with its actual plane interchanges.

Generation, disjointness, commutation, exclusion of order 27, and `Y = Y₊`
are all conclusions. No assertion of the numbered containment theorem is made. -/
theorem alternating_square_of_local_geometry [Finite G] [Finite D]
    {M Y Yplus L S T U W : Subgroup G}
    (f : Y →* D) (hD : Nat.card D = 9)
    (hk : f.ker = (centralizer (U ⊔ W : Subgroup G)).subgroupOf Y)
    (hquot : QuotientAlternatives Y f)
    (hcase : Hypothesis15310 M Y S U Yplus)
    (hplus9 : Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (hY : IsPPerfect 2 Y) (hplusY : Yplus ≤ Y)
    (hT : T ≤ normalizer (Y : Set G))
    (hRS : (Y ⊔ T).pCoreIn 2 ≤ S)
    (hself : Y ⊓ centralizer ((Y ⊔ T).pCoreIn 2 : Set G) ≤ (Y ⊔ T).pCoreIn 2)
    (hUR : U ≤ (Y ⊔ T).pCoreIn 2) (hWR : W ≤ (Y ⊔ T).pCoreIn 2)
    (hU : Nat.card U = 4) (hW : Nat.card W = 4) (hdUW : Disjoint U W)
    (hSA : S ≤ normalizer (componentFactor Yplus L : Set G))
    (hAU : componentFactor Yplus L ≤ centralizer (U : Set G))
    (hAW : ⁅W, componentFactor Yplus L⁆ = W)
    (eA : componentFactor Yplus L ≃* alternatingGroup (Fin 4))
    (t : G) (ht : t ∈ T ∧ t ∉ S)
    (hswapU : U.map (MulAut.conj t).toMonoidHom = W)
    (hswapW : W.map (MulAut.conj t).toMonoidHom = U) :
    Nat.card (Y ⧸ pCore 2 Y) = 9 ∧ IsElementaryAbelian 3 (Y ⧸ pCore 2 Y) ∧
    Y = Yplus ∧
    Y = componentFactor Yplus L ⊔ (componentFactor Yplus L).map (MulAut.conj t).toMonoidHom ∧
    Disjoint (componentFactor Yplus L) ((componentFactor Yplus L).map (MulAut.conj t).toMonoidHom) ∧
    componentFactor Yplus L ≤ centralizer ((componentFactor Yplus L).map (MulAut.conj t).toMonoidHom : Set G) ∧
    Nonempty (Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  let A := componentFactor Yplus L
  let B := A.map (MulAut.conj t).toMonoidHom
  let Q := (Y ⊔ T).pCoreIn 2
  let e := (MulAut.conj t).toMonoidHom
  have hAY : A ≤ Y := ((map_subtype_le _).trans inf_le_left).trans hplusY
  have hKY : Y ⊔ T ≤ normalizer (Y : Set G) := sup_le Y.le_normalizer hT
  have hKQ : Y ⊔ T ≤ normalizer (Q : Set G) :=
    (Y ⊔ T).le_normalizer.trans (normalizer_le_normalizer_characteristic_image
      (Y ⊔ T) (pCore 2 (Y ⊔ T : Subgroup G)))
  have hYQ : Y ≤ normalizer (Q : Set G) := le_sup_left.trans hKQ
  have hQt : Q.map e = Q := mem_normalizer_iff_map_conj_eq.mp (hKQ (mem_sup_right ht.1))
  have hYt : Y.map e = Y := mem_normalizer_iff_map_conj_eq.mp (hT ht.1)
  have hBY : B ≤ Y := by
    rw [← hYt]
    exact map_mono hAY
  have hQA : Q ≤ normalizer (A : Set G) := hRS.trans hSA
  have hAQ : A ≤ normalizer (Q : Set G) := hAY.trans hYQ
  have hQB : Q ≤ normalizer (B : Set G) := by
    rw [← hQt]
    exact (map_mono hQA).trans (le_normalizer_map e)
  have hBQ : B ≤ normalizer (Q : Set G) := hBY.trans hYQ
  have hWA : W ≤ A := by
    rw [← hAW]
    exact le_normalizer_iff_commutator_le_right.mp (hWR.trans hQA)
  have hUB : U ≤ B := by
    rw [← hswapW]
    exact map_mono hWA
  have hBW : B ≤ centralizer (W : Set G) := by
    rw [← hswapU]
    exact map_centralizes e hAU
  have hBU : ⁅U, B⁆ = U := by
    rw [← hswapW]
    exact (map_commutator W A e).symm.trans (congrArg (Subgroup.map e) hAW)
  have hA : IsPPerfect 2 A := componentFactor_isPPerfect Yplus L
  have hB : IsPPerfect 2 B := hA.of_surjective
    (e.subgroupMap A) (e.subgroupMap_surjective A)
  have hQ : IsPGroup 2 Q := isPGroup_pCoreIn 2 (Y ⊔ T)
  have hcA : Nat.card A = 12 := alternating_four_card eA
  have hcB : Nat.card B = 12 := (card_map_of_injective (MulAut.conj t).injective).trans hcA
  have hQAeq : Q ⊓ A = W := inf_eq_plane hQ hcA hW hWR hWA
  have hQBeq : Q ⊓ B = U := inf_eq_plane hQ hcB hU hUR hUB
  have hc : A ≤ centralizer (B : Set G) := actors_commute hAY hBY hself hQ hA hB
    hQA hQB hAQ hBQ hQAeq hQBeq hAU hBW hdUW
  have hd : Disjoint A B := actors_disjoint hc (alternating_four_center eA)
  have hUne : U ≠ ⊥ := by intro he; simp [he] at hU
  have hWne : W ≠ ⊥ := by intro he; simp [he] at hW
  have himage := action_image_generated f hk hAY hBY hAU hBW hc hcA hcB hD hAW hBU hUne hWne
  have hsupp := supplement_core_of_action_image f himage (kernel_le_frattini f hquot)
  have hsupp' : (A ⊔ B) ⊔ Y.pCoreIn 2 = Y := by
    have hh := congrArg (Subgroup.map Y.subtype) hsupp
    simpa only [pCoreIn, Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hAY hBY),
      ← MonoidHom.range_eq_map, range_subtype] using hh
  have hcoreQ : Y.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left hKY
  have hgen : Y = A ⊔ B := residual_generated hY hA hB hQ hAY hBY hQA hQB (by
    rw [← hsupp']
    exact sup_le_sup_left hcoreQ _)
  obtain ⟨esquare⟩ := alternating_square_of_conjugate_factors Y A t hgen hd hc eA
  have hcardY : Nat.card Y = 144 := by
    rw [Nat.card_congr esquare.toEquiv, Nat.card_prod, nat_card_alternatingGroup]
    norm_num
  have hnot27 : Nat.card (Y ⧸ pCore 2 Y) ≠ 27 := by
    intro h27
    have hdiv := (pCore 2 Y).index_dvd_card
    rw [index_eq_card, h27, hcardY] at hdiv
    norm_num at hdiv
  have hordinary : IsElementaryAbelian 3 (Y ⧸ pCore 2 Y) ∧
      Nat.card (Y ⧸ pCore 2 Y) = 9 ∧
      f.ker.map (QuotientGroup.mk' (pCore 2 Y)) = ⊥ := by
    rcases hquot with h | h
    · exact h
    · exact (hnot27 h.2.1).elim
  have hkerTwo : IsPGroup 2 f.ker := by
    have hle := (map_eq_bot_iff f.ker).mp hordinary.2.2
    rw [QuotientGroup.ker_mk'] at hle
    exact pCore_isPGroup.to_le hle
  have hplusDiv : 9 ∣ Nat.card (Yplus.subgroupOf Y) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hplusY).toEquiv]
    have hh := (pCore 2 Yplus).index_dvd_card
    rwa [index_eq_card, hplus9] at hh
  have hplusImage : (Yplus.subgroupOf Y).map f = ⊤ :=
    image_top_of_nine_dvd f (Yplus.subgroupOf Y) hkerTwo hplusDiv hD
  have hYYplus : Y = Yplus := by
    rcases hcase with he | ⟨_, he⟩
    · exact he.symm
    · have hplusU : Yplus ≤ centralizer (U : Set G) := by
        rw [he]
        exact (map_subtype_le _).trans inf_le_right
      have hid := opposite_images_disjoint f hk hplusU hBW
      rw [hplusImage] at hid
      have hBbot : (B.subgroupOf Y).map f = ⊥ := top_disjoint.mp hid
      have hk' : f.ker = (centralizer (W ⊔ U : Subgroup G)).subgroupOf Y := by
        simpa only [sup_comm] using hk
      exact (plane_image_ne_bot f hk' hBY hUne hBU hBbot).elim
  exact ⟨hordinary.2.1, hordinary.1, hYYplus, hgen, hd, hc, ⟨esquare⟩⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.ResidualProduct
