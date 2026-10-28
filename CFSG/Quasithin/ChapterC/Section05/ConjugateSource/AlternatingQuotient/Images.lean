module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Basic

/-!
# Images of the original block subgroups

A kernel contained in D is disjoint from the original module and its
noncommuting conjugate. Their actual images therefore retain the marked
module coordinates. The elementary image cores span the whole target,
so their common D-image is central.

Source: Aschbacher–Smith C.5.6(5), printed pp.157–158.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
open RankOne
variable {G : Type*} [Group G] {R K : Subgroup G} {T : Type*} [Group T]

theorem image_centralizes (f : S R →* T) (A B : Subgroup G)
    (hc : A ≤ centralizer (B : Set G)) :
    baumannImage R f A ≤ centralizer (baumannImage R f B : Set T) := by
  rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
  exact (map_mul f t s).symm.trans
    ((congrArg f (Subtype.ext (hc hs t ht))).trans (map_mul f s t))

theorem image_sup (f : S R →* T) (A B : Subgroup G) (hA : A ≤ S R) (hB : B ≤ S R) :
    baumannImage R f (A ⊔ B) = baumannImage R f A ⊔ baumannImage R f B := by
  rw [baumannImage, subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

theorem image_top (f : S R →* T) (hf : Function.Surjective f) :
    baumannImage R f (S R) = ⊤ := by
  rw [baumannImage, subgroupOf_self, map_top_of_surjective f hf]

theorem image_range (f : S R →* T) (B : Subgroup G) (hB : B ≤ S R) :
    (f.comp (inclusion hB)).range = baumannImage R f B := by
  ext t
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨inclusion hB b, b.property, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

theorem image_injective (f : S R →* T) (hk : f.ker ≤ (D R K).subgroupOf (S R))
    (B : Subgroup G) (hB : B ≤ S R) (hd : Disjoint B (D R K)) :
    Function.Injective (f.comp (inclusion hB)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro b hb
  have hbD : (b : G) ∈ D R K := hk hb
  exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨b.property, hbD⟩))

/-- The actual image of a subgroup disjoint from D is isomorphic to that
original subgroup, through the given quotient map. -/
noncomputable def imageEquiv (f : S R →* T) (hk : f.ker ≤ (D R K).subgroupOf (S R))
    (B : Subgroup G) (hB : B ≤ S R) (hd : Disjoint B (D R K)) : B ≃* baumannImage R f B :=
  (MulEquiv.ofBijective (f.comp (inclusion hB)).rangeRestrict
    ⟨fun _ _ hab => image_injective f hk B hB hd (congrArg Subtype.val hab),
      (f.comp (inclusion hB)).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (image_range f B hB))

theorem imageEquiv_apply (f : S R →* T) (hk : f.ker ≤ (D R K).subgroupOf (S R))
    (B : Subgroup G) (hB : B ≤ S R) (hd : Disjoint B (D R K)) (b : B) :
    (imageEquiv f hk B hB hd b : T) = f (inclusion hB b) := rfl

private theorem intersection_centralizes_top (A B : Subgroup T)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] (hspan : A ⊔ B = ⊤) :
    A ⊓ B ≤ center T := by
  intro z hz
  apply mem_center_iff.mpr
  intro t
  have hc : z ∈ centralizer ((A ⊔ B : Subgroup T) : Set T) := by
    rw [show ((A ⊔ B : Subgroup T) : Set T) = (closure ((A : Set T) ∪ B) : Set T) by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq], centralizer_closure]
    intro a ha
    rcases ha with ha | ha
    · exact mem_centralizer_iff.mp (le_centralizer A hz.1) a ha
    · exact mem_centralizer_iff.mp (le_centralizer B hz.2) a ha
  rw [hspan] at hc
  exact hc t (mem_top _)

variable [Finite G] {L : Subgroup G}

theorem opposite_elementary (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hPhi : (Phi R K).subgroupOf (S R) ≤ f.ker) :
    IsElementaryAbelian 2 (baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom)) := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hV : V ≤ S R := (map_mono h.module_le).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx)))
  let : IsElementaryAbelian 2 (U K) := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (baumannImage R f V) := by
    let : IsElementaryAbelian 2 (V.subgroupOf (S R)) := IsElementaryAbelian.subgroupOf hV
    exact IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 (baumannImage R f (Q R K)) := h.quotient_core_elementary f hPhi
  have hDQ : baumannImage R f (D R K) ≤ baumannImage R f (Q R K) :=
    map_mono (subgroupOf_mono _ (show D R K ≤ Q R K from le_sup_right.trans_eq h.product.symm))
  let : IsElementaryAbelian 2 (baumannImage R f (D R K)) := IsElementaryAbelian.of_le hDQ
  rw [← h.opposite_eq_conjugate x hx hnc, image_sup f _ _ hV inf_le_left]
  exact IsElementaryAbelian.sup_of_le_centralizer
    (image_centralizes f _ _ (h.centralizer_centralizes_conjugate x hx hnc))

theorem image_core_span (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hf : Function.Surjective f) :
    baumannImage R f (Q R K) ⊔
      baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom) = ⊤ := by
  rw [← image_sup f _ _ (h.core.le.trans inf_le_left) ((h.conjugate_core x hx).le.trans inf_le_left),
    ← h.core_conjugate_span x hx hnc, image_top f hf]

theorem image_centralizer_central (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hPhi : (Phi R K).subgroupOf (S R) ≤ f.ker) :
    baumannImage R f (D R K) ≤ center T := by
  let := h.quotient_core_elementary f hPhi
  let := opposite_elementary h x hx hnc f hPhi
  apply (le_inf ?_ ?_).trans (intersection_centralizes_top _ _ (image_core_span h x hx hnc f hf))
  · exact map_mono (subgroupOf_mono _ (show D R K ≤ Q R K from le_sup_right.trans_eq h.product.symm))
  · exact map_mono (subgroupOf_mono _ ((h.opposite_eq_conjugate x hx hnc).symm ▸ le_sup_right))

/-- Both cores have equal image order for every common kernel contained in D;
no invariance of this kernel under x is required. -/
theorem image_core_card (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    Nat.card (baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom)) =
      Nat.card (baumannImage R f (Q R K)) := by
  let A := (Q R K).subgroupOf (S R)
  let B := ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom).subgroupOf (S R)
  have hkA : f.ker ≤ A := hk.trans (subgroupOf_mono _ (show D R K ≤ Q R K from le_sup_right.trans_eq h.product.symm))
  have hkB : f.ker ≤ B := hk.trans
    (subgroupOf_mono _ ((h.opposite_eq_conjugate x hx hnc).symm ▸ le_sup_right))
  have hc : Nat.card A = Nat.card B := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (h.core.le.trans inf_le_left)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe ((h.conjugate_core x hx).le.trans inf_le_left)).toEquiv,
      card_map_of_injective (MulAut.conj x⁻¹).injective]
  have hA := relIndex_mul_relIndex ⊥ f.ker A bot_le hkA
  have hB := relIndex_mul_relIndex ⊥ f.ker B bot_le hkB
  rw [relIndex_bot_left, relIndex_bot_left] at hA hB
  have he : f.ker.relIndex B = f.ker.relIndex A := by
    have hp : 0 < Nat.card f.ker := Nat.card_pos
    nlinarith
  simpa only [baumannImage, ← relIndex_ker] using he
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
end
