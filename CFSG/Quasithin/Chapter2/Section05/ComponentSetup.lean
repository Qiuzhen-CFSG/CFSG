module

public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.CoreGeometry

/-!
# The original tuples and characteristic-two overgroups in Section 2.5

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Section 2.5, printed pp.550–551, Lemma 2.5.1.

Conjugacy inside M transports all three beta conditions. Consequently any
Sylow subgroup of H intersect M is a beta-subgroup and a Sylow subgroup of H.
If a characteristic-two overgroup of that subgroup escaped M, its Sylow order
would put it in one of the two starred Gamma families, contradicting the empty
Gamma-even-zero hypothesis. This also identifies H intersect M as the greatest
characteristic-two overgroup inside H, including its nontrivial two-core.

`SourceTuple` contains only the original tuple hypotheses. The stronger local
form of Lemma 2.5.1 needs characteristic two of M, which the chapter's genuine
QTKE and maximal-two-local hypotheses supply; it assumes no component,
classification or overgroup-placement conclusion.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05
variable {G : Type*} [Group G] [Finite G] {M H U : Subgroup G}

omit [Finite G] in
private theorem beta_map (hU : U ∈ beta M) (e : MulAut G)
    (hM : M.map e.toMonoidHom = M)
    (hQ : (twoCore M).map e.toMonoidHom = twoCore M) :
    U.map e.toMonoidHom ∈ beta M := by
  have hMi : M.map e.symm.toMonoidHom = M := by
    exact (map_symm_eq_iff_map_eq (K := M) (H := M) (e := e)).mpr hM
  refine ⟨⟨?_, hU.1.2.map e.toMonoidHom⟩, ?_, ?_, ?_⟩
  · intro hb
    apply hU.1.1
    apply bot_unique
    intro u hu
    have he : e u = 1 := by
      have hm := mem_map_of_mem e.toMonoidHom hu
      rw [hb] at hm
      exact hm
    exact e.injective (he.trans (map_one e).symm)
  · exact (map_mono hU.2.1).trans hM.le
  · intro V hVp hUV hVM y hy
    let W := V.map e.symm.toMonoidHom
    have hWp : W ∈ twoSubgroups := by
      refine ⟨?_, hVp.2.map e.symm.toMonoidHom⟩
      intro hb
      apply hVp.1
      apply bot_unique
      intro v hv
      have he : e.symm v = 1 := by
        have hm := mem_map_of_mem e.symm.toMonoidHom hv
        change e.symm v ∈ W at hm
        rw [hb] at hm
        exact hm
      exact e.symm.injective (he.trans (map_one e.symm).symm)
    have hUW : U ≤ W := by
      intro u hu
      exact ⟨e u, hUV (mem_map_of_mem e.toMonoidHom hu), e.symm_apply_apply u⟩
    have hWM : W ≤ M := (map_mono hVM).trans hMi.le
    have hyn : e.symm y ∈ normalizer (W : Set G) := by
      rw [← map_equiv_normalizer_eq V e.symm]
      exact mem_map_of_mem e.symm.toMonoidHom hy
    have hym := hU.2.2.1 W hWp hUW hWM hyn
    simpa using hM.le (mem_map_of_mem e.toMonoidHom hym)
  · intro x hx
    apply mem_map_equiv.mpr
    apply hU.2.2.2
    refine ⟨?_, ?_⟩
    · exact mem_map_equiv.mp (hQ.ge hx.1)
    · intro u hu
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using
        hx.2 (e u) (mem_map_of_mem e.toMonoidHom hu)

omit [Finite G] in
/-- Conjugation inside M preserves the original beta conditions. -/
theorem beta_conjugate (hU : U ∈ beta M) {m : G} (hm : m ∈ M) :
    U.map (MulAut.conj m).toMonoidHom ∈ beta M :=
  beta_map hU (MulAut.conj m)
    (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hm))
    (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_twoCore M hm))

/-- Every Sylow of the actual intersection lies in beta and is Sylow in H. -/
theorem intersection_sylow (hH : H ∈ gamma (Chapter1.He G) M)
    (S : Sylow 2 ↥(H ⊓ M)) :
    (S : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ∈ beta M ∧
    ∃ R : Sylow 2 H, (R : Subgroup H).map H.subtype =
      (S : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
  obtain ⟨⟨U, L⟩, hp, hLH⟩ := hH.2
  obtain ⟨R, hUR, hRb⟩ := beta_exists_sylow hp.1 (hp.2.2.2.1.trans hLH)
  obtain ⟨P, hP⟩ := sylow_image_in_inf R hRb.2.1
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥(H ⊓ M) P S
  have he : ((R : Subgroup H).map H.subtype).map
      (MulAut.conj (m : G)).toMonoidHom =
      (S : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    rw [← hP]
    have hh := congrArg (fun Q : Sylow 2 ↥(H ⊓ M) =>
      (Q : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) hm
    change ((P : Subgroup ↥(H ⊓ M)).map (MulAut.conj m).toMonoidHom).map
      (H ⊓ M).subtype = _ at hh
    rw [map_map] at hh ⊢
    change (P : Subgroup ↥(H ⊓ M)).map
      ((MulAut.conj (m : G)).toMonoidHom.comp (H ⊓ M).subtype) = _ at hh
    exact hh
  refine ⟨he ▸ beta_conjugate hRb m.property.2, ?_⟩
  apply exists_sylow_of_card ((map_subtype_le _).trans inf_le_left)
  exact (sylow_image_card (H ⊓ M) S).trans (gamma_twoPart_inf hH).symm

/-- The tuple in the opening of Section 2.5, before Sylow transport to H.
Both Sylow conditions retain their actual ambient images. -/
structure SourceTuple (M H S T : Subgroup G) (z : G) : Prop where
  gamma_zero : H ∈ gammaZero (Chapter1.He G) M
  sylow_intersection : ∃ P : Sylow 2 ↥(H ⊓ M),
    (P : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype = S
  sylow_maximal : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T
  center_le : (center T).map T.subtype ≤ S
  lt : S < T
  involution : orderOf z = 2
  mem_center : z ∈ (center T).map T.subtype

/-- Empty Gamma-even-zero excludes every characteristic-two overgroup of
an original intersection Sylow. This is the substance of 2.5.1(1). -/
theorem heOver_le_of_empty (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 ↥(H ⊓ M)) {X : Subgroup G}
    (hX : X ∈ Chapter1.HeOver G
      ((S : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype : Set G)) : X ≤ M := by
  by_contra hXM
  have hgam : H ∈ gamma (Chapter1.He G) M :=
    hH.elim (fun h => h.1.1) (fun h => h.1)
  have hSb := (intersection_sylow hgam S).1
  have hp : ((S : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype, X) ∈
      localPairs (Chapter1.He G) M := ⟨hSb, hX.1, hX.2.1, hX.2.2, hXM⟩
  have hXgam := localPair_snd_mem_gamma hp
  have hcard : Nat.card ((S : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) =
      twoPart H := (sylow_image_card _ S).trans (gamma_twoPart_inf hgam).symm
  have hle : twoPart H ≤ twoPart X := by
    rw [← hcard]
    exact beta_card_le_twoPart hSb hX.2.2
  have hXzero : X ∈ gammaZero (Chapter1.He G) M := by
    rcases hH with hs | hm
    · apply Or.inl
      apply (gammaStar_of_twoPart_le hs ?_ hle).1
      refine ⟨hXgam, (_, X), ⟨hp, le_rfl⟩, ?_⟩
      intro V hV
      rw [hcard]
      exact gammaZero_card_bound (Or.inl hs) hV
    · exact Or.inr (gammaMax_of_twoPart_le hm hXgam hle).1
  have hx : X ∈ gammaEvenZero (Chapter1.He G) M := ⟨hXzero, hX.1⟩
  rw [hempty] at hx
  exact hx

/-- The intersection retains a nontrivial two-core; this clause is needed
for membership in He(S), not just for characteristic two. -/
theorem intersection_core_ne_bot (hH : H ∈ gamma (Chapter1.He G) M) :
    twoCore (H ⊓ M) ≠ ⊥ := by
  obtain ⟨⟨U, L⟩, hp, hLH⟩ := hH.2
  obtain ⟨R, _, hRb⟩ := beta_exists_sylow hp.1 (hp.2.2.2.1.trans hLH)
  have hle : twoCore H ≤ twoCore (H ⊓ M) :=
    le_pCoreIn_inf (isPGroup_pCoreIn 2 H) (pCoreIn_le 2 H)
      ((pCoreIn_le_sylow H R).trans hRb.2.1) (le_normalizer_twoCore H)
  intro he
  exact hH.1 (bot_unique (he ▸ hle))

/-- Full 2.5.1, with the tuple's original Sylow subgroup. The greatest-member
assertion includes membership and is stronger than uniqueness of the maximal
member. Characteristic two of M follows from the chapter's QTKE hypotheses. -/
theorem lemma_2_5_1 {S T : Subgroup G} {z : G}
    (hM : M ∈ Chapter1.He G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (d : SourceTuple M H S T z) :
    (∀ X ∈ Chapter1.HeOver G (S : Set G), X ≤ M) ∧
    IsGreatest {X : Subgroup G | X ∈ Chapter1.HeOver G (S : Set G) ∧ X ≤ H}
      (H ⊓ M) ∧
    ∃ R : Sylow 2 H, (R : Subgroup H).map H.subtype = S := by
  obtain ⟨P, hP⟩ := d.sylow_intersection
  have hgam : H ∈ gamma (Chapter1.He G) M :=
    d.gamma_zero.elim (fun h => h.1.1) (fun h => h.1)
  have hs := intersection_sylow hgam P
  have hall : ∀ X ∈ Chapter1.HeOver G (S : Set G), X ≤ M := by
    intro X hX
    apply heOver_le_of_empty d.gamma_zero hempty P
    simpa only [hP] using hX
  have he : H ⊓ M ∈ Chapter1.He G := by
    obtain ⟨⟨U, L⟩, hp, hLH⟩ := hgam.2
    obtain ⟨R, hUR, _⟩ := beta_exists_sylow hp.1 (hp.2.2.2.1.trans hLH)
    exact lemma_2_3_9_4 hM d.gamma_zero ⟨hp, hLH⟩ R hUR
  refine ⟨hall, ⟨⟨⟨he, intersection_core_ne_bot hgam, ?_⟩, inf_le_left⟩,
    ?_⟩, ?_⟩
  · rw [← hP]
    exact map_subtype_le _
  · intro X hX
    exact le_inf hX.2 (hall X hX.1)
  · simpa only [hP] using hs.2

end CFSG.Quasithin.Chapter2.Section05
