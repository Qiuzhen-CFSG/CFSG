module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.Nine
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.LocalNormalizerUniqueness
import Mathlib.Tactic

/-!
# Sylow geometry of inner four-group normalizers over the field of nine

For every prescribed Sylow two-subgroup T of PΓL₂(F), and every inner
four-group B contained in T, the full normalizer N of B meets T in order
sixteen and generates PΓL₂(F) together with T. No field-involution
identification of N is assumed, and both inner four-group classes remain.

The inner intersection of T is dihedral of order eight. Its two four-groups
are permuted by T. The order-sixteen linear intersection cannot normalize B:
the full linear normalizer has order twenty-four. Thus the stabilizer of B
has index two in T, whose order is thirty-two.

For generation, the inner intersection of J = T ⊔ N contains the inner S₄
normalizer of B. The proper Sylow-overgroup classification in PSL₂(9)
therefore leaves only S₄. In that case B is its characteristic two-core,
so J normalizes B, contradicting the preceding nonnormalization by T.
Consequently J contains the whole inner group; its index then divides both
four and the odd Sylow index forty-five, and J is the full semilinear group.

Source: Aschbacher–Smith, E.1.2 and E.1.14(6), printed pp.209–210 and 214,
citing Aschbacher (1982), Lemma 4.10. The PSL₂(9) model and proper-overgroup
results are the checked inputs of `LinearWitnesses.InnerPlacement.Nine`.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry.SylowNormalizers
open PrimeGeometry.Inner.SymmetricNormalizers

private theorem index_two_of_two_fours {G : Type*} [Group G]
    (T D B : Subgroup G) (eD : D ≃* DihedralGroup 4)
    (hTD : T ≤ normalizer (D : Set G)) (hBD : B ≤ D) (hB : IsKleinFour B)
    (hnot : ¬ T ≤ normalizer (B : Set G)) :
    (normalizer (B : Set G)).relIndex T = 2 := by
  classical
  obtain ⟨U, V, _, _, _, _, hUV, hcases⟩ := dihedral_four_four_groups D eD
  obtain ⟨t, htT, htN⟩ := SetLike.not_le_iff_exists.mp hnot
  let C := B.map (MulAut.conj t).toMonoidHom
  have hc (g : G) (hg : g ∈ T) :
      B.map (MulAut.conj g).toMonoidHom = U ∨
      B.map (MulAut.conj g).toMonoidHom = V := by
    apply hcases
    · exact (map_mono hBD).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hTD hg))
    · exact isKleinFour_map_of_injective B hB _ (MulAut.conj g).injective
  have hBC : B ≠ C := fun he => htN (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hpair (g : G) (hg : g ∈ T) :
      B.map (MulAut.conj g).toMonoidHom = B ∨
      B.map (MulAut.conj g).toMonoidHom = C := by
    have hBcases := hcases B hBD hB
    have hCcases := hc t htT
    have hGcases := hc g hg
    change C = U ∨ C = V at hCcases
    rcases hBcases with hBU | hBV <;> rcases hCcases with hCU | hCV
    · exact (hBC (hBU.trans hCU.symm)).elim
    · simpa only [hBU, hCV] using hGcases
    · exact hGcases.elim (fun h => Or.inr (h.trans hCU.symm))
        (fun h => Or.inl (h.trans hBV.symm))
    · exact (hBC (hBV.trans hCV.symm)).elim
  apply relIndex_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨t⁻¹, T.inv_mem htT, fun h => htN (by simpa using (normalizer (B : Set G)).inv_mem h), ?_⟩
  intro g hg
  rcases hpair g hg with hfix | hmove
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hfix)
  · left
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hcomp : (MulAut.conj (t⁻¹ * g)).toMonoidHom =
        (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      change (t⁻¹ * g) * x * (t⁻¹ * g)⁻¹ = t⁻¹ * (g * x * g⁻¹) * (t⁻¹)⁻¹
      group
    change B.map (MulAut.conj (t⁻¹ * g)).toMonoidHom = B
    rw [hcomp, ← map_map, hmove]
    change (B.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom = B
    rw [map_map]
    have he : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
      ext x
      change t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x
      group
    rw [he, map_id]

variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]
local instance : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

omit [Field F] [Finite F] [Finite (PGammaL2 F)] in
private theorem odd_nine (hF : Nat.card F = 9) : IsOddPrimePower (Nat.card F) :=
  ⟨3, 2, Nat.prime_three, by decide, by decide, by simpa using hF⟩

omit [Finite (PGammaL2 F)] in
private theorem full_card (hF : Nat.card F = 9) : Nat.card (PGammaL2 F) = 1440 := by
  rw [SemidirectProduct.card, pgl2_card_formula,
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_three (show Nat.card F = 3 ^ 2 by simpa using hF), hF]
  norm_num

private theorem full_sylow_card (hF : Nat.card F = 9) (T : Sylow 2 (PGammaL2 F)) :
    Nat.card T = 32 := by
  rw [T.card_eq_multiplicity, full_card hF]
  decide +kernel

private theorem inner_sylow_card (hF : Nat.card F = 9) (S : Sylow 2 (pGammaL2PSLRange F)) :
    Nat.card S = 8 := by
  rw [S.card_eq_multiplicity,
    ← Nat.card_congr (pGammaL2PSLRangeEquiv F).toEquiv,
    Atlas.Comparisons.Exceptional.psl2Card9_card hF]
  decide +kernel

omit [Finite (PGammaL2 F)] in
private theorem inner_normalizer_equiv (hF : Nat.card F = 9)
    (B : Subgroup (pGammaL2PSLRange F)) (hB : IsKleinFour B) :
    Nonempty (normalizer (B : Set (pGammaL2PSLRange F)) ≃* Equiv.Perm (Fin 4)) := by
  let e := (pGammaL2PSLRangeEquiv F).symm
  obtain ⟨eN⟩ := LinearWitnesses.InnerPlacement.Nine.normalizer_equiv hF
    (B.map e.toMonoidHom) (isKleinFour_map_of_injective B hB _ e.injective)
  exact ⟨((normalizer (B : Set _)).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (map_equiv_normalizer_eq B e)).trans eN)⟩

private theorem inner_overgroup_models (hF : Nat.card F = 9)
    (S : Sylow 2 (pGammaL2PSLRange F)) (M : Subgroup (pGammaL2PSLRange F))
    (hSM : (S : Subgroup _) ≤ M) (hM : M ≠ ⊤) :
    M = (S : Subgroup _) ∨ Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
  let e := (pGammaL2PSLRangeEquiv F).symm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS'M : (S' : Subgroup (PSL2 F)) ≤ M.map e.toMonoidHom := map_mono hSM
  have hM' : M.map e.toMonoidHom ≠ ⊤ := by
    intro h
    apply hM
    apply map_injective (f := e.toMonoidHom) e.injective
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using h
  rcases LinearWitnesses.InnerPlacement.Nine.proper_overgroup_models hF S'
    (M.map e.toMonoidHom) hS'M hM' with he | heM
  · exact Or.inl (map_injective (f := e.toMonoidHom) e.injective he)
  · obtain ⟨eM⟩ := heM
    exact Or.inr ⟨(M.equivMapOfInjective e.toMonoidHom e.injective).trans eM⟩

private theorem perm_four_card {H : Type*} [Group H] (e : H ≃* Equiv.Perm (Fin 4)) :
    Nat.card H = 24 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

omit [Finite (PGammaL2 F)] in
private theorem inner_normalizer_card (hF : Nat.card F = 9)
    (B : Subgroup (PGammaL2 F)) (hB : IsKleinFour B) (hBL : B ≤ pGammaL2PSLRange F) :
    Nat.card ((normalizer (B : Set (PGammaL2 F))).subgroupOf (pGammaL2PSLRange F)) = 24 := by
  let := hB
  rw [subgroupOf_normalizer_eq hBL]
  exact perm_four_card (inner_normalizer_equiv hF _ (klein_subgroupOf B _ hBL)).some

omit [Finite (PGammaL2 F)] in
private theorem linear_normalizer_card (hF : Nat.card F = 9)
    (B : Subgroup (PGL2 F)) (hB : IsKleinFour B)
    (hBL : B ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range) :
    Nat.card (normalizer (B : Set (PGL2 F))) = 24 := by
  let := hB
  let L : Subgroup (PGL2 F) := Matrix.ProjectiveSpecialLinearGroup.toPGL.range
  let e := (psl2EquivToPGLRange F).symm
  let B₀ := B.subgroupOf L
  let : IsKleinFour B₀ := klein_subgroupOf B L hBL
  obtain ⟨eN⟩ := LinearWitnesses.InnerPlacement.Nine.normalizer_equiv hF
    (B₀.map e.toMonoidHom) (isKleinFour_map_of_injective B₀ inferInstance _ e.injective)
  have hcard : Nat.card (normalizer (B₀ : Set L)) = 24 := by
    apply perm_four_card
    exact ((normalizer (B₀ : Set L)).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (map_equiv_normalizer_eq B₀ e)).trans eN)
  have hle : (normalizer (B₀ : Set L)).map L.subtype ≤ normalizer (B : Set (PGL2 F)) := by
    have hm : B₀.map L.subtype = B := map_subgroupOf_eq_of_le hBL
    have hn := le_normalizer_map (H := B₀) L.subtype
    rwa [hm] at hn
  apply Nat.le_antisymm
  · exact normalizer_card_le B (pgl2_kleinFour_centralizer_eq_self F (odd_nine hF) B hB)
  · have := card_le_of_le hle
    rwa [card_map_of_injective L.subtype_injective, hcard] at this

private theorem linear_sylow_card (hF : Nat.card F = 9)
    (T : Sylow 2 (PGammaL2 F)) :
    Nat.card ((T : Subgroup (PGammaL2 F)).comap
      (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) = 16 := by
  let P := pGammaL2PGLRange F
  obtain ⟨U, hU⟩ := T.exists_subgroupOf_eq_of_normal P
  have hUc : Nat.card U = 16 := by
    rw [U.card_eq_multiplicity, ← Nat.card_congr (pGammaL2PGLRangeEquiv F).toEquiv,
      pgl2_card_formula, hF]
    decide +kernel
  have he : (T : Subgroup (PGammaL2 F)).comap SemidirectProduct.inl =
      ((T : Subgroup (PGammaL2 F)).subgroupOf P).map
        (pGammaL2PGLRangeEquiv F).symm.toMonoidHom := by
    rw [map_equiv_eq_comap_symm']
    rfl
  rw [he, ← hU, card_map_of_injective (pGammaL2PGLRangeEquiv F).symm.injective]
  exact hUc

private theorem sylow_not_le_normalizer (hF : Nat.card F = 9)
    (T : Sylow 2 (PGammaL2 F)) (B : Subgroup (PGL2 F))
    (hB : IsKleinFour B) (hBL : B ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range) :
    ¬ (T : Subgroup (PGammaL2 F)) ≤
      normalizer (B.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) : Set _) := by
  intro h
  have hi := comap_mono (f := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) h
  rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self_of_injective SemidirectProduct.inl_injective] at hi
  have hd := card_dvd_of_le hi
  rw [linear_sylow_card hF T, linear_normalizer_card hF B hB hBL] at hd
  norm_num at hd

private theorem card_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← subgroupOf_map_subtype H K, card_map_of_injective K.subtype_injective]

private theorem inner_sup_sylow (hF : Nat.card F = 9) (T : Sylow 2 (PGammaL2 F)) :
    pGammaL2PSLRange F ⊔ (T : Subgroup (PGammaL2 F)) = ⊤ := by
  have hL : (pGammaL2PSLRange F).index = 4 := by
    have hc := (pGammaL2PSLRange F).card_mul_index
    rw [← Nat.card_congr (pGammaL2PSLRangeEquiv F).toEquiv,
      Atlas.Comparisons.Exceptional.psl2Card9_card hF, full_card hF] at hc
    omega
  have hT : (T : Subgroup (PGammaL2 F)).index = 45 := by
    have hc := (T : Subgroup (PGammaL2 F)).card_mul_index
    rw [full_sylow_card hF T, full_card hF] at hc
    omega
  apply index_eq_one.mp
  apply Nat.dvd_one.mp
  have hdiv := Nat.dvd_gcd (index_dvd_of_le (le_sup_left : pGammaL2PSLRange F ≤
    pGammaL2PSLRange F ⊔ (T : Subgroup (PGammaL2 F))))
    (index_dvd_of_le (le_sup_right : (T : Subgroup (PGammaL2 F)) ≤
    pGammaL2PSLRange F ⊔ (T : Subgroup (PGammaL2 F))))
  simpa only [hL, hT, show Nat.gcd 4 45 = 1 by decide] using hdiv

/-- The prescribed Sylow meets the full normalizer in order sixteen and
those two subgroups generate the full semilinear group. Both inner four-group
classes are retained. -/
theorem fourNormalizerSylowGeometry (hF : Nat.card F = 3 ^ 2) :
    FourNormalizerSylowGeometry F := by
  have h9 : Nat.card F = 9 := by simpa using hF
  intro T B hB hBL hBT
  let i : PGL2 F →* PGammaL2 F := SemidirectProduct.inl
  let A := B.map i
  let N := normalizer (A : Set (PGammaL2 F))
  let L := pGammaL2PSLRange F
  let : L.Normal := pGammaL2PSLRange_normal F (odd_nine h9) (by omega)
  let : IsKleinFour A := isKleinFour_map_of_injective B hB i SemidirectProduct.inl_injective
  have hAL : A ≤ L := by
    rintro x ⟨b, hb, rfl⟩
    obtain ⟨y, hy⟩ := hBL hb
    exact ⟨y, by change i (Matrix.ProjectiveSpecialLinearGroup.toPGL y) = i b; rw [hy]⟩
  have hAT : A ≤ (T : Subgroup (PGammaL2 F)) := hBT
  have hnot : ¬ (T : Subgroup (PGammaL2 F)) ≤ N := sylow_not_le_normalizer h9 T B hB hBL
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal L
  let D : Subgroup (PGammaL2 F) := (T : Subgroup _) ⊓ L
  have hD : Nat.card D = 8 := by
    rw [← card_subgroupOf, ← hS]
    exact inner_sylow_card h9 S
  have hAD : A ≤ D := le_inf hAT hAL
  have hDN : D ≤ N := normalizes_four_of_card_eight A D hAD hD
  let H : Subgroup (PGammaL2 F) := N ⊓ L
  have hH : Nat.card H = 24 := by
    rw [← card_subgroupOf]
    exact inner_normalizer_card h9 A inferInstance hAL
  have eH : Nonempty (H ≃* Equiv.Perm (Fin 4)) := by
    have eN := (inner_normalizer_equiv h9 (A.subgroupOf L) (klein_subgroupOf A L hAL)).some
    rw [← subgroupOf_normalizer_eq hAL] at eN
    have eMap := (N.subgroupOf L).equivMapOfInjective L.subtype L.subtype_injective
    rw [subgroupOf_map_subtype] at eMap
    exact ⟨eMap.symm.trans eN⟩
  obtain ⟨eD⟩ := eight_equiv_of_symmetric D H (le_inf hDN inf_le_right) hD eH.some
  have hTD : (T : Subgroup (PGammaL2 F)) ≤ normalizer (D : Set (PGammaL2 F)) :=
    (le_inf (T : Subgroup (PGammaL2 F)).le_normalizer
      (le_normalizer_of_normal (H := L))).trans inf_normalizer_le_normalizer_inf
  have hidx : N.relIndex (T : Subgroup (PGammaL2 F)) = 2 :=
    index_two_of_two_fours _ D A eD hTD hAD inferInstance hnot
  constructor
  · have hc := (N.subgroupOf (T : Subgroup (PGammaL2 F))).card_mul_index
    change Nat.card (N.subgroupOf (T : Subgroup (PGammaL2 F))) *
      N.relIndex (T : Subgroup (PGammaL2 F)) = Nat.card T at hc
    rw [hidx, full_sylow_card h9 T, card_subgroupOf] at hc
    change Nat.card ((T : Subgroup (PGammaL2 F)).subgroupOf N) = 16
    rw [card_subgroupOf, inf_comm]
    omega
  · let J : Subgroup (PGammaL2 F) := (T : Subgroup _) ⊔ N
    let M := J.subgroupOf L
    have hSM : (S : Subgroup L) ≤ M := by
      rw [hS]
      exact comap_mono le_sup_left
    have hHM : N.subgroupOf L ≤ M := comap_mono le_sup_right
    by_cases hM : M = ⊤
    · have hLJ : L ≤ J := subgroupOf_eq_top.mp hM
      apply top_unique
      rw [← inner_sup_sylow h9 T]
      exact sup_le hLJ le_sup_left
    · rcases inner_overgroup_models h9 S M hSM hM with hMS | heM
      · have hd := card_dvd_of_le hHM
        rw [inner_normalizer_card h9 A inferInstance hAL, hMS, inner_sylow_card h9 S] at hd
        norm_num at hd
      · obtain ⟨eM⟩ := heM
        let K : Subgroup (PGammaL2 F) := J ⊓ L
        have eK : K ≃* Equiv.Perm (Fin 4) := by
          have em := M.equivMapOfInjective L.subtype L.subtype_injective
          change M ≃* (J.subgroupOf L).map L.subtype at em
          rw [subgroupOf_map_subtype] at em
          exact em.symm.trans eM
        have hHK : H = K := eq_of_le_of_card_ge (inf_le_inf le_sup_right le_rfl)
          (by rw [hH, perm_four_card eK])
        have hAK : A ≤ K := le_inf (le_normalizer.trans le_sup_right) hAL
        let : IsKleinFour (A.subgroupOf K) := klein_subgroupOf A K hAK
        let : (A.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hAK).mpr
          (hHK ▸ (inf_le_left : H ≤ N))
        have hcore := normal_four_eq_core eK (A.subgroupOf K)
        have hcoremap : (pCore 2 K).map K.subtype = A := by
          rw [← hcore, map_subgroupOf_eq_of_le hAK]
        have hJK : J ≤ normalizer (K : Set (PGammaL2 F)) :=
          (le_inf J.le_normalizer (le_normalizer_of_normal (H := L))).trans
            inf_normalizer_le_normalizer_inf
        have hJN : J ≤ N := by
          have hn := hJK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
          rwa [hcoremap] at hn
        exact (hnot (le_sup_left.trans hJN)).elim

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.NineGeometry.SylowNormalizers
