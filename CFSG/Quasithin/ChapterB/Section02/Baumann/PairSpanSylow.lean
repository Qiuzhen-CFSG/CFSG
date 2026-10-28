module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.SpanSylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.SylowNormalSupplementProduct

/-!
# Sylow transport through a pair of exchanged normal factors

A componentwise Baumann conjugate span places one factor Sylow inside a
prescribed Sylow container. Conjugating it into the prescribed two-group
can exchange the factors; the original Sylow exchange then supplies both
factor Sylows in that same two-group. Relative normality and the Sylow
index theorem give the Sylow subgroup of the full residual supplement.
No individual factor is assumed normal in the entire ambient group.

Source: Aschbacher–Smith 3.1.7, printed pp.575–576.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Sylows of two relatively normal factors contained in a two-group give
its Sylow property in the full normal supplement. -/
theorem sylow_sup_of_normal_pair (K L R : Subgroup G)
    [(K.subgroupOf (K ⊔ L)).Normal]
    (hR : IsPGroup 2 R) (hn : R ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hK : ∃ P, Chapter1.IsSylowIn 2 P K ∧ P ≤ R)
    (hL : ∃ P, Chapter1.IsSylowIn 2 P L ∧ P ≤ R) :
    Chapter1.IsSylowIn 2 R ((K ⊔ L) ⊔ R) := by
  let X := K ⊔ L
  let K' := K.subgroupOf X
  let L' := L.subgroupOf X
  let R' := R.subgroupOf X
  have hjoin : K' ⊔ L' = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ X from le_sup_left) (show L ≤ X from le_sup_right)]
    exact subgroupOf_self X
  obtain ⟨P,⟨P₀,hP₀⟩,hPR⟩ := hK
  obtain ⟨Q,⟨Q₀,hQ₀⟩,hQR⟩ := hL
  let eK := (subgroupOfEquivOfLe (show K ≤ X from le_sup_left)).symm
  let eL := (subgroupOfEquivOfLe (show L ≤ X from le_sup_right)).symm
  let P' := P₀.mapSurjective (f := eK.toMonoidHom) eK.surjective
  let Q' := Q₀.mapSurjective (f := eL.toMonoidHom) eL.surjective
  have hP' : (P' : Subgroup K').map K'.subtype ≤ R' := by
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact hPR (hP₀ ▸ mem_map_of_mem K.subtype hz)
  have hQ' : (Q' : Subgroup L').map L'.subtype ≤ R' := by
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact hQR (hQ₀ ▸ mem_map_of_mem L.subtype hz)
  have hR' : IsPGroup 2 R' := hR.comap_subtype
  obtain ⟨S,hS⟩ := hR'.exists_sylow_sup_of_normal_sylow_images K' L' R'
    (hjoin.symm ▸ le_top) P' Q' hP' hQ'
  have hstop : Chapter1.IsSylowIn 2 R' (⊤ : Subgroup X) := hjoin ▸ ⟨S,hS⟩
  have hs := (Chapter1.IsSylowIn.map_iff X.subtype X.subtype_injective).mpr hstop
  rw [subgroupOf_map_subtype, ← MonoidHom.range_eq_map,range_subtype] at hs
  obtain ⟨S₀,hS₀⟩ := hs
  exact hR.exists_sylow_sup_of_coprime_index X R hn (S₀ : Subgroup X)
    S₀.not_dvd_index (hS₀.le.trans inf_le_left)

omit [Finite G] in
/-- A chosen exchanging element transports either factor's Sylow in R
to a Sylow of the other factor in the same R. -/
theorem sylows_in_exchanged_pair (T : Subgroup G) (K L R P : Subgroup G)
    (hTR : T ≤ normalizer (R : Set G)) (hPR : P ≤ R)
    (hP : Chapter1.IsSylowIn 2 P K ∨ Chapter1.IsSylowIn 2 P L)
    (hexchange : ∃ t ∈ T, K.map (MulAut.conj t).toMonoidHom = L ∧
      L.map (MulAut.conj t).toMonoidHom = K) :
    (∃ P, Chapter1.IsSylowIn 2 P K ∧ P ≤ R) ∧
      (∃ P, Chapter1.IsSylowIn 2 P L ∧ P ≤ R) := by
  obtain ⟨t,ht,hK,hL⟩ := hexchange
  have hR : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hTR ht)
  have hle : P.map (MulAut.conj t).toMonoidHom ≤ R := (map_mono hPR).trans_eq hR
  rcases hP with hP | hP
  · have hs := (Chapter1.IsSylowIn.map_iff (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).mpr hP
    rw [hK] at hs
    exact ⟨⟨P,hP,hPR⟩,⟨_,hs,hle⟩⟩
  · have hs := (Chapter1.IsSylowIn.map_iff (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).mpr hP
    rw [hL] at hs
    exact ⟨⟨_,hs,hle⟩,⟨P,hP,hPR⟩⟩

/-- The paired S5 span in 3.1.7 gives Sylow membership in the whole
residual supplement, even though either individual factor can be exchanged. -/
theorem sylow_sup_of_permuted_pair_span
    (T : Sylow 2 G) (K L D R E Q : Subgroup G)
    [(K.subgroupOf (K ⊔ L)).Normal]
    (hRT : R ≤ T) (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hBR : baumann (T : Subgroup G) ≤ R)
    (hR : Chapter1.IsSylowIn 2 R D) (hED : E ≤ normalizer (D : Set G))
    (hn : R ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hQ : Chapter1.IsSylowIn 2 Q (K ⊔ baumann (T : Subgroup G)))
    (hspan : Q ≤ conjugateSpanBy (baumann (T : Subgroup G)) E)
    (hperm : ∀ g : G, K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom = L)
    (hexchange : ∃ t ∈ (T : Subgroup G), K.map (MulAut.conj t).toMonoidHom = L ∧
      L.map (MulAut.conj t).toMonoidHom = K) :
    Chapter1.IsSylowIn 2 R ((K ⊔ L) ⊔ R) := by
  have hQD : Q ≤ D := hspan.trans (conjugateSpanBy_le
    (hBR.trans (Chapter1.isSylowIn_iff.mp hR).2.1) hED)
  obtain ⟨g,hg,hgQ⟩ := exists_conjugate_le_relative_sylow D R Q hR
    (Chapter1.isSylowIn_iff.mp hQ).1 hQD
  have : (K.subgroupOf (K ⊔ baumann (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hBK)
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hQ le_sup_left
    (Subgroup.Normal.isSubnormal inferInstance)
  have hs' := (Chapter1.IsSylowIn.map_iff (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).mpr hs
  have hPR : (Q ⊓ K).map (MulAut.conj g).toMonoidHom ≤ R :=
    (map_mono inf_le_left).trans hgQ
  have hh : Chapter1.IsSylowIn 2 ((Q ⊓ K).map (MulAut.conj g).toMonoidHom) K ∨
      Chapter1.IsSylowIn 2 ((Q ⊓ K).map (MulAut.conj g).toMonoidHom) L := by
    rcases hperm g with he | he
    · rw [he] at hs'
      exact Or.inl hs'
    · rw [he] at hs'
      exact Or.inr hs'
  obtain ⟨hK,hL⟩ := sylows_in_exchanged_pair T K L R _ hTR hPR hh hexchange
  exact sylow_sup_of_normal_pair K L R (T.isPGroup'.to_le hRT) hn hK hL
end CFSG.Quasithin.ChapterB
