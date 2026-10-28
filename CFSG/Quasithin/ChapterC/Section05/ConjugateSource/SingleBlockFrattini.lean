module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamily
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
public import Mathlib.GroupTheory.IndexNormal

/-!
# Eliminating the source centralizer Frattini subgroup

In the single-block index-two case, TH normalizes the block and the chosen
outside conjugator preserves Φ(D) by C.5.6(4). The two cosets of TH therefore
make all M₀ preserve Φ(D). The block centralizes Φ(D), which lies in R;
the original no-common-normal hypothesis C.5.2 forces it to be trivial.
The resulting A₅ four-family theorem has no Frattini-zero premise.

Source: Aschbacher–Smith, C.5.6(7), printed p.158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]

private theorem normalizer_centralizer_frattini (R K : Subgroup G) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    normalizer (R : Set G) ⊓ normalizer (K : Set G) ≤
      normalizer ((frattini D).map D.subtype : Set G) := by
  let S := ChapterB.baumann R
  let D := S ⊓ centralizer (K : Set G)
  have hnC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
  have hnD : normalizer (R : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (D : Set G) :=
    (le_inf (inf_le_left.trans (Stellmacher.normalizer_le_normalizer_baumann R))
      (inf_le_right.trans hnC)).trans inf_normalizer_le_normalizer_inf
  exact hnD.trans (normalizer_le_normalizer_characteristic_image D (frattini D))

/-- C.5.2 eliminates the Frattini subgroup in the single-block index-two case.
Neither its triviality nor any elementary-family conclusion is assumed. -/
theorem centralizerFrattini_eq_bot_of_index_two
    (R K : Subgroup G) (hU : IsElementaryAbelian 2 (sourceModule K))
    (H M₀ T_H : Subgroup G) (hTHM : T_H ≤ M₀)
    (hM₀R : M₀ ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G))
    (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M₀ ≤ normalizer (W : Set G) → W = ⊥)
    (hindex : T_H.relIndex M₀ = 2)
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi_inv : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      ((frattini D).map D.subtype).map (MulAut.conj x⁻¹).toMonoidHom =
        (frattini D).map D.subtype) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    (frattini D).map D.subtype = ⊥ := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let D := S ⊓ centralizer (K : Set G)
  let P := (frattini D).map D.subtype
  have hPR : P ≤ R := (map_subtype_le _).trans (inf_le_left.trans inf_le_left)
  have hTHP : T_H ≤ normalizer (P : Set G) :=
    (le_inf (hTHM.trans hM₀R) hTHK).trans (normalizer_centralizer_frattini R K)
  have hKP : K ≤ normalizer (P : Set G) :=
    ((le_centralizer_iff.mp (show P ≤ centralizer (K : Set G) from
      (map_subtype_le _).trans inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
  have hHP : H ≤ normalizer (P : Set G) := hH ▸ sup_le hKP hTHP
  have hxP : x ∈ normalizer (P : Set G) := by
    have hh : x⁻¹ ∈ normalizer (P : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr hphi_inv
    simpa only [inv_inv] using (normalizer (P : Set G)).inv_mem hh
  have hxTH : x ∉ T_H := by
    intro hxt
    have hnU : x ∈ normalizer (U : Set G) :=
      normalizer_le_normalizer_characteristic_image K (blockU K) (hTHK hxt)
    have he : U.map (MulAut.conj x⁻¹).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (U : Set G)).inv_mem hnU)
    apply hnc
    change U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G)
    rw [he]
    let : IsElementaryAbelian 2 U := hU
    exact le_centralizer U
  apply hno P hPR hHP
  intro g hg
  by_cases hgTH : g ∈ T_H
  · exact hTHP hgTH
  · have hm : g * x⁻¹ ∈ T_H := by
      have hi : (T_H.subgroupOf M₀).index = 2 := hindex
      exact (mul_mem_iff_of_index_two hi (a := (⟨g, hg⟩ : M₀))
        (b := (⟨x⁻¹, M₀.inv_mem hx⟩ : M₀))).mpr
        (iff_of_false hgTH (fun hi => hxTH (by
          have hi' : x⁻¹ ∈ T_H := hi
          simpa only [inv_inv] using T_H.inv_mem hi')))
    have hh := (normalizer (P : Set G)).mul_mem (hTHP hm) hxP
    simpa using hh
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.frattini_eq_bot_of_index_two
    (h : AlternatingPairSetup R K L)
    (H M₀ T_H : Subgroup G) (hTHM : T_H ≤ M₀)
    (hM₀R : M₀ ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G)) (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M₀ ≤ normalizer (W : Set G) → W = ⊥)
    (hindex : T_H.relIndex M₀ = 2) (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    (frattini D).map D.subtype = ⊥ := by
  have hU : IsElementaryAbelian 2 (sourceModule K) := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  exact centralizerFrattini_eq_bot_of_index_two R K hU H M₀ T_H hTHM hM₀R hTHK hH
    hno hindex x hx hnc (h.frattini_invariant x (hM₀R hx) hnc)

open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily

/-- The single-block index-two source has exactly four maximum elementary
subgroups of R, with no assumed Frattini or family input. -/
theorem AlternatingPairSetup.family_of_index_two
    (h : AlternatingPairSetup R K L)
    (H M₀ T_H : Subgroup G) (hTHM : T_H ≤ M₀)
    (hM₀R : M₀ ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G)) (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M₀ ≤ normalizer (W : Set G) → W = ⊥)
    (hindex : T_H.relIndex M₀ = 2) (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    ∃ B₀ B₁ : Subgroup G,
      Stellmacher.elementaryAbelianMaxSubgroups R = {Q, V ⊔ D, B₀, B₁} ∧
      (B₀.subgroupOf (K ⊔ S)).map h.action = line 0 ∧
      (B₁.subgroupOf (K ⊔ S)).map h.action = line 1 :=
  h.family_eq_four x (hM₀R hx) hnc
    (h.frattini_eq_bot_of_index_two H M₀ T_H hTHM hM₀R hTHK hH hno hindex x hx hnc)

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.frattini_eq_bot_of_index_two (h : Setup R K F)
    (H M₀ T_H : Subgroup G) (hTHM : T_H ≤ M₀)
    (hM₀R : M₀ ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G)) (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M₀ ≤ normalizer (W : Set G) → W = ⊥)
    (hindex : T_H.relIndex M₀ = 2) (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    ((frattini (D R K)).map (D R K).subtype) = ⊥ :=
  centralizerFrattini_eq_bot_of_index_two R K h.elementary H M₀ T_H hTHM hM₀R hTHK hH
    hno hindex x hx hnc (h.frattini_invariant (hM₀R hx) hnc)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]

/-- The source maximal block normalizer eliminates Φ(D) without an index assumption. -/
theorem centralizerFrattini_eq_bot_of_coatom
    (R K : Subgroup G) (hU : IsElementaryAbelian 2 (sourceModule K))
    (H M₀ T_H : Subgroup G) (hTHM : T_H ≤ M₀)
    (hM₀R : M₀ ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G))
    (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M₀ ≤ normalizer (W : Set G) → W = ⊥)
    (hmax : IsCoatom ((normalizer (K : Set G)).subgroupOf M₀))
    (x : G) (hx : x ∈ M₀)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi_inv : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      ((frattini D).map D.subtype).map (MulAut.conj x⁻¹).toMonoidHom =
        (frattini D).map D.subtype) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    (frattini D).map D.subtype = ⊥ := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let D := S ⊓ centralizer (K : Set G)
  let P := (frattini D).map D.subtype
  have hPR : P ≤ R := (map_subtype_le _).trans (inf_le_left.trans inf_le_left)
  have hn : normalizer (R : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (P : Set G) :=
    normalizer_centralizer_frattini R K
  have hTHP : T_H ≤ normalizer (P : Set G) :=
    (le_inf (hTHM.trans hM₀R) hTHK).trans hn
  have hKP : K ≤ normalizer (P : Set G) :=
    (le_centralizer_iff.mp (show P ≤ centralizer (K : Set G) from
      (map_subtype_le _).trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hHP : H ≤ normalizer (P : Set G) := hH ▸ sup_le hKP hTHP
  have hxP : x ∈ normalizer (P : Set G) := by
    have hh : x⁻¹ ∈ normalizer (P : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr hphi_inv
    simpa only [inv_inv] using (normalizer (P : Set G)).inv_mem hh
  have hxK : x ∉ normalizer (K : Set G) := by
    intro hxK
    have hnU : x ∈ normalizer (U : Set G) :=
      normalizer_le_normalizer_characteristic_image K (blockU K) hxK
    have he : U.map (MulAut.conj x⁻¹).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (U : Set G)).inv_mem hnU)
    apply hnc
    change U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G)
    rw [he]
    let : IsElementaryAbelian 2 U := hU
    exact le_centralizer U
  have htop : (normalizer (P : Set G)).subgroupOf M₀ = ⊤ := by
    apply hmax.lt_iff.mp
    apply lt_of_le_not_ge
    · intro m hm
      exact hn ⟨hM₀R m.property, hm⟩
    · intro he
      exact hxK (he (show (⟨x, hx⟩ : M₀) ∈ (normalizer (P : Set G)).subgroupOf M₀ from hxP))
  apply hno P hPR hHP
  intro m hm
  exact (show (⟨m, hm⟩ : M₀) ∈ (normalizer (P : Set G)).subgroupOf M₀ from htop ▸ mem_top _)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
