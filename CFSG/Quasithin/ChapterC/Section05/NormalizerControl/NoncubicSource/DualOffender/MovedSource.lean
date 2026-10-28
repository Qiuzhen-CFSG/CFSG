module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Placement
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Restriction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Moved
/-!
# The source dual ratio on I=[V₁,L]

The canonical action is restricted to the actual conjugate-span image
and its original moved subgroup. The natural actor remains whole; for
A₅ its even diagonal intersection supplies the required rank budget.
No component classification or quotient-recognition premise is used.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem natural_source_moved_dual_ratio {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    quadraticRatio (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)).dual ≤ 2 := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  let A := (B.subgroupOf N).map q
  let ρ := centralizerQuotient (V.subgroupOf N)
  have hfull := natural_source_dual_ratio h hn hT hTK P hP X hA hAX hx hnc
  have hAN : K ⊔ T ≤ N := le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G))))
  have hPC := (normalizer_core_omega_span (K ⊔ T) X T P hP hA hAX).2.2.1
  have hplace : A ≤ (K.subgroupOf N).map q := natural_actor_le_block_image h (natural_internal h hn)
    hT hTK N V (le_sup_right.trans hAN) (le_sup_left.trans hAN) hs.2.1 hs.2.2.1 hPC hx
  have hAL : A ≤ closureImage (V.subgroupOf N) (K.subgroupOf N) :=
    hplace.trans (map_mono le_normalClosure)
  have he : IsElementaryTwo A := hfull.2.2.1
  have hq : IsQuadratic ρ.dual A := hfull.2.2.2.1
  have hr : rank A = n := hfull.2.1
  have hb : fixedCodim ρ.dual A ≤ 2 * rank A := by rw [hr]; exact hfull.2.2.2.2.1
  exact dual_restriction_ratio ρ (movedSpace (V.subgroupOf N) (K.subgroupOf N))
    (closureImage (V.subgroupOf N) (K.subgroupOf N)) A A le_rfl hAL he he.1 hq hb
theorem alternating_source_moved_dual_ratio {K T L : Subgroup G}
    (h : AlternatingPairSetup T K L) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := alternating_five_source_omega_span h hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    quadraticRatio (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)).dual ≤ 2 := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let B := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  let A := (B.subgroupOf N).map q
  let D := A ⊓ (K.subgroupOf N).map q
  let ρ := centralizerQuotient (V.subgroupOf N)
  have hfull := alternating_source_dual_ff h hTK P hP X hA hAX hx hnc
  have hAN : K ⊔ T ≤ N := le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G))))
  have hPC := (normalizer_core_omega_span (K ⊔ T) X T P hP hA hAX).2.2.1
  have hD : D ≠ ⊥ := alternating_actor_inf_block_ne_bot h hTK N V
    (le_sup_right.trans hAN) (le_sup_left.trans hAN) hs.2.1 hs.2.2.1 hs.2.2.2.1 hPC hx hnc
  have hDL : D ≤ closureImage (V.subgroupOf N) (K.subgroupOf N) :=
    inf_le_right.trans (map_mono le_normalClosure)
  have he : IsElementaryTwo A := hfull.2.2.1.1
  let : IsElementaryAbelian 2 A := he.2
  have hd : IsElementaryTwo D := ⟨hD,IsElementaryAbelian.of_le (show D ≤ A from inf_le_left)⟩
  have hq : IsQuadratic ρ.dual A := hfull.2.2.2.1
  have hr : rank A = 2 := hfull.2.1
  have hb : fixedCodim ρ.dual A ≤ 2 * rank D := by
    have hh : fixedCodim ρ.dual A ≤ rank A := hfull.2.2.1.2
    have hp := hd.rank_pos
    omega
  exact dual_restriction_ratio ρ (movedSpace (V.subgroupOf N) (K.subgroupOf N))
    (closureImage (V.subgroupOf N) (K.subgroupOf N)) A D inf_le_left hDL he hD hq hb
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
