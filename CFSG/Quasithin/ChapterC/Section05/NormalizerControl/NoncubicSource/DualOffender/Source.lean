module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Relative
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.NaturalCard
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.AlternatingCard
/-!
# The original C.5.13 dual offender and natural ratio bound

The original noncommuting x produces the literal actor Uˣ in the auxiliary
normalizer. Its kernel and displacement are the actual intersection E.
The A₅ orders give a rank-two dual offender. The universal natural cover
bounds |E| by the square of the actor order, hence gives dual quadratic
ratio at most two. All statements use the canonical centralizer quotient
and retain the full natural central layer.
Source: Aschbacher–Smith C.5.13 and B.4.7, printed pp.162 and90.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- The genuine natural source actor has its original field-order image
and yields the printed bound q(X₁*,V₁*)≤2 on the dual module. -/
theorem natural_source_dual_ratio {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    let hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    let A := (B.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))
    let ρ := centralizerQuotient (V.subgroupOf N)
    Nat.card A = Nat.card F ∧ rank A = n ∧ IsElementaryTwo A ∧ IsQuadratic ρ.dual A ∧
      fixedCodim ρ.dual A ≤ 2 * n ∧ quadraticRatio ρ.dual ≤ 2 := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let E := U K ⊓ B
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  let : IsElementaryAbelian 2 (U K) := h.elementary
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let A := (B.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))
  let ρ := centralizerQuotient (V.subgroupOf N)
  have hg := natural_source_omega_displacement h hn hT hTK P hP X hA hAX hx hnc
  have hb := relative_dual_bounds N V B E hs.2.1 hs.2.2.1 hg.1
    (by rw [commutator_comm]; exact hg.2.1.le)
    (inf_le_right.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
    (fun hc => hnc (hc.trans (centralizer_le hs.2.2.2.1))) hg.2.2.1
  have hc := natural_pair_card_bounds h hn hx hnc
  have hcard : Nat.card A = Nat.card F := hb.2.2.2.trans hc.2.1
  have hbound : fixedCodim ρ.dual A ≤ 2 * rank A := by
    have hh := Nat.log_monotone (b := 2) hc.2.2
    rw [← hcard,hb.1.card_eq_two_pow_rank,← pow_mul,Nat.log_pow (by decide : 1 < 2)] at hh
    exact hb.2.2.1.trans (by simpa only [Nat.mul_comm] using hh)
  have hrank : rank A = n := by
    rw [rank,hcard,natural_coordinate_card h hn,Nat.log_pow (by decide : 1 < 2)]
  exact ⟨hcard,hrank,hb.1,hb.2.1,by simpa only [hrank] using hbound,
    (quadraticRatio_le_two_iff ρ.dual).mpr ⟨A,hb.1,hb.2.1,hbound⟩⟩
/-- The actual A₅ source actor is a four-group dual offender on V₁. -/
theorem alternating_source_dual_ff {K T L : Subgroup G}
    (h : AlternatingPairSetup T K L) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let B := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
    let hs := alternating_five_source_omega_span h hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    let A := (B.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))
    let ρ := centralizerQuotient (V.subgroupOf N)
    Nat.card A = 4 ∧ rank A = 2 ∧ IsOffender ρ.dual A ∧
      IsQuadratic ρ.dual A ∧ IsFFModule ρ.dual := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let B := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
  let E := sourceModule K ⊓ B
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  let : IsElementaryAbelian 2 (sourceModule K) := h.block.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let A := (B.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))
  let ρ := centralizerQuotient (V.subgroupOf N)
  have hg := alternating_five_source_omega_displacement h hTK P hP X hA hAX hx hnc
  have hb := relative_dual_bounds N V B E hs.2.1 hs.2.2.1 hg.1
    (by rw [commutator_comm]; exact hg.2.1.le)
    (inf_le_right.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
    (fun hc => hnc (hc.trans (centralizer_le hs.2.2.2.1))) hg.2.2.1
  have hc := alternating_pair_card h hx hnc
  have hcard : Nat.card A = 4 := hb.2.2.2.trans hc.2
  have hrank : rank A = 2 := by rw [rank,hcard]; decide
  have hbound : fixedCodim ρ.dual A ≤ rank A := by
    rw [hrank]
    have he : Nat.card E = 4 := hc.1
    have hh : fixedCodim ρ.dual A ≤ Nat.log 2 (Nat.card E) := hb.2.2.1
    simpa only [he,show Nat.log 2 4 = 2 from rfl] using hh
  exact ⟨hcard,hrank,⟨hb.1,hbound⟩,hb.2.1,⟨A,hb.1,hbound⟩⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
