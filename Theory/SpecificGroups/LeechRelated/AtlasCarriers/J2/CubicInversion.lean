module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SolvableActors
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap
public import Theory.GroupTheory.CubicSylowInversion
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Inverting an escaping cubic above the Hall--Janko two-core quotient

The native Sylow cover puts a proper full-Sylow overgroup in a local of
order 1920 or 1152. A section with a factor fifteen forces the first local;
its full Sylow normalizer therefore normalizes the section. An escaping
cubic in an index-three Sylow overgroup cannot normalize that Sylow.
The three-coset quotient and the cubic lifting theorem give an inverter
inside the prescribed Sylow, including above an arbitrary two-core.

The source application keeps the actual perfect residual and its two-core
quotient of order 60. Perfect normalizer lifting preserves escape across
the quotient. No splitting or involutory-lift premise is used.
Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
The imported native J₂ cover retains the ATLAS J2G1-p100B0 attribution.
-/

public noncomputable section
open Subgroup
namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics

/-- A proper section with a factor fifteen and normalized by a full Sylow
is also normalized by its entire Sylow normalizer. -/
theorem sylow_normalizer_le_section_normalizer (S : Sylow 2 Carrier)
    (R : Subgroup Carrier)
    (hn : (S : Subgroup Carrier) ≤ normalizer (R : Set Carrier))
    (hp : R ⊔ (S : Subgroup Carrier) ≠ ⊤) (h15 : 15 ∣ Nat.card R) :
    normalizer (S : Set Carrier) ≤ normalizer (R : Set Carrier) := by
  let S₀ := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S S₀
  let a := MulAut.conj g
  have hS : (S : Subgroup Carrier).map a.toMonoidHom = Seed.s :=
    congrArg Sylow.toSubgroup hg
  let U := R.map a.toMonoidHom
  let J := U ⊔ Seed.s
  have hJ : J ≠ ⊤ := by
    intro he
    apply hp
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [Subgroup.map_sup,hS,map_top_of_surjective _ a.surjective]
    exact he
  have h15J : 15 ∣ Nat.card J := by
    have hu : Nat.card U = Nat.card R := card_map_of_injective a.injective
    exact (hu.symm ▸ h15).trans (card_dvd_of_le (show U ≤ J from le_sup_left))
  have h128 : 128 ∣ Nat.card J :=
    PairNormalizer.card_s ▸ card_dvd_of_le (show Seed.s ≤ J from le_sup_right)
  have hJn : J ≤ normalizer (U : Set Carrier) := by
    apply sup_le U.le_normalizer
    rw [←hS]
    exact (map_mono (f := a.toMonoidHom) hn).trans (le_normalizer_map _)
  have hfirst : J = Seed.l₁ := by
    rcases SylowOvergroups.proper_overgroup_le J le_sup_right hJ with h | h
    · apply eq_of_le_of_card_ge h
      rw [FirstParabolic.card_l₁]
      exact Nat.le_of_dvd Nat.card_pos
        ((by decide : Nat.Coprime 128 15).mul_dvd_of_dvd_of_dvd h128 h15J)
    · have hd := h15J.trans (card_dvd_of_le h)
      rw [PairNormalizer.card_p₂] at hd
      norm_num at hd
  have hs : normalizer (Seed.s : Set Carrier) ≤ normalizer (U : Set Carrier) := by
    rw [SecondParabolic.Overlap.normalizer_s_eq_B PairNormalizer.card_p₂]
    exact SecondParabolic.Overlap.B_le_l₁.trans (hfirst ▸ hJn)
  apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
  change (normalizer ((S : Subgroup Carrier) : Set Carrier)).map a.toMonoidHom ≤
    (normalizer (R : Set Carrier)).map a.toMonoidHom
  rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq,hS]
  exact hs

/-- An escaping cubic in an index-three Sylow overgroup above J₂ is
inverted by the prescribed Sylow. All kernel and section maps are literal. -/
theorem escaping_cubic_inverted {G : Type*} [Group G] [Finite G]
    (f : G →* Carrier) (hf : Function.Surjective f)
    (S : Sylow 2 G)
    (J D : Subgroup G) (hSJ : (S : Subgroup G) ≤ J) (hDJ : D ≤ J)
    (hJ : Nat.card J = 3 * Nat.card S) (hD : Nat.card D = 3)
    (R : Subgroup Carrier)
    (hn : (S.mapSurjective hf : Subgroup Carrier) ≤ normalizer (R : Set Carrier))
    (hp : R ⊔ (S.mapSurjective hf : Subgroup Carrier) ≠ ⊤)
    (h15 : 15 ∣ Nat.card R) (he : ¬ D.map f ≤ normalizer (R : Set Carrier)) :
    ∃ t ∈ (S : Subgroup G), ∀ d ∈ D, t*d*t⁻¹ = d⁻¹ := by
  let SJ := S.subtype hSJ
  have hi : (SJ : Subgroup J).index = 3 := by
    have hh := (SJ : Subgroup J).card_mul_index
    have hc : Nat.card SJ = Nat.card S :=
      Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv
    rw [hc,hJ] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hh.trans (Nat.mul_comm _ _))
  have hp' : pCore 2 J < (SJ : Subgroup J) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal SJ) ?_
    intro heq
    have hn' : (SJ : Subgroup J).Normal := heq ▸ inferInstance
    have hnorm : D ≤ normalizer (S : Set G) :=
      hDJ.trans ((normal_subgroupOf_iff_le_normalizer hSJ).mp hn')
    apply he
    exact ((map_mono (f := f) hnorm).trans (le_normalizer_map f)).trans
      (sylow_normalizer_le_section_normalizer (S.mapSurjective hf) R hn hp h15)
  obtain ⟨e⟩ := sylow_index_three_core_quotient SJ hi hp'
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨t,ht,hinv⟩ := cubic_inverted_in_sylow_of_two_kernel q hq hqk
    (D.subgroupOf J) (by rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv,hD]) SJ
  exact ⟨t,ht,fun d hd => congrArg Subtype.val (hinv ⟨d,hDJ hd⟩ hd)⟩

private theorem proper_normalized_join {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (S : Sylow 2 X) (R : Subgroup X) (hr : R ≠ ⊤)
    (hn : (S : Subgroup X) ≤ normalizer (R : Set X)) : R ⊔ (S : Subgroup X) ≠ ⊤ := by
  intro he
  let : R.Normal := normalizer_eq_top_iff.mp (top_unique (he ▸ sup_le R.le_normalizer hn))
  let : Nontrivial (X ⧸ R) := QuotientGroup.nontrivial_iff.mpr hr
  let : Group.IsPerfect (X ⧸ R) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective R)
  let : Group.IsNilpotent (X ⧸ R) :=
    (isPGroup_quotient_of_sup_eq_top R (S : Subgroup X) S.isPGroup' he).isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ R) inferInstance

/-- Above a two-core quotient J₂, an escaping cubic is inverted from the
original Sylow when the same normalized perfect section has quotient order 60. -/
theorem escaping_cubic_inverted_above_twoCore
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (e : (G ⧸ pCore 2 G) ≃* Carrier) (S : Sylow 2 G)
    (R J D : Subgroup G) [Group.IsPerfect R]
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (hSJ : (S : Subgroup G) ≤ J) (hDJ : D ≤ J)
    (hJ : Nat.card J = 3 * Nat.card S) (hD : Nat.card D = 3)
    (hR : Nat.card (R ⧸ pCore 2 R) = 60) (hDn : ¬ D ≤ normalizer (R : Set G)) :
    ∃ t ∈ (S : Subgroup G), ∀ d ∈ D, t*d*t⁻¹ = d⁻¹ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let R' := R.map f
  let S' := S.mapSurjective hf
  have hn : (S' : Subgroup Carrier) ≤ normalizer (R' : Set Carrier) :=
    (map_mono (f := f) hSR).trans (le_normalizer_map f)
  have hpre : (normalizer (R' : Set Carrier)).comap f = normalizer (R : Set G) := by
    change (normalizer (R.map (e.toMonoidHom.comp q) : Set Carrier)).comap
      (e.toMonoidHom.comp q) = _
    rw [←map_map,←comap_comap,comap_normalizer_eq_of_surjective _ e.surjective,
      comap_map_eq_self_of_injective e.injective]
    exact normalizer_perfect_image_comap R (pCore 2 G) pCore_isPGroup
      ((pCore_isPGroup.le_sylow_of_normal S).trans hSR)
  have hesc : ¬ D.map f ≤ normalizer (R' : Set Carrier) := by
    intro hh
    apply hDn
    have hh' := map_le_iff_le_comap.mp hh
    rwa [hpre] at hh'
  have hne : R' ≠ ⊤ := by
    intro he
    apply hesc
    rw [he,normalizer_eq_top]
    exact le_top
  let : Group.IsPerfect Carrier := Group.IsPerfect.ofSurjective hf
  have hp := proper_normalized_join S' R' hne hn
  let r := f.subgroupMap R
  have hrk : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let a := r.pCoreQuotientEquiv (f.subgroupMap_surjective R) hrk
  have hc : Nat.card (R' ⧸ pCore 2 R') = 60 :=
    (Nat.card_congr a.toEquiv).symm.trans hR
  have h15 : 15 ∣ Nat.card R' := (by decide : 15 ∣ 60).trans
    (hc ▸ card_quotient_dvd_card (pCore 2 R'))
  exact escaping_cubic_inverted f hf S J D hSJ hDJ hJ hD R' hn hp h15 hesc

end Sporadic.LeechRelated.J2
