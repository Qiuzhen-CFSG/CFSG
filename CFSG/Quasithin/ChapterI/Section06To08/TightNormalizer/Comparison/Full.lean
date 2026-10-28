module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Basic
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The full-normalizer branch of I.7.7

Write `S₀ = S ∩ Kᵍ`. Restricting the supplied Sylow subgroup of `KᵍR`
to its relatively normal subgroup `Kᵍ` realizes `S₀` as a Sylow image.
Conjugation and Sylow conjugacy identify it with every Sylow image in `K`.

When `S₀` normalizes `R`, I.7.2(5) makes it normalize `K`. Extend `RS₀`
to a Sylow subgroup of `KS₀` and restrict to `K`, obtaining an `S₀`-invariant
Sylow image `R₁` containing `R`. The equal orders of `S₀` and `R₁` give
the relative-index bound in `S₀R₁`. I.7.3 makes `R₁` normalize `S₀`,
and I.7.2(5) then makes it normalize `Kᵍ`. Maximality of `R` gives `R₁ = R`.
The final multiplicative equivalence comes from the actual Sylow equivalences.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.7, printed p.427 (PDF p.438), the case `S₁ = S₀`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem full_sylow_of_maximal {A L : Subgroup G}
    (hp : IsPGroup 2 A) (hle : A ≤ L)
    (hm : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ L → A ≤ T → T ≤ A) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = A := by
  obtain ⟨P, hP⟩ := (hp.of_equiv (subgroupOfEquivOfLe hle).symm).exists_le_sylow
  have ha : A ≤ (P : Subgroup L).map L.subtype := by
    rw [← map_subgroupOf_eq_of_le hle]
    exact map_mono hP
  exact ⟨P, le_antisymm (hm _ (P.isPGroup'.map _) (map_subtype_le _) ha) ha⟩

private theorem full_restrict_sylow {L N : Subgroup G} (hNL : N ≤ L)
    (hn : L ≤ normalizer (N : Set G)) (P : Sylow 2 L) :
    ∃ Q : Sylow 2 N,
      (Q : Subgroup N).map N.subtype = (P : Subgroup L).map L.subtype ⊓ N := by
  let : (N.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal (N.subgroupOf L)
  let e := subgroupOfEquivOfLe hNL
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hzP : (z : L) ∈ (P : Subgroup L) := by
      change z ∈ (Q : Subgroup (N.subgroupOf L)) at hz
      rw [hQ] at hz
      exact hz
    exact ⟨⟨(z : L), hzP, rfl⟩, z.property⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyN⟩
    refine ⟨⟨(y : G), hyN⟩, ?_, rfl⟩
    refine ⟨⟨y, hyN⟩, ?_, rfl⟩
    change (⟨y, hyN⟩ : N.subgroupOf L) ∈ (Q : Subgroup (N.subgroupOf L))
    rw [hQ]
    exact hy

omit [Finite G] in
private theorem full_tight_conjugate {K : Subgroup G}
    (hK : Theory.GroupTheory.IsTightlyEmbedded K) (g : G) :
    Theory.GroupTheory.IsTightlyEmbedded (conjSubgroup K g) := by
  let e := MulAut.conj g
  refine ⟨?_, ?_⟩
  · simpa only [card_conjSubgroup] using hK.1
  · intro x hx
    have hn : e.symm x ∉ normalizer (K : Set G) := by
      intro hn
      apply hx
      rw [conjSubgroup, ← map_equiv_normalizer_eq K e]
      exact ⟨e.symm x, hn, e.apply_symm_apply x⟩
    have heq : (K.map e.toMonoidHom) ⊓
        (K.map e.toMonoidHom).map (MulAut.conj x).toMonoidHom =
        (K ⊓ K.map (MulAut.conj (e.symm x)).toMonoidHom).map e.toMonoidHom := by
      rw [map_inf _ _ e.toMonoidHom e.injective]
      congr 1
      ext y
      simp only [mem_map_equiv, MulAut.conj_symm_apply, map_mul, map_inv]
    change Odd (Nat.card ↥(K.map e.toMonoidHom ⊓
      (K.map e.toMonoidHom).map (MulAut.conj x).toMonoidHom))
    rw [heq, card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hK.2 _ hn

namespace TightNormalizerSetup
variable {K : Subgroup G} {g : G} {R S : Subgroup G} (h : TightNormalizerSetup K g R S)
include h

/-- The intersection with `Kᵍ` is the exact ambient image of a Sylow subgroup. -/
theorem intersection_sylow : ∃ P : Sylow 2 (conjSubgroup K g),
    (P : Subgroup (conjSubgroup K g)).map (conjSubgroup K g).subtype =
      S ⊓ conjSubgroup K g := by
  obtain ⟨U, hU⟩ := full_sylow_of_maximal h.hSp h.hSle h.hSmax
  obtain ⟨P, hP⟩ := full_restrict_sylow
    (le_sup_left : conjSubgroup K g ≤ conjSubgroup K g ⊔ R) h.overgroup_normalizes U
  exact ⟨P, hU ▸ hP⟩

/-- Conjugation and Sylow conjugacy identify `S₀` with any Sylow image in `K`. -/
theorem intersection_equiv_sylow (P : Sylow 2 K) :
    Nonempty (↥(S ⊓ conjSubgroup K g) ≃* (P : Subgroup K).map K.subtype) := by
  obtain ⟨Q, hQ⟩ := h.intersection_sylow
  let eK : K ≃* conjSubgroup K g := (MulAut.conj g).subgroupMap K
  let P' : Sylow 2 (conjSubgroup K g) :=
    P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  let eP : P ≃* P' :=
    (P : Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective
  let eQ : Q ≃* ↥(S ⊓ conjSubgroup K g) :=
    ((Q : Subgroup (conjSubgroup K g)).equivMapOfInjective
      (conjSubgroup K g).subtype (conjSubgroup K g).subtype_injective).trans
        (MulEquiv.subgroupCongr hQ)
  exact ⟨eQ.symm.trans ((Q.equiv P').trans (eP.symm.trans
    ((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective)))⟩

/-- In the full-normalizer branch, extend `R` to an `S₀`-invariant Sylow image in `K`. -/
theorem invariant_sylow_extension
    (hfull : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) = S ⊓ conjSubgroup K g) :
    ∃ P : Sylow 2 K, let R1 := (P : Subgroup K).map K.subtype
      R ≤ R1 ∧ S ⊓ conjSubgroup K g ≤ normalizer (R1 : Set G) := by
  let S0 := S ⊓ conjSubgroup K g
  have hS0p : IsPGroup 2 S0 := h.hSp.to_le inf_le_left
  have hS0R : S0 ≤ normalizer (R : Set G) := by
    change S ⊓ conjSubgroup K g ≤ _
    rw [← hfull]
    exact inf_le_right
  have hS0K : S0 ≤ normalizer (K : Set G) :=
    hS0R.trans (h.hK.normalizer_le h.hRp h.hRne (h.hRle.trans inf_le_left))
  let L := K ⊔ S0
  have hRL : R ⊔ S0 ≤ L := sup_le_sup (h.hRle.trans inf_le_left) le_rfl
  have hp : IsPGroup 2 ↥(R ⊔ S0) := h.hRp.to_sup_of_normal_left' hS0p hS0R
  obtain ⟨U, hU⟩ := (hp.of_equiv (subgroupOfEquivOfLe hRL).symm).exists_le_sylow
  let A := (U : Subgroup L).map L.subtype
  have hRA : R ⊔ S0 ≤ A := by
    rw [← map_subgroupOf_eq_of_le hRL]
    exact map_mono hU
  obtain ⟨P, hP⟩ := full_restrict_sylow (le_sup_left : K ≤ L)
    (sup_le K.le_normalizer hS0K) U
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    exact le_inf (le_sup_left.trans hRA) (h.hRle.trans inf_le_left)
  · rw [hP]
    exact (le_inf ((le_sup_right.trans hRA).trans A.le_normalizer) hS0K).trans
      inf_normalizer_le_normalizer_inf

/-- In the full-normalizer branch, the Sylow extension cannot enlarge `R`. -/
theorem sylow_of_full
    (hfull : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) = S ⊓ conjSubgroup K g) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = R := by
  obtain ⟨P, hRP, hn⟩ := h.invariant_sylow_extension hfull
  let R1 := (P : Subgroup K).map K.subtype
  let S0 := S ⊓ conjSubgroup K g
  let U := S0 ⊔ R1
  have hR1p : IsPGroup 2 R1 := P.isPGroup'.map _
  have hS0p : IsPGroup 2 S0 := h.hSp.to_le inf_le_left
  obtain ⟨e⟩ := h.intersection_equiv_sylow P
  have hc : Nat.card S0 = Nat.card R1 := Nat.card_congr e.toEquiv
  have hne : S0 ≠ ⊥ := by
    intro hbot
    have hb : R1 = ⊥ := card_eq_one.mp (hc.symm.trans (card_eq_one.mpr hbot))
    exact h.hRne (eq_bot_iff.mpr (hb ▸ hRP))
  have hUp : IsPGroup 2 U := hS0p.to_sup_of_normal_right' hR1p hn
  obtain ⟨Q, hQ⟩ := h.intersection_sylow
  have hsetup : TightPGroupSetup (conjSubgroup K g) U S0 U := by
    refine ⟨full_tight_conjugate h.hK g, hS0p, hne,
      le_inf le_sup_left inf_le_right, ?_, hUp, le_rfl, le_sup_left⟩
    intro T hTp hT hS0T
    have hTK : T ≤ conjSubgroup K g := hT.trans inf_le_right
    have hQT : (Q : Subgroup (conjSubgroup K g)) ≤ T.subgroupOf (conjSubgroup K g) := by
      apply map_le_iff_le_comap.mp
      exact hQ.trans_le hS0T
    have hTeq := Q.is_maximal' (hTp.of_equiv (subgroupOfEquivOfLe hTK).symm) hQT
    have heq : T = S0 := by
      rw [← map_subgroupOf_eq_of_le hTK, hTeq, hQ]
    exact heq.le
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes R1 S0 hn
  have hUbound : Nat.card U ≤ Nat.card R1 * Nat.card S0 := by
    rw [hprod, sup_comm R1 S0]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  have hindex : S0.relIndex U ≤ Nat.card S0 := by
    have hm := (S0.subgroupOf U).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : S0 ≤ U)).toEquiv] at hm
    change S0.relIndex U * Nat.card S0 = Nat.card U at hm
    have hb : S0.relIndex U * Nat.card S0 ≤ Nat.card S0 * Nat.card S0 := by
      rw [hm]
      exact hUbound.trans_eq (by rw [hc])
    exact Nat.le_of_mul_le_mul_right hb Nat.card_pos
  have hnormal := lemma_I_7_3 hsetup hindex
  have hR1S0 : R1 ≤ normalizer (S0 : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (le_sup_left : S0 ≤ U)).mp hnormal)
  have hR1K : R1 ≤ normalizer (conjSubgroup K g : Set G) :=
    hR1S0.trans (lemma_I_7_2_5 hsetup hne le_rfl).1
  have hle : R1 ≤ R := h.hRmax R1 hR1p (le_inf (map_subtype_le _) hR1K) hRP
  exact ⟨P, le_antisymm hle hRP⟩

/-- The factor isomorphism in the full-normalizer branch of I.7.7. -/
theorem equiv_of_full
    (hfull : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) = S ⊓ conjSubgroup K g) :
    Nonempty (↥(S ⊓ conjSubgroup K g) ≃* R) := by
  obtain ⟨P, hP⟩ := h.sylow_of_full hfull
  obtain ⟨e⟩ := h.intersection_equiv_sylow P
  exact ⟨e.trans (MulEquiv.subgroupCongr hP)⟩

/-- The two factors have equal orders in the full-normalizer branch of I.7.7. -/
theorem card_eq_of_full
    (hfull : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) = S ⊓ conjSubgroup K g) :
    Nat.card ↥(S ⊓ conjSubgroup K g) = Nat.card R := by
  obtain ⟨e⟩ := h.equiv_of_full hfull
  exact Nat.card_congr e.toEquiv

end TightNormalizerSetup
end CFSG.Quasithin.ChapterI.Section06To08
