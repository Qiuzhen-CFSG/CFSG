module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ElementarySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterCommutatorCardSource

/-!
# Root centralizers in the original Thompson subgroup

The absorbed elementary pair makes R nilpotent of class two, with center
inside the core Q. The original natural-action coordinates show that every
element of R outside Q has centralizer Z(R) on Q. In the centerless case,
the known orders |R|=|Z(R)|³ and |Q|=|Z(R)|² give the literal root quotient
order |R/Q|=2^n. These are the marked inputs to the fixed-root calculation.

Source: Aschbacher–Smith, 2.4.8(3),(7) and 2.4.12(2), printed pp.529–532.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_thompson_root_geometry
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Q := twoCore d.H
    let Z := R ⊓ centralizer (R : Set G)
    Q ≤ R ∧ Z ≤ Q ∧ ⁅R,R⁆ ≤ Z ∧
      ∀ r ∈ R, r ∉ Q → Q ⊓ centralizer ({r} : Set G) = Z := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Q := twoCore d.H
  let U := sourceModule L
  let Z := R ⊓ centralizer (R : Set G)
  have hUQ : U = Q := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  have hQR : Q ≤ R := le_sSup (d.core_source hG T hST).2.2
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hgen : U ⊔ V = R :=
    ((source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS).1.symm
  have hZ : U ⊓ V = Z := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hZQ : Z ≤ Q := hZ.ge.trans (inf_le_left.trans_eq hUQ)
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  let : IsElementaryAbelian 2 U := hUQ.symm ▸ (d.core_source hG T hST).2.2.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hRU : R ≤ normalizer (U : Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hRa : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (ht.2.2 (T.inv_mem hxT))
  have hRV : R ≤ normalizer (V : Set G) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hRU).trans
      (U.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
    rwa [hRa] at hh
  have hder : ⁅R,R⁆ ≤ Z := by
    rw [←hZ]
    apply le_inf
    · rw [←hgen]
      exact commutator_sup_le_of_normalized_derived U V (hVR.trans hRU)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)
    · rw [←hgen,sup_comm U V]
      exact commutator_sup_le_of_normalized_derived V U (hUR.trans hRV)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)
  refine ⟨hQR,hZQ,hder,?_⟩
  intro r hr hrQ
  apply le_antisymm
  · obtain ⟨c,F,hF,h,hint,y,hy,hnc⟩ := d.single_natural_configuration hG T hST.le hsingle hK
      (T : Subgroup G) hST.le le_rfl ht.1
    have hh := ChapterC.Section06.rankOne_family_from_original c h ht.1 y hy hnc
    have hSR : RankOne.S S = R := hh.2.1
    have hQU : RankOne.Q S L = U := hh.1.trans hUQ.symm
    have hrS : r ∈ RankOne.S S := hSR.symm ▸ hr
    have hrc : r ∉ centralizer (U : Set G) := by
      intro he
      have hrQ' : r ∈ RankOne.Q S L := h.core.symm ▸ ⟨hrS,he⟩
      exact hrQ (hUQ.le (hQU ▸ hrQ'))
    rintro u ⟨hu,huc⟩
    have huU : u ∈ U := hUQ.symm ▸ hu
    have hfix : RankOne.moduleConjugate h.coordinates.normalizes ⟨r,hrS⟩ ⟨u,huU⟩ = ⟨u,huU⟩ := by
      apply Subtype.ext
      change r*u*r⁻¹=u
      rw [←mem_centralizer_singleton_iff.mp huc,mul_inv_cancel_right]
    have huC : u ∈ centralizer (R : Set G) := by
      rw [←hSR]
      exact h.fixed_by_noncentral_imp_fixed_by_all ⟨r,hrS⟩ hrc ⟨u,huU⟩ hfix
    exact ⟨hQR hu,huC⟩
  · exact le_inf hZQ (fun z hz => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hz.2 r hr).symm)
theorem source_centerless_root_quotient_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hcenter : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    Nat.card (R ⧸ N) = 2^n := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let N := Q.subgroupOf R
  let : N.Normal := source_field_core_normal d
  let Z := R ⊓ centralizer (R : Set G)
  have hQR : Q ≤ R := le_sSup (d.core_source hG T hST).2.2
  have hZcard : Nat.card Z = 2^n :=
    (source_centerless_torus_regular d hG T hST hsingle hL hM hTM hunique hcenter c.torus
      (c.torus_le.trans inf_le_right) (Odd.of_dvd_nat c.hall_odd (card_dvd_of_le c.torus_le_hall))
      c.torus_card (c.torus_le_hall.trans c.hall_normalizes)).1
  have hQcard : Nat.card Q = Nat.card Z^2 := by
    change Nat.card (twoCore d.H) = Nat.card Z^2
    rw [←(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact source_centerless_elementary_pair_card d hG T hST hsingle hL hM hTM hunique hcenter
  have hNcard : Nat.card N = Nat.card Z^2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv,hQcard]
  have hRcard : Nat.card R = Nat.card Z^3 :=
    source_centerless_sylow_card d hG T hST hsingle hL hM hTM hunique hcenter
  have hc := card_eq_card_quotient_mul_card_subgroup N
  change Nat.card R = Nat.card (R ⧸ N) * Nat.card N at hc
  rw [hRcard,hNcard] at hc
  change Nat.card (R ⧸ N) = 2^n
  rw [←hZcard]
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α:=Z)) 2)
  calc
    Nat.card (R ⧸ N) * Nat.card Z^2 = Nat.card Z^3 := hc.symm
    _ = Nat.card Z * Nat.card Z^2 := by ring


end CFSG.Quasithin.Chapter2.LinearShadows.Single
