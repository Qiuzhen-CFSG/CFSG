module
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max4Image
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Action
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.Certification
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Theory.SpecificGroups.SymmetricFive.NoForty

/-!
# Two-core sections and quintic actors in Rudvalis

The two actual Sylow-overgroup quotient maps have targets GL₃(2) and S₅
and two-group kernels. Thus their subgroup sections modulo their intrinsic
two-cores have order dividing 840. A three-free full-Sylow overgroup cannot
contain five: in the S₅ quotient its image would have order forty.

The native automorphism realization makes a quintic actor on a normal
Rudvalis factor inner. The actor-Sylow order bound then contradicts the
same three-free overgroup restriction. The cover premise is discharged by
the existing two-core and radical-normalizer calculations in ChapterF's
literal source application. Existing order and primitivity certificates
supply simplicity only where required for automorphism realization.

Source: Aschbacher–Smith A.3.12(20) and5.2.2, pp.47–48 and648–649.
The imported ATLAS RuG1 carriers, word conventions, attribution and license
are unchanged; no new finite enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Rudvalis.SylowOvergroups

private theorem section_card_dvd {A Y : Type*} [Group A] [Finite A] [Group Y] [Finite Y]
    (f : A →* Y) (hk : IsPGroup 2 f.ker) (B : Subgroup A) :
    Nat.card (B ⧸ pCore 2 B) ∣ Nat.card Y := by
  have hkb : IsPGroup 2 (f.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  rw [Nat.card_congr ((f.subgroupMap B).pCoreQuotientEquiv
    (f.subgroupMap_surjective B) hkb).toEquiv]
  exact (card_quotient_dvd_card _).trans (B.map f).card_subgroup_dvd_card

/-- Every section in a proper full-Sylow overgroup has two-core quotient
order dividing 840, using the actual two native quotient maps. -/
theorem proper_overgroup_section_order (hcover : OddIndexMaximalCover)
    (S : Sylow 2 Model) (J B : Subgroup Model)
    (hSJ : (S : Subgroup Model) ≤ J) (hJ : J ≠ ⊤) (hBJ : B ≤ J) :
    Nat.card (B ⧸ pCore 2 B) ∣ 840 := by
  obtain ⟨M,hM,hJM⟩ := (eq_top_or_exists_le_coatom J).resolve_left hJ
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (hSJ.trans hJM)))
  let a := subgroupOfEquivOfLe (hBJ.trans hJM)
  let aQ := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  rw [←Nat.card_congr aQ.toEquiv]
  rcases hcover M hM hodd with he | he
  · obtain ⟨e⟩ := he
    let C := (B.subgroupOf M).map e.toMonoidHom
    let b := e.subgroupMap (B.subgroupOf M)
    let bQ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
    rw [Nat.card_congr bQ.toEquiv]
    have hd := section_card_dvd CoreQuotients.max4LinearAction
      (by rw [CoreQuotients.max4LinearAction_ker_eq_pCore]; exact pCore_isPGroup) C
    rw [Matrix.PSL3Two.card_PSL] at hd
    exact hd.trans (by decide)
  · obtain ⟨e⟩ := he
    let C := (B.subgroupOf M).map e.toMonoidHom
    let b := e.subgroupMap (B.subgroupOf M)
    let bQ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
    rw [Nat.card_congr bQ.toEquiv]
    apply (section_card_dvd CoreQuotients.max6FiveAction
      (by rw [CoreQuotients.max6FiveAction_ker]; exact pCore_isPGroup) C).trans
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

private theorem five_image {A Y : Type*} [Group A] [Finite A] [Group Y] [Finite Y]
    (f : A →* Y) (hk : IsPGroup 2 f.ker) (B : Subgroup A)
    (h5 : 5 ∣ Nat.card B) : 5 ∣ Nat.card (B.map f) := by
  let g := f.comp B.subtype
  have hkg : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.ker.subgroupOf B)
    exact hk.comap_subtype
  obtain ⟨a,ha⟩ := hkg.exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card g.ker) := by
    rw [ha]
    exact (by decide : Nat.Coprime 5 2).pow_right a
  have he := g.ker.card_mul_index
  rw [index_ker] at he
  rw [←he] at h5
  have hi := hcop.dvd_of_dvd_mul_left h5
  simpa only [g,MonoidHom.range_comp,range_subtype] using hi

/-- A three-free full-Sylow overgroup has no factor five. -/
theorem not_five_of_three_free (hcover : OddIndexMaximalCover)
    (S : Sylow 2 Model) (J : Subgroup Model)
    (hSJ : (S : Subgroup Model) ≤ J) (h3 : ¬ 3 ∣ Nat.card J) :
    ¬ 5 ∣ Nat.card J := by
  have hJ : J ≠ ⊤ := by
    intro he
    apply h3
    rw [he,card_top,model_card]
    decide
  obtain ⟨M,hM,hJM⟩ := (eq_top_or_exists_le_coatom J).resolve_left hJ
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (hSJ.trans hJM)))
  intro h5
  rcases hcover M hM hodd with he | he
  · obtain ⟨e⟩ := he
    let B := (J.subgroupOf M).map e.toMonoidHom
    have hB : Nat.card B = Nat.card J :=
      (card_map_of_injective e.injective).trans
        (Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv)
    have hd := (five_image CoreQuotients.max4LinearAction
      (by rw [CoreQuotients.max4LinearAction_ker_eq_pCore]; exact pCore_isPGroup)
      B (hB ▸ h5)).trans (B.map CoreQuotients.max4LinearAction).card_subgroup_dvd_card
    rw [Matrix.PSL3Two.card_PSL] at hd
    norm_num at hd
  · obtain ⟨e⟩ := he
    let B := (J.subgroupOf M).map e.toMonoidHom
    have hB : Nat.card B = Nat.card J :=
      (card_map_of_injective e.injective).trans
        (Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv)
    let f := CoreQuotients.max6FiveAction
    have hk : IsPGroup 2 f.ker := by
      rw [CoreQuotients.max6FiveAction_ker]
      exact pCore_isPGroup
    let P := ((S.subtype (hSJ.trans hJM)).mapSurjective (f := e.toMonoidHom) e.surjective).mapSurjective
      CoreQuotients.max6FiveAction_surjective
    have hPB : (P : Subgroup (Equiv.Perm (Fin 5))) ≤ B.map f :=
      map_mono (map_mono (comap_mono hSJ))
    have h8 : 8 ∣ Nat.card (B.map f) := by
      have hp : Nat.card P = 8 := by
        rw [P.card_eq_multiplicity,Nat.card_eq_fintype_card,Fintype.card_perm]
        decide +kernel
      exact hp ▸ card_dvd_of_le hPB
    have hd : Nat.card (B.map f) ∣ 120 := by
      convert (B.map f).card_subgroup_dvd_card using 1
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    have h3b : ¬ 3 ∣ Nat.card (B.map f) := fun hh =>
      h3 (hB ▸ hh.trans (B.card_map_dvd f))
    have h5b := five_image f hk B (hB ▸ h5)
    have hcases : ∀ m ∈ (120 : ℕ).divisors,
        8 ∣ m → ¬ 3 ∣ m → 5 ∣ m → m = 40 := by decide +kernel
    exact _root_.SymmetricFive.subgroup_card_ne_forty _
      (hcases _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩) h8 h3b h5b)

/-- The original actor-Sylow order bound excludes a faithful quintic actor
on a normal Rudvalis factor. -/
theorem no_five_actor (hcover : OddIndexMaximalCover)
    {G : Type*} [Group G] [Finite G]
    (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (e : K ≃* Model) (hE : Nat.card E = 5)
    (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  have hzK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center Model at hh
    rw [LowCentralizers.model_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let := model_isPreprimitive
  let : IsSimpleGroup Model := simple_of_card_of_primitive model_card
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hzK
    (outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  have h3 : ¬3 ∣ Nat.card J := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right (by decide)).of_dvd_right hJ)
  have hh := not_five_of_three_free hcover (P.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono hPJ) (by rwa [card_map_of_injective e.injective])
  rwa [card_map_of_injective e.injective] at hh
end Rudvalis.SylowOvergroups
