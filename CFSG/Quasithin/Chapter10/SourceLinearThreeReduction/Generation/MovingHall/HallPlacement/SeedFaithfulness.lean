module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SeedAction

/-!
# Seed faithfulness and the common local overgroup before Hall placement

Restrict the actual quotient-faithful Hall action to its seed centralizer.
Both component actions are inner by `SeedAction`; component-prime
coprimality lifts that subgroup to L₀. The original natural coordinates
then detect every nonidentity odd element, so the Hall seed centralizer is
trivial. H-star minimality identifies C_H(Ω₁Z(T)) with the prescribed Sylow.
The genuine natural H-star rows now construct a common maximal two-local
overgroup of H and the full Baumann normalizer.

These are the earlier inputs to the Borel-normalization argument, proved
without original Hall placement. Final Hall placement and source assembly
remain with the moving-Hall owner.
Source: Aschbacher–Smith 10.2.2(4), 10.2.3, printed pp.744–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]

open CentralHall Chapter4
private theorem quotient_action_kernel_le_section
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (normalizerQuotientAction (localOrbit T L) (pCore 2 (localOrbit T L))).ker.map
      D.maximalLocal.subtype ≤ sectionCentralizer (localOrbit T L) := by
  let K := (normalizerQuotientAction (localOrbit T L) (pCore 2 (localOrbit T L))).ker
  have hKM : K ≤ D.maximalLocal.subgroupOf D.maximalLocal := fun x _ => x.property
  have hk : (action D K hKM).ker = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact x.property
  have hh := action_kernel_image_le D K hKM
  rw [hk,←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype] at hh
  exact hh

/-- Innerness on the original product quotient places any subgroup of the faithful Hall in L₀. -/
theorem subgroup_le_orbit_of_inner
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (A : Subgroup H) (hAB : A ≤ B)
    {J : Type*} [Group J]
    (e : (L ⧸ pCore 2 L) ≃* J)
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (J × J))
    (hinner : ∀ b : A, action D A (hAB.trans c.hall_le) b ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L))) :
    A.map H.subtype ≤ localOrbit T L := by
  have ho : Odd (Nat.card A) := c.hall_odd.of_dvd_nat (card_dvd_of_le hAB)
  have hfaith : A.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (map_mono hAB)).trans c.faithful.le)
  let R := localOrbit T L
  let Q := R ⧸ pCore 2 R
  let C := A.map H.subtype
  let f := (action D A (hAB.trans c.hall_le)).codRestrict (MulAut.innerSubgroup Q) hinner
  have hfi : Function.Injective f := fun _ _ h =>
    action_injective D A (hAB.trans c.hall_le) hfaith (congrArg Subtype.val h)
  have hcard : Nat.card A ∣ Nat.card Q :=
    (card_dvd_of_injective f hfi).trans (card_range_dvd (MulAut.conj : Q →* MulAut Q))
  have hCM : C ≤ D.maximalLocal := map_le_iff_le_comap.mpr (hAB.trans c.hall_le)
  have hc : Nat.Coprime (Nat.card C) (Nat.card (sectionCentralizer R)) := by
    rw [show Nat.card C = Nat.card A from card_map_of_injective H.subtype_injective]
    apply Nat.coprime_of_dvd
    intro p hp hpB hpC
    let : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact (Nat.not_even_iff_odd.mpr (ho)) (even_iff_two_dvd.mpr hpB)
    have hL : p ∣ Nat.card (L ⧸ pCore 2 L) := by
      have hd := hpB.trans hcard
      rw [Nat.card_congr q.toEquiv,Nat.card_prod] at hd
      rw [Nat.card_congr e.toEquiv]
      exact (hp.dvd_mul.mp hd).elim id id
    exact hp.coprime_iff_not_dvd.mp
      (source_nonnormal_sectionCentralizer_prime_coprime D c.nonnormal p hp2 hL) hpC
  have hkcard : Nat.card (normalizerQuotientAction R (pCore 2 R)).ker ∣
      Nat.card (sectionCentralizer R) := by
    rw [←card_map_of_injective (normalizer (R : Set G)).subtype_injective]
    exact card_dvd_of_le (quotient_action_kernel_le_section D)
  apply le_of_normalizerQuotientAction_inner R (pCore 2 R) C hCM
    (hc.coprime_dvd_right hkcard)
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨b,hb,hba⟩ := ha
  have he : a = (⟨b,c.hall_le (hAB hb)⟩ : D.maximalLocal) := Subtype.ext hba.symm
  rw [he]
  exact hinner ⟨b,hb⟩

/-- The original Hall seed centralizer is trivial before Hall placement.
Only the original quotient-faithfulness hypothesis is used. -/
theorem hall_seed_centralizer_eq_bot
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    B.map H.subtype ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ := by
  let A : Subgroup H := B ⊓ (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).comap H.subtype
  have hAB : A ≤ B := inf_le_left
  have hi (b : A) : action D A (hAB.trans c.hall_le) b ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L)) := by
    exact odd_pair_inner_of_seed_centralizer D degree hdegree hF e c.nonnormal mark
      (b:G) (c.hall_le b.property.1)
      (hall_normalizes_component D c (mem_map_of_mem H.subtype b.property.1))
      b.property.2 (by
        have ho := (c.hall_odd.of_dvd_nat (card_dvd_of_le hAB)).of_dvd_nat (orderOf_dvd_natCard b)
        rwa [←orderOf_injective (H.subtype.comp A.subtype)
          (H.subtype_injective.comp A.subtype_injective) b] at ho)
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  obtain ⟨q,_,_⟩ := source_original_natural_pair_quotient D degree hdegree hF e c.nonnormal ht htn
  have hAR := subgroup_le_orbit_of_inner D c A hAB e q hi
  apply le_bot_iff.mp
  rintro b ⟨hb,hbZ⟩
  by_contra hne
  obtain ⟨a,ha,rfl⟩ := hb
  have haA : a ∈ A := ⟨ha,hbZ⟩
  let bR : localOrbit T L := ⟨a,hAR (mem_map_of_mem H.subtype haA)⟩
  have hp : bR ^ Nat.card B = 1 := by
    apply Subtype.ext
    exact congrArg (H.subtype.comp B.subtype) (pow_card_eq_one' (x := (⟨a,ha⟩ : B)))
  exact source_natural_odd_not_centralizes_omegaCenter D degree hdegree hF e c.nonnormal mark
    bR (Nat.card B) c.hall_odd hp (fun he => hne (congrArg Subtype.val he)) hbZ

/-- The genuine natural H-star rows are available before original Hall placement. -/
theorem seed_centralizer_eq_sylow
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype c.hstar.1.1.2 : Subgroup H) :=
  Chapter3.HStar.omega_center_centralizer_eq_sylow_of_hall c.hstar c.moving B
    c.hall_le c.hall (hall_seed_centralizer_eq_bot D c degree hdegree hF e mark)

/-- Source 10.2.2(4) in the original moving natural row, without Hall placement
or an assumed seed-centralizer identity. -/
theorem common_local_overgroup
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e) :
    ∃ M₁ : Subgroup G, IsMaximalTwoLocal M₁ ∧
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ⊔ H ≤ M₁ :=
  c.hstar_baumann_normalizer_common_overgroup D degree hdegree hF e
    (seed_centralizer_eq_sylow D c degree hdegree hF e mark)

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
