module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FieldKernel
public import Theory.GroupTheory.TwoOrbitOddPrime.BinaryIndex
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Splitting the original Hall coefficient action

For every odd prime in the actual binary component order, the ambient
rank-two bound and the paired semilinear calculation make M/L₀ p-prime.
The exact kernel identification ker(φ) = B_H ∩ L₀ transfers this to the
coefficient image. Its order is therefore coprime to the component order.
The kernel embeds in two field-unit groups, so Schur--Zassenhaus supplies
an actual complement inside B_H. Its restriction to the coefficient image
is bijective. The final theorem retains the original component inclusion,
Sylow marking, kernel characters, and diagonal-plus-field action together.

This discharges the splitting step in the binary-linear cases of 10.2.3.
Field-factor elimination using Ω₁Z(T), the nonlinear module recognition,
and the three module-row calculations remain with
qt-d-10-nona5-central-hall-orders. No module-row conclusion is asserted here.
Source: Aschbacher--Smith 1.2.2(a),10.1.3,10.2.3, printed pp.504,742,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Chapter1.Section02 Matrix.SpecialLinearGroup BenderSuzuki.ZD.Linear
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
private theorem source_local_sqtk (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1


variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- Odd primes in the actual binary component quotient do not occur above
its original two-component orbit in M. -/
theorem hall_component_orbit_index_coprime
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime p ((localOrbit T L).subgroupOf D.maximalLocal).index := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hlocal := source_local_sqtk D
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin r hr ho)
  have hnot : ¬ A.Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨hi,_⟩ := (proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let a : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM) (pCore_map_iso 2 _)
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv a.symm
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tM : M := ⟨t,hTM ht⟩
  have htnM : tM ∉ normalizer (A : Set M) := by
    rw [←subgroupOf_normalizer_eq hLM]
    exact htn
  have hmap : (A ⊔ A.conjBy tM).map M.subtype = localOrbit T L := by
    rw [Subgroup.map_sup]
    change A.map M.subtype ⊔ (A.map (MulAut.conj tM).toMonoidHom).map M.subtype = _
    rw [map_map,show M.subtype.comp (MulAut.conj tM).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp M.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLM,←hpair]
  have he : A ⊔ A.conjBy tM = (localOrbit T L).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hmap,map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer]
  rw [←he]
  refine TwoOrbitOddPrime.binary_cComponent_pair_index_coprime p hp
    D.component_in_maximalLocal hi tM htnM ?_ ?_
    (hlocal.stronglyQuasithin p Fact.out ((Fact.out : p.Prime).odd_of_ne_two hp)) F
    ((a.trans e).trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)))
  · apply eq_bot_iff.mpr
    intro x hx
    have hz : a x ∈ center (L ⧸ pCore 2 L) := (centerCongr a ⟨x,hx⟩).property
    rw [source_nonnormal_component_core_center D hn,mem_bot] at hz
    exact a.map_eq_one_iff.mp hz
  · rwa [Nat.card_congr a.toEquiv]

/-- The original field-action image has order coprime to the component order. -/
theorem hall_field_image_coprime
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (φ : B →* ((F ≃+* F) × (F ≃+* F)))
    (hk : φ.ker = (localOrbit T L).comap (H.subtype.comp B.subtype)) :
    Nat.Coprime (Nat.card φ.range) (Nat.card (L ⧸ pCore 2 L)) := by
  let R := (localOrbit T L).subgroupOf D.maximalLocal
  let : R.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let f : B →* D.maximalLocal := (H.subtype.comp B.subtype).codRestrict
    D.maximalLocal (fun b => c.hall_le b.property)
  have hindex : Nat.card φ.range ∣ R.index := by
    rw [←index_ker φ,hk]
    change (R.comap f).index ∣ R.index
    rw [index_comap]
    exact R.relIndex_dvd_index_of_normal f.range
  have ho : Odd (Nat.card φ.range) := (hall_odd D c).of_dvd_nat (card_range_dvd φ)
  apply Nat.coprime_of_dvd
  intro p hp hφ hL
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hφ)
  exact hp.coprime_iff_not_dvd.mp
    (hall_component_orbit_index_coprime D c.nonnormal e p hp2 hL) (hφ.trans hindex)

/-- The actual field kernel has a complement inside the original Hall carrier;
the complement maps bijectively to the coefficient-action image. -/
theorem exists_hall_field_complement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (φ : B →* ((F ≃+* F) × (F ≃+* F)))
    (hk : φ.ker = (localOrbit T L).comap (H.subtype.comp B.subtype))
    (χ : φ.ker →* Fˣ × Fˣ) (hχ : Function.Injective χ) :
    ∃ E : Subgroup B, φ.ker.IsComplement' E ∧
      Function.Bijective (φ.rangeRestrict.comp E.subtype) ∧
      Nat.Coprime (Nat.card E) (Nat.card (L ⧸ pCore 2 L)) := by
  let : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hc := hall_field_image_coprime D c e φ hk
  have hunit : Nat.card Fˣ ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv]
    exact card_dvd_of_injective (splitDiagonalHom (F := F)) splitDiagonalHom_injective
  have hker : Nat.card φ.ker ∣ Nat.card Fˣ * Nat.card Fˣ := by
    simpa only [Nat.card_prod] using card_dvd_of_injective χ hχ
  have hcop : Nat.Coprime (Nat.card φ.ker) φ.ker.index := by
    rw [index_ker]
    exact ((hc.coprime_dvd_right hunit).mul_right (hc.coprime_dvd_right hunit)).symm.coprime_dvd_left hker
  obtain ⟨E,hE⟩ := exists_right_complement'_of_coprime hcop
  have hcard : Nat.card E = Nat.card φ.range := hE.card_right.trans (index_ker φ)
  have hinj : Function.Injective (φ.rangeRestrict.comp E.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    have hh : (x : B) ∈ φ.ker ⊓ E := ⟨congrArg Subtype.val hx,x.property⟩
    exact mem_bot.mp (hE.isCompl.inf_eq_bot ▸ hh)
  exact ⟨E,hE,(Nat.bijective_iff_injective_and_card _).mpr ⟨hinj,hcard⟩,hcard ▸ hc⟩
/-- The original simultaneous marking admits an actual coefficient complement,
with no additional action, coprimality, or splitting premise. -/
theorem exists_hall_split_field_coordinates
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,F))
      (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
      (φ : B →* ((F ≃+* F) × (F ≃+* F)))
      (χ : φ.ker →* Fˣ × Fˣ) (E : Subgroup B),
      (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
          (upperUnipotent F).prod (upperUnipotent F) ∧
      φ.ker = (localOrbit T L).comap (H.subtype.comp B.subtype) ∧
      Function.Injective χ ∧
      Monoid.exponent φ.ker ∣ Nat.card F - 1 ∧
      φ.ker.IsComplement' E ∧
      Function.Bijective (φ.rangeRestrict.comp E.subtype) ∧
      Nat.Coprime (Nat.card E) (Nat.card (L ⧸ pCore 2 L)) ∧
      ∀ b : B, ∃ d : Fˣ × Fˣ,
        MulAut.congr q (action D B c.hall_le b) =
          (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
            (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2) := by
  obtain ⟨e',q,φ,χ,hcomp,hS,_ho,hk,hχ,hexp,_hact,hd⟩ :=
    exists_hall_field_kernel_coordinates D c e
  obtain ⟨E,hE,hbij,hcop⟩ := exists_hall_field_complement D c e' φ hk χ hχ
  refine ⟨e',q,φ,χ,E,hcomp,hS,hk,hχ,hexp,hE,hbij,hcop,?_⟩
  simpa only [splitDiagonalHom_apply] using hd

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
