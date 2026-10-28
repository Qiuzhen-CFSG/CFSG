module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SolvableContaining
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions
public import Theory.GroupTheory.ComponentLocalPrimeFree

/-!
# Full-Sylow containing-component tests

If a containing component contains the whole original orbit, both exchanged
factors are C-components of the same subgroup containing its full Sylow
subgroup. Uniqueness there contradicts the actual exchanger. Solvable-kernel
lifting makes this a test on the literal two-core quotient.

A second test forces three to divide the original quotient whenever every
three-free full-Sylow overgroup in the containing quotient is solvable.
The source intersection normalizer ensures that adjoining the full Sylow
introduces no factor of three, while the original local component stays
nonsolvable after removing the containing two-core.

BinaryLinearContaining applies both tests without extra callbacks; the
remaining source branches and assembly belong to
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the independent input of
qt-d-10-nona5-point-selection, discharged finally by
qt-d-10-nona5-point-control.
Source: Aschbacher--Smith A.3.12 and 10.2.6, printed pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Both exchanged factors cannot lie in a group with unique full-Sylow local components. -/
theorem ContainingPair.not_orbit_le_of_sylow_component_unique
    (C : ContainingPair D H t K₁ K₂) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H) (hu : SylowOvergroupComponentUnique K) :
    ¬ localOrbit T L ≤ K := by
  intro hOK
  let O := localOrbit T L
  have hLO : L ≤ O := le_componentOrbit L T
  have hLK : L ≤ K := hLO.trans hOK
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  have hLK' : L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K := by
    simpa only [hid,Subgroup.map_id] using hLK
  obtain ⟨S,hS,_⟩ := C.local_sylow_in_containing (one_mem _) hK hLK'
  let P := O ⊔ (S : Subgroup K).map K.subtype
  have hPK : P ≤ K := sup_le hOK (map_subtype_le _)
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    rw [hS,subgroupOf_map_subtype]
    exact inf_le_left.trans inf_le_left
  have hON : (O.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show O ≤ P from le_sup_left)).mpr
      (sup_le O.le_normalizer (hST.trans (le_normalizer_componentOrbit L T)))
  let e : O ≃* O.subgroupOf P := (subgroupOfEquivOfLe (show O ≤ P from le_sup_left)).symm
  let f : O →* P := (O.subgroupOf P).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := (O.subgroupOf P).subtype_injective.comp e.injective
  have hOt : O.map (MulAut.conj t).toMonoidHom = O :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T C.t_mem)
  let τ : MulAut O := ((MulAut.conj t).subgroupMap O).trans (MulEquiv.subgroupCongr hOt)
  let A := L.subgroupOf O
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent := D.maximal.1.1.subgroupOf_of_le hLO (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hAf : (A.map f).IsCComponent := by
    simpa only [map_map] using (hA.map_equiv e).map_subtype hON.isSubnormal
  have hBf : (B.map f).IsCComponent := by
    simpa only [map_map] using (hB.map_equiv e).map_subtype hON.isSubnormal
  let j : P ≃* P.subgroupOf K := (subgroupOfEquivOfLe hPK).symm
  have hSP : (S : Subgroup K) ≤ P.subgroupOf K := by
    intro x hx
    exact (show (S : Subgroup K).map K.subtype ≤ P from le_sup_right) (mem_map_of_mem K.subtype hx)
  have he : A.map f = B.map f := map_injective j.injective
    (hu S (P.subgroupOf K) hSP _ _ (hAf.map_equiv j) (hBf.map_equiv j))
  have hab : A = B := map_injective hf he
  have hmA : A.map O.subtype = L := map_subgroupOf_eq_of_le hLO
  have hmB : B.map O.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show O.subtype.comp τ.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp O.subtype from rfl,←map_map,hmA]
  exact C.t_not_normalizes (mem_normalizer_iff_map_conj_eq.mpr
    (hmB.symm.trans ((congrArg (map O.subtype) hab).symm.trans hmA)))

/-- Uniqueness in the first literal quotient forces distinct containing components. -/
theorem ContainingPair.distinct_of_first_sylow_unique_quotient
    (C : ContainingPair D H t K₁ K₂) {X : Type*} [Group X] [Finite X]
    (d : (K₁ ⧸ pCore 2 K₁) ≃* X) (hu : SylowOvergroupComponentUnique X) : K₁ ≠ K₂ := by
  intro he
  let : Group.IsNilpotent (pCore 2 K₁) := pCore_isNilpotent
  have hu₁ : SylowOvergroupComponentUnique K₁ :=
    .of_quotient (pCore 2 K₁) (.of_equiv d hu)
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  have hum : SylowOvergroupComponentUnique (K₁.map H.subtype) := .of_equiv a hu₁
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hK : K₁.map H.subtype ∈ cComponentsIn H :=
    ⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩
  apply C.not_orbit_le_of_sylow_component_unique hK hum
  rw [C.orbit_eq]
  apply sup_le
  · simpa only [map_subgroupOf_eq_of_le C.left_le] using map_mono (f := H.subtype) C.first_le
  · have hh := map_mono (f := H.subtype) C.second_le
    rwa [map_subgroupOf_eq_of_le C.right_le,←he] at hh

/-- The corresponding second-factor conclusion uses the same source exchanger. -/
theorem ContainingPair.distinct_of_second_sylow_unique_quotient
    (C : ContainingPair D H t K₁ K₂) {X : Type*} [Group X] [Finite X]
    (d : (K₂ ⧸ pCore 2 K₂) ≃* X) (hu : SylowOvergroupComponentUnique X) : K₁ ≠ K₂ := by
  intro he
  subst K₂
  exact C.distinct_of_first_sylow_unique_quotient d hu rfl

/-- Solvability of three-free Sylow overgroups forces a cubic divisor in the original quotient. -/
theorem ContainingPair.three_dvd_of_solvable_three_free_sylow_overgroups
    (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {X : Type*} [Group X] [Finite X] (d : (K ⧸ pCore 2 K) ≃* X)
    (hfree : ∀ (S : Sylow 2 X) (P : Subgroup X), (S : Subgroup X) ≤ P →
      ¬ 3 ∣ Nat.card P → Group.IsSolvable P) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨S,hS,hl⟩ := C.local_sylow_in_containing hs hK hBK
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let b : L ≃* B := ((MulAut.conj s).subgroupMap L).trans (subgroupOfEquivOfLe hBK).symm
  have hSN : (S : Subgroup K) ≤ normalizer (B : Set K) := by
    rw [←subgroupOf_normalizer_eq hBK,hS]
    intro x hx
    exact C.intersection_normalizes_conjugate_of_sylow hn hs
      ⟨hK.1 x.property,(le_normalizer_componentOrbit L T) hx.1⟩
  let q := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hk.symm ▸ pCore_isNilpotent
  let S' := S.mapSurjective hq
  let A := B.map q
  have hA : A ∈ localCComponents S' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hnA : (S' : Subgroup X) ≤ normalizer (A : Set X) :=
    (map_mono hSN).trans (le_normalizer_map q)
  have hdA : 3 ∣ Nat.card A := by
    by_contra h3
    have hS3 : ¬ 3 ∣ Nat.card S' := by
      obtain ⟨n,he⟩ := S'.isPGroup'.exists_card_eq
      rw [he]
      exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
    let hp := hfree S' (A ⊔ (S' : Subgroup X)) le_sup_right
      (not_dvd_card_sup_of_normalizes Nat.prime_three A S' hnA h3 hS3)
    let : Group.IsSolvable ↥(A ⊔ (S' : Subgroup X)) := hp
    exact hA.not_isSolvable inferInstance
  have hdB : 3 ∣ Nat.card B := hdA.trans
    (card_dvd_of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B))
  have hdL : 3 ∣ Nat.card L := (Nat.card_congr b.toEquiv).symm ▸ hdB
  by_contra hd
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup] at hz
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz hdL

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
