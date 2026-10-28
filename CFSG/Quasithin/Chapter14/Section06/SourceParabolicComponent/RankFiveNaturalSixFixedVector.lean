module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixSpans
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointResidualRestriction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing

/-!
# The fixed vector in the original second-parabolic span

The second parabolic has the full point-stabilizer image in the same six-letter
action: it contains the original Sylow subgroup, and its symmetric-three
quotient makes the image nonbinary. Thus its plane span contains the full
point-centralizer hyperplane and the all-ones vector. The latter centralizes
the entire source group. Every nonidentity vector fixed by the component has
this same constant coordinate.

Source: Aschbacher–Smith, 14.6.10(5), printed pp.1029–1030.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry Representation.BinaryOffender

theorem point_image_eq_of_sylow (F P Q : Subgroup S)
    (hF : alternatingGroup (Fin 6) ≤ F) (hSyl : Chapter1.IsSylowIn 2 Q F)
    (hQP : Q ≤ P) (hP : P ≤ F ⊓ H1) (hp : ¬ IsPGroup 2 P) :
    P = F ⊓ H1 := by
  let J := F ⊓ H1
  obtain ⟨R,hR⟩ := hSyl.restrict (hQP.trans hP) inf_le_left
  have hr : R.index = 3 := by
    have hh := point_sylow_index_three F hF canonicalLine canonicalLine_finrank
    rw [show subspaceStabilizer (naturalRepresentation (Fin 6)) canonicalLine = H1 from
      flagStabilizer_line] at hh
    exact hh R
  have hRP : (R : Subgroup J) ≤ P.subgroupOf J := by
    intro r hr
    exact hQP (hR ▸ mem_map_of_mem J.subtype hr)
  rcases (isCoatom_of_index_three (R : Subgroup J) hr).le_iff.mp hRP with he | he
  · have hh := congrArg (Subgroup.map J.subtype) he
    rw [map_subgroupOf_eq_of_le (show P ≤ J from hP)] at hh
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  · exfalso
    apply hp
    have hh := R.isPGroup'.map J.subtype
    rw [hR] at hh
    have hPQ : P = Q := by
      have he' := congrArg (Subgroup.map J.subtype) he
      rw [map_subgroupOf_eq_of_le (show P ≤ J from hP),hR] at he'
      exact he'
    exact hPQ ▸ hh

variable {G : Type*} [Group G] [Finite G]

theorem source_second_parabolic_image
    (I K S0 I2 : Subgroup G) (hIK : I ≤ normalizer (K : Set G))
    (hI2 : I2 ≤ I) (hSI2 : S0 ≤ I2)
    (hSyl : Chapter1.IsSylowIn 2 S0 I)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* S)
    (he : ∀ (n : normalizer (K : Set G)) (u : sourceModule K)
      (hu : n.val*u.val*n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*u.val*n.val⁻¹,hu⟩).toAdd = coreRepresentation (Fin 6) (f n) (E u).toAdd)
    (hk : (restrictedActor I K hIK f).ker = pCore 2 I)
    (hA : alternatingGroup (Fin 6) ≤ (restrictedActor I K hIK f).range)
    (hquot : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (z : sourceModule K) (hz : (E z).toAdd = CoreCrossing.z)
    (hIz : I2 ≤ centralizer ({z.val} : Set G)) :
    (I2.subgroupOf I).map (restrictedActor I K hIK f) =
      (restrictedActor I K hIK f).range ⊓ H1 := by
  let a := restrictedActor I K hIK f
  let P := (I2.subgroupOf I).map a
  have hP : P ≤ a.range ⊓ H1 := by
    refine le_inf (map_le_range _ _) ?_
    rintro _ ⟨i,hi,rfl⟩
    apply (CoreCrossing.fixes_z_iff _).mp
    have hc : i.val*z.val*i.val⁻¹ = z.val := by
      have hh : i.val*z.val = z.val*i.val := mem_centralizer_singleton_iff.mp (hIz hi)
      rw [hh,mul_inv_cancel_right]
    have hw : i.val*z.val*i.val⁻¹ ∈ sourceModule K := hc.symm ▸ z.property
    have hh := he (inclusion hIK i) z hw
    change (E ⟨i.val*z.val*i.val⁻¹,hw⟩).toAdd = coreRepresentation (Fin 6) (a i) (E z).toAdd at hh
    have hze : (⟨i.val*z.val*i.val⁻¹,hw⟩ : sourceModule K) = z := Subtype.ext hc
    rw [hze,hz] at hh
    exact hh.symm
  have hnp : ¬ IsPGroup 2 P := by
    intro hp
    have hker : IsPGroup 2 a.ker := hk ▸ pCore_isPGroup
    have hpre := hp.comap_of_ker_isPGroup a hker
    have hI2p : IsPGroup 2 (I2.subgroupOf I) := hpre.to_le (le_comap_map a (I2.subgroupOf I))
    have hIp : IsPGroup 2 I2 := hI2p.of_equiv (subgroupOfEquivOfLe hI2)
    obtain ⟨q⟩ := hquot
    have hSp : IsPGroup 2 (Equiv.Perm (Fin 3)) :=
      (hIp.of_surjective (QuotientGroup.mk' (pCore 2 I2)) (QuotientGroup.mk'_surjective _)).of_equiv q
    obtain ⟨n,hn⟩ := hSp.exists_card_eq
    have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by rw [Nat.card_perm,Nat.card_fin]; decide
    have hd : 3 ∣ 2^n := hn ▸ hc.symm ▸ (by decide : 3 ∣ 6)
    exact (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
  exact point_image_eq_of_sylow a.range P ((S0.subgroupOf I).map a) hA
    (restrictedActor_sylow I K S0 hIK hSyl f) (map_mono (subgroupOf_mono I hSI2)) hP hnp
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix

namespace CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]

/-- The fixed constant vector is already in the actual second-parabolic
plane span. Its coordinates and full normalizer centralization are retained. -/
theorem source_fixed_vector
    (I K S0 I2 B : Subgroup G) (hIK : I ≤ normalizer (K : Set G))
    (hI2 : I2 ≤ I) (hSI2 : S0 ≤ I2)
    (hSyl : Chapter1.IsSylowIn 2 S0 I)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* S)
    (he : ∀ (n : normalizer (K : Set G)) (v : sourceModule K)
      (hv : n.val*v.val*n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd = coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (hk : (restrictedActor I K hIK f).ker = pCore 2 I)
    (hA : alternatingGroup (Fin 6) ≤ (restrictedActor I K hIK f).range)
    (hquot : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hBW : B ≤ sourceModule K) (hB : sourceImage (sourceModule K) E B = CoreCrossing.plane)
    (z : sourceModule K) (hz : (E z).toAdd = CoreCrossing.z)
    (hIz : I2 ≤ centralizer ({z.val} : Set G)) :
    ∃ a : sourceModule K, a.val ∈ conjugateSpanBy B I2 ∧ a.val ≠ 1 ∧
      I ≤ centralizer ({a.val} : Set G) ∧ (E a).toAdd = CoreCrossing.oneWord := by
  let A := restrictedActor I K hIK f
  let P := (I2.subgroupOf I).map A
  have hP := source_second_parabolic_image I K S0 I2 hIK hI2 hSI2 hSyl E f he hk hA hquot z hz hIz
  have hL1 : L1 ≤ P := by
    rw [show P = A.range ⊓ H1 from hP]
    exact le_inf (inf_le_right.trans hA) inf_le_left
  have hspan := sourceImage_conjugateSpan I (sourceModule K) B I2 E A
    (hIK.trans (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K)))
    hI2 hBW (fun i v => he (inclusion hIK i) v _)
  have horbit : Homogeneous.orbitSpan (coreRepresentation (Fin 6)) L1 CoreCrossing.plane ≤
      Homogeneous.orbitSpan (coreRepresentation (Fin 6)) P CoreCrossing.plane := by
    apply Homogeneous.orbitSpan_le
      _ (Homogeneous.le_orbitSpan _ _ _)
      (hL1.trans (Homogeneous.orbitSpan_invariant _ _ _))
  have hone : CoreCrossing.oneWord ∈ sourceImage (sourceModule K) E (conjugateSpanBy B I2) := by
    rw [hspan,hB]
    exact horbit (CoreCrossing.orbitSpan_eq_hyperplane.symm ▸ CoreCrossing.oneWord_mem_hyperplane)
  let a := E.symm (Multiplicative.ofAdd CoreCrossing.oneWord)
  have ha : (E a).toAdd = CoreCrossing.oneWord := by simp [a]
  refine ⟨a,(mem_sourceImage _ E _ a).mp (ha.symm ▸ hone),?_,?_,ha⟩
  · intro hh
    have ha1 : a = 1 := Subtype.ext hh
    have hh0 : CoreCrossing.oneWord = 0 := by simpa only [ha1,map_one,toAdd_one] using ha.symm
    exact (by decide : CoreCrossing.oneWord ≠ 0) hh0
  · intro i hi
    have hip : i*a.val*i⁻¹ ∈ sourceModule K :=
      (mem_normalizer_iff.mp
        (normalizer_le_normalizer_characteristic_image K (ChapterC.blockU K) (hIK hi)) a).mp a.property
    have hh := he ⟨i,hIK hi⟩ a hip
    rw [ha] at hh
    have hfix : coreRepresentation (Fin 6) (f ⟨i,hIK hi⟩) CoreCrossing.oneWord = CoreCrossing.oneWord :=
      Subtype.ext rfl
    rw [hfix,←ha] at hh
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (E.injective (Multiplicative.toAdd.injective hh))))

omit [Finite G] in
/-- The only nonidentity core element centralized by the alternating
component is its constant vector. -/
theorem source_fixed_core_coordinate (K : Subgroup G)
    (E : sourceModule K ≃* Multiplicative (core (Fin 6)))
    (f : normalizer (K : Set G) →* S)
    (he : ∀ (n : normalizer (K : Set G)) (v : sourceModule K)
      (hv : n.val*v.val*n.val⁻¹ ∈ sourceModule K),
      (E ⟨n.val*v.val*n.val⁻¹,hv⟩).toAdd = coreRepresentation (Fin 6) (f n) (E v).toAdd)
    (hA : (K.subgroupOf (normalizer (K : Set G))).map f = alternatingGroup (Fin 6))
    (a : sourceModule K) (ha : a.val ≠ 1) (hKa : K ≤ centralizer ({a.val} : Set G)) :
    (E a).toAdd = CoreCrossing.oneWord := by
  let v := (E a).toAdd
  have hv (g : alternatingGroup (Fin 6)) : coreRepresentation (Fin 6) g.val v = v := by
    have hgmem : g.val ∈ (K.subgroupOf (normalizer (K : Set G))).map f := by
      rw [hA]
      exact g.property
    obtain ⟨n,hn,hng⟩ := hgmem
    have hna : n.val*a.val*n.val⁻¹ = a.val := by
      have hh : n.val*a.val = a.val*n.val := mem_centralizer_singleton_iff.mp (hKa hn)
      rw [hh,mul_inv_cancel_right]
    have hh := he n a (hna.symm ▸ a.property)
    have hh' : (⟨n.val*a.val*n.val⁻¹,hna.symm ▸ a.property⟩ : sourceModule K) = a := Subtype.ext hna
    rw [hh',hng] at hh
    exact hh.symm
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin 6) (by simp)
  have hconst (i : Fin 6) : v.val i = v.val 0 := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) (0 : Fin 6) i
    have hh := congrArg (fun w : core (Fin 6) => w.val (g.val 0)) (hv g)
    change v.val (g.val.symm (g.val 0)) = v.val (g.val 0) at hh
    rw [g.val.symm_apply_apply] at hh
    exact (show g.val 0 = i from hg) ▸ hh.symm
  have hv0 : v.val 0 ≠ 0 := by
    intro hz
    have hvz : v = 0 := Subtype.ext (funext (fun i => (hconst i).trans hz))
    have hae : E a = E 1 := by
      apply Multiplicative.toAdd.injective
      simpa only [map_one,toAdd_one] using hvz
    exact ha (congrArg Subtype.val (E.injective hae))
  have hvo : v.val 0 = 1 := by
    generalize hc : v.val 0 = c at *
    fin_cases c
    · exact (hv0 rfl).elim
    · rfl
  exact Subtype.ext (funext (fun i => (hconst i).trans hvo))
end CFSG.Quasithin.Chapter14.Section06.RankFiveNaturalSix
