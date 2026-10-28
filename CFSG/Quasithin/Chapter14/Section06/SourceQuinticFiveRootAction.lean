module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveFixedCyclic
public import Theory.GroupTheory.CommutatorOrbitCard
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The native cyclic root acts on the original five-residual

Once the full core centralizer of the actual residual is its central line,
the original five-action counts the fixed subgroup of a cyclic root. It is
exactly the original elementary derived layer. The commutator subgroup has
at least sixteen elements, meets the residual center nontrivially, and its
five-action count forces order thirty-two. Thus both root-action conditions
needed by semilinear coordinate construction follow from one intrinsic
centralizer condition; no coordinates or model are assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual cyclic fixed root has residual centralizer and commutator
exactly U. The only additional intrinsic premise is the full residual
centralizer in Q; the original exact (64,1024) branch is retained. -/
theorem source_quintic_large_five_root_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5)
    (hcR : H.pCoreIn 2 ⊓ centralizer ((⁅H.pCoreIn 2,A⁆ : Subgroup G) : Set G) = centralInvolutions T)
    (t : G) (ht : t ∈ H.pCoreIn 2 ⊓ centralizer (A : Set G))
    (htR : t ∉ ⁅H.pCoreIn 2,A⁆) :
    let U := conjugateSpanBy (localModule T M) H
    let R := ⁅H.pCoreIn 2,A⁆
    R ⊓ centralizer ({t} : Set G) = U ∧ ⁅R,zpowers t⁆ = U := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let B := Q ⊓ centralizer (A : Set G)
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  let D := R ⊓ centralizer ({t} : Set G)
  obtain ⟨_,_,_,_,hRcard,hUR,_,_⟩ := source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  obtain ⟨_,hRB,_,hcenter,hQR,hAR⟩ := source_quintic_large_five_residual_center
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  change Nat.card R = 512 at hRcard
  change U ≤ R at hUR
  change R ⊓ B = Z at hRB
  change (center R).map R.subtype = Z at hcenter
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hUcard : Nat.card U = 32 := (source_quintic_span_card_and_core_radical
    hG T hempty hM hu hmany hcard e H hH hi).1
  have htU : t ∈ centralizer (U : Set G) :=
    ((source_quintic_five_centralizers hG T hempty hM hu hmany hcard e H hH hi
      A hAH hA).2.le ht).1.2
  have hUD : U ≤ D := le_inf hUR (fun u hu =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htU u hu))
  have hHZ : H ≤ centralizer (Z : Set G) := (Section02.source_lemma_14_2_3
    hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hAC : A ≤ centralizer ({t} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ht.2 a ha)
  have hAD : A ≤ normalizer (D : Set G) :=
    (le_inf hAR (hAC.trans (centralizer ({t} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let : MulDistribMulAction A D := conjMulDistribMulActionOfLeNormalizer A D hAD
  have hFD : (FixedPoints.subgroup A D).map D.subtype = Z := by
    apply le_antisymm
    · rintro x ⟨d,hd,rfl⟩
      apply hRB.le
      refine ⟨d.property.1,hRQ d.property.1,?_⟩
      intro a ha
      have hh := congrArg (fun d : D => (d : G)) (hd ⟨a,ha⟩)
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro z hz
      refine ⟨⟨z,hUD (hZU hz)⟩,?_,rfl⟩
      intro a
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((hHZ (hAH a.property)) z hz).symm
  have hFcard : Nat.card (FixedPoints.subgroup A D) = 2 := by
    rw [← card_map_of_injective D.subtype_injective,hFD,hZcard]
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hAfive : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hAfive.card_modEq_card_fixedPoints D
  change Nat.card D % 5 = Nat.card (FixedPoints.subgroup A D) % 5 at hmod
  rw [hFcard] at hmod
  have hdiv : Nat.card D ∣ 2 ^ 9 := by
    simpa only [hRcard,Nat.reducePow] using card_dvd_of_le (show D ≤ R from inf_le_left)
  have hproper : Nat.card D ≠ 512 := by
    intro he
    have heq : D = R := eq_of_le_of_card_ge inf_le_left (by rw [he,hRcard])
    apply htR
    apply hZU.trans hUR
    apply hcR.le
    refine ⟨ht.1,?_⟩
    intro r hr
    exact mem_centralizer_singleton_iff.mp ((heq.ge hr).2)
  obtain ⟨n,hn,hncard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hDcard : Nat.card D = 32 := by
    have hlo := card_le_of_le hUD
    rw [hUcard] at hlo
    interval_cases n <;> norm_num only [Nat.reducePow] at hncard <;> omega
  have hDeq : D = U := (eq_of_le_of_card_ge hUD (by rw [hDcard,hUcard])).symm
  refine ⟨hDeq,?_⟩
  let E := ⁅R,zpowers t⁆
  have hEU : E ≤ U := by
    have hh := commutator_mono hRQ (zpowers_le.mpr ht.1)
    exact hh.trans_eq (source_quintic_full_core_layers
      hG T hempty hM hu hmany hcard e H hH hi).1
  have hER : E ≤ R := hEU.trans hUR
  have hCR : Nat.card ((centralizer ({t} : Set G)).subgroupOf R) = 32 := by
    have he : (centralizer ({t} : Set G)).subgroupOf R = U.subgroupOf R := by
      ext r
      change (r : G) ∈ centralizer ({t} : Set G) ↔ (r : G) ∈ U
      rw [← hDeq]
      simp only [D,mem_inf,r.property,true_and]
    rw [he,Nat.card_congr (subgroupOfEquivOfLe hUR).toEquiv,hUcard]
  have hElow : 16 ≤ Nat.card E := by
    have hh := card_le_commutator_card_mul_centralizer R t
    rw [hRcard,hCR] at hh
    change 16 ≤ Nat.card (⁅R,zpowers t⁆ : Subgroup G)
    omega
  have hAE : A ≤ normalizer (E : Set G) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq]
    have hta : MulAut.conj a t = t :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp ht.2 a ha)
    change E.map (MulAut.conj a).toMonoidHom = E
    dsimp only [E]
    have hRa : R.map (MulAut.conj a).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hAR ha)
    rw [map_commutator,hRa,MonoidHom.map_zpowers]
    change ⁅R,zpowers (MulAut.conj a t)⁆ = ⁅R,zpowers t⁆
    rw [hta]
  let : MulDistribMulAction A E := conjMulDistribMulActionOfLeNormalizer A E hAE
  let F := FixedPoints.subgroup A E
  have hFZ : F.map E.subtype ≤ Z := by
    rintro x ⟨d,hd,rfl⟩
    apply hRB.le
    refine ⟨hER d.property,hRQ (hER d.property),?_⟩
    intro a ha
    have hh := congrArg (fun d : E => (d : G)) (hd ⟨a,ha⟩)
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hFbound : Nat.card F ≤ 2 := by
    have hh := card_le_of_le hFZ
    rwa [card_map_of_injective E.subtype_injective,hZcard] at hh
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 R) := ⟨IsPGroup.of_card (n := 9) hRcard⟩
  let : (E.subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hER).mpr (normalizer_commutator_ge_left R (zpowers t))
  have hEnative : Nat.card (E.subgroupOf R) = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv
  let : Nontrivial (E.subgroupOf R) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hEnative]; omega)
  obtain ⟨w,hwne,hwZ⟩ := exists_nontrivial_center_mem_normal (E.subgroupOf R) (p := 2)
  let wE : E := ⟨((w : R) : G),w.property⟩
  have hwF : wE ∈ F := by
    intro a
    apply Subtype.ext
    change (a : G) * (wE : G) * (a : G)⁻¹ = (wE : G)
    exact mul_inv_eq_iff_eq_mul.mpr ((hHZ (hAH a.property)) _
      (hcenter ▸ mem_map_of_mem R.subtype hwZ)).symm
  have hFne : F ≠ ⊥ := by
    intro he
    have hh : wE = 1 := he.le hwF
    apply hwne
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun d : E => (d : G)) hh
  have hFtwo : Nat.card F = 2 := by
    have hh := (one_lt_card_iff_ne_bot F).mpr hFne
    omega
  have hEmod := hAfive.card_modEq_card_fixedPoints E
  change Nat.card E % 5 = Nat.card F % 5 at hEmod
  rw [hFtwo] at hEmod
  have hEdiv : Nat.card E ∣ 2 ^ 5 := by
    simpa only [hUcard,Nat.reducePow] using card_dvd_of_le hEU
  obtain ⟨k,hk,hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hEdiv
  have hEcard : Nat.card E = 32 := by
    interval_cases k <;> norm_num only [Nat.reducePow] at hkcard <;> omega
  exact eq_of_le_of_card_ge hEU (by rw [hUcard,hEcard])

end CFSG.Quasithin.Chapter14.Section06
