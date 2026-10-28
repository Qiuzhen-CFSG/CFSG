module
public import Theory.GroupTheory.CubicResidualSelection
public import Theory.GroupTheory.PResidual.OddConjugateSpan
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ResidualCubic
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.Uniqueness

/-!
# Single-factor selection and the ordinary larger-kernel local product

Use the actual H=C_G(z), V_H=⟨Ω₁(Z(T))^H⟩, K=C_H(V_H), and embedded
D=O²(K). Earlier 13.4.4(ii) makes R₁ Sylow in C_H(D/O₂(D)). Consequently
I=⟨J(R₁)^H⟩ centralizes that section. Its two-group seed makes I
three-perfect. If D/O₂(D) has order three, central-kernel elimination
and the ambient three-rank bound select I/O₂(I)≅S₃ and identify the
actual action image with S₃. The existing relative Thompson theorem
then gives m([V_H,I])=2.

The final theorem applies this to the ordinary A₆, Baumann-bound branch.
The core marking and the literal residual identity construct the cubic
section. The earlier Baumann bound supplies noncentrality. The fixed-line
argument and earlier 13.3.9/13.4.2 residual statements then give the actual
H/O₂(H)≅S₃×S₃, H=L₁IT, H∩M=L₁T, the set product, and uniqueness of IT
in HStar(T,M) within H. No local product or fusion conclusion is assumed.

Earlier-source inputs retain final discharge with qt-d-1341-fixed-core-source.
The covered-row exclusion, larger-kernel short-block noncentrality, original
R₁ identification, C₃ geometry, involution orbits and ambient fusion remain
with qt-d-1341-solvable-source. This is not full 13.4.8–9.
Source: Aschbacher–Smith 13.4.8, printed pp.904–905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal larger-kernel section selects one factor without assuming
that the full action kernel is a two-group. -/
theorem centralizer_single_factor_of_cubic_residual_section
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))).subtype).map
          (centralizer ({z} : Set G)).subtype = R)
    (hcard : let H := centralizer ({z} : Set G)
      let K := centralizer ((centralizerOmegaOrbit T z).subgroupOf H : Set H)
      let D := (pResidual 2 K).map K.subtype
      Nat.card (D ⧸ pCore 2 D) = 3)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G))) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (((I.subgroupOf H).map q) ≃* Equiv.Perm (Fin 3)) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let K := centralizer (U : Set H)
  let D := (pResidual 2 K).map K.subtype
  let C := residualSectionCentralizer 2 K
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let N := I.subgroupOf H
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans (original_sylow_le_centralizer hz)))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  let : D.Normal := inferInstance
  let : (D.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 D).map D.subtype).Normal
  obtain ⟨hc,_,hIC,_⟩ := centralizer_larger_kernel_local_data h₀ hz hz1 R hRT S hR
  have hQR := hc.symm.le.trans inf_le_left
  have hnC : N ≤ C := by
    intro x hx
    exact (mem_map_iff_mem H.subtype_injective).mp (hIC hx)
  have hcomm : ⁅N,D⁆ ≤ D.pCoreIn 2 :=
    (commutator_mono hnC le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ D (D.pCoreIn 2) le_normalizer_of_normal)
  let eN : N ≃* I := subgroupOfEquivOfLe hIH
  have hpJ : IsPGroup 2 (elementaryAbelianMaxJ R) :=
    (T.isPGroup'.to_le hRT).to_le (sSup_le fun _ hA => hA.1)
  obtain ⟨n,hn⟩ := hpJ.exists_card_eq
  have hperf : IsPPerfect 3 I := isPPerfect_conjugateSpanBy_of_coprime _ _
    (by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)
  have hperfN := hperf.of_surjective eN.symm.toMonoidHom eN.symm.surjective
  have hQK : pCore 2 H ≤ K := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hm := centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv
  have hrank : primeRank 3 H ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      3 (by decide) (by decide)
  obtain ⟨⟨e⟩,hNK⟩ := CubicResidualSelection.core_quotient_single K N hQK
    hcard hperfN hcomm hm hrank
  refine ⟨⟨(QuotientGroup.congr _ _ eN (pCore_map_iso 2 eN)).symm.trans e⟩,?_⟩
  let q := QuotientGroup.mk' K
  let f := q.subgroupMap N
  have hk : f.ker = pCore 2 N := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',pCore_eq_comap_of_normal]
    apply le_antisymm
    · intro x hx
      exact hNK ⟨x.property,hx⟩
    · intro x hx
      exact hQK hx
  let eqI : (N ⧸ pCore 2 N) ≃* N.map q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective N))
  exact ⟨eqI.symm.trans e⟩

/-- The earlier Baumann bound supplies noncentrality, and the cubic residual
section then supplies both clauses of the source Thompson-factor conclusion. -/
theorem centralizer_single_factor_data_of_larger_kernel
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))).subtype).map
          (centralizer ({z} : Set G)).subtype = R)
    (hcard : let H := centralizer ({z} : Set G)
      let K := centralizer ((centralizerOmegaOrbit T z).subgroupOf H : Set H)
      let D := (pResidual 2 K).map K.subtype
      Nat.card (D ⧸ pCore 2 D) = 3)
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G))) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z,I⁆ : Subgroup G) = 2 := by
  obtain ⟨hc,_,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz hz1 R hRT S hR
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hc hB hout
  obtain ⟨he,hm⟩ := centralizer_single_factor_of_cubic_residual_section h₀ hz hz1 R hRT
    S hR hcard hJ hsolv
  have hfour := centralizer_thompson_commutator_card_of_single_factor h₀ hz hz1 R hRT
    (hc.symm.le.trans inf_le_left) hJ hsolv hm
  refine ⟨he,?_⟩
  change Nat.log 2 _ = 2
  rw [hfour]
  decide

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped Pointwise
universe u

/-- In the ordinary larger-kernel, Baumann-bound branch, the literal source residual
identity supplies the cubic section and hence the pair quotient and local product. -/
theorem centralizer_pair_quotient_of_ordinary_larger_kernel
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))).subtype).map
          (centralizer ({z.val} : Set G)).subtype = R)
    (hres : let H := centralizer ({z.val} : Set G)
      let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
      ((pResidual 2 K).map K.subtype).map H.subtype = firstCentralizerResidual L z.val)
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨eo⟩ := ordinary
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eo]
    exact pCore_isPGroup
  have hcard := centralizer_kernel_residual_core_card_of_firstResidual D m hcore z hzL hres
  obtain ⟨hc,_,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz hz1 R hRT S hR
  have hQR := hc.symm.le.trans inf_le_left
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hc hB hout
  obtain ⟨hq,hm⟩ := centralizer_single_factor_of_cubic_residual_section h₀ hz hz1
    R hRT S hR hcard hJ hsolv
  have hfour := centralizer_thompson_commutator_card_of_single_factor h₀ hz hz1 R hRT
    hQR hJ hsolv hm
  have hr : Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,
      conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z.val} : Set G))⁆ : Subgroup G) = 2 := by
    change Nat.log 2 _ = 2
    rw [hfour]
    decide
  have hprod := centralizer_thompson_normalizer_product h₀ h structural hz hzL R hRT hQR hJ
    hsolv hindex hm
  have hi := centralizer_thompson_normalizer_index h structural hz R hRT hq hprod hout
  have hres := firstCentralizerResidual_eq_intersection_residual z.val h1342
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let A := firstCentralizerResidual L z.val
  obtain ⟨hpi,hgen⟩ := centralizer_firstResidual_product_of_normalizer_product
    h structural hz I hprod hi h1339 hres
  have hinter := centralizer_intersection_product_of_twoThree h structural hz hpi hres
  have hu := centralizer_thompson_unique_of_source_product D m hcore z hzL hz
    R hRT hq hgen hinter hout
  refine ⟨centralizer_pair_quotient_of_source_product D m hcore z hzL hz R hRT
    hq hgen hinter hout,hq,hr,hgen,hinter,?_,hu⟩
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hAH : A ≤ H := (firstCentralizerResidual_le L z.val).trans inf_le_right
  have hnA : (T : Subgroup G) ≤ normalizer (A : Set G) := by
    rw [show A = firstCentralizerResidual L z.val from rfl,firstCentralizerResidual_eq]
    have hn : (T : Subgroup G) ≤ normalizer
        ((L ⊓ H : Subgroup G) : Set G) :=
      (le_inf D.sylow_normalizes_component (hTH.trans H.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    exact hn.trans (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))
  have hnI : H ≤ normalizer (I : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnAI : (T : Subgroup G) ≤ normalizer ((A ⊔ I : Subgroup G) : Set G) :=
    (le_inf hnA (hTH.trans hnI)).trans (normalizer_inf_normalizer_le_normalizer_sup A I)
  calc
    (H : Set G) = ((A ⊔ I ⊔ (T : Subgroup G) : Subgroup G) : Set G) :=
      congrArg (fun B : Subgroup G => (B : Set G)) hgen
    _ = ((A ⊔ I : Subgroup G) : Set G) * (T : Set G) :=
      coe_mul_of_right_le_normalizer_left _ _ hnAI
    _ = (A : Set G) * (I : Set G) * (T : Set G) := by
      rw [coe_mul_of_left_le_normalizer_right A I (hAH.trans hnI)]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
