module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.Native
public import Stellmacher.CentralizerQuotientAction
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Stellmacher.SectionOne.SL2FactorJoinPrime

/-!
# Intrinsic residual factors with their original supports

For each native factor Dᵢ, put Fᵢ=Dᵢ′ and take Kᵢ to be the two-residual
of O²(G) intersected with the original preimage of Fᵢ. The literal action
identifies its commutator layer with the original four-element support.
Central two-kernel elimination gives precisely that support as O₂(Kᵢ),
and the quotient has order three. The same Kᵢ are subnormal, are generated
by their commutators with J(S), and jointly generate O²(G).

Only the kernel restricted to each perfect subgroup is used in lifting
commutator generation; no two-group assertion about the entire module
centralizer is made. These intrinsic factors supply the solvable local
C.1.29 outside-block argument (Aschbacher–Smith, printed pp.132–134), from
Stellmacher (1.7), (2.2) and (2.4), `refs/latex/stellmacher-n-group.tex`.
-/

public section
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
open Subgroup Stellmacher
open scoped commutatorElement
universe u
variable {G B : Type u} [Group G] [Finite G] [Group B] [Finite B]

abbrev ActualData (S : Sylow 2 G) (q : G →* B) (hq : Function.Surjective q)
    (hker : q.ker = SectionTwo.cSubgroup S) :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData S q hq

private theorem elementary_of_injective {A D : Type*} [Group A] [Group D]
    {p : ℕ} [IsElementaryAbelian p D] (f : A →* D) (hf : Function.Injective f) :
    IsElementaryAbelian p A := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    apply hf
    simpa only [map_mul] using (IsMulCommutative.is_comm (M := D)).comm (f a) (f b)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    apply hf
    simpa only [map_pow, map_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p D) (f a)

omit [Finite G] [Finite B] in
/-- Only the kernel inside the original perfect subgroup is needed. -/
private theorem le_of_twoPerfect_of_image_le
    (K N : Subgroup G) (hp : IsPPerfect 2 K) (hNK : N ≤ K)
    (hn : K ≤ normalizer (N : Set G)) (f : G →* B)
    (hk : IsPGroup 2 (f.ker.subgroupOf K)) (hi : K.map f ≤ N.map f) : K ≤ N := by
  have him : K ≤ N ⊔ f.ker := by
    have hh := (le_comap_map f K).trans (comap_mono (f := f) hi)
    simpa only [comap_map_eq] using hh
  let : (N.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hNK).mpr hn
  have ht : (⊤ : Subgroup K) ≤ N.subgroupOf K ⊔ f.ker.subgroupOf K := by
    intro x _
    obtain ⟨n, hn, k, hk, he⟩ := mem_sup_of_normal_right.mp (him x.property)
    have hkK : k ∈ K := by
      have heq : k = n⁻¹ * (x : G) := by rw [← he]; group
      rw [heq]
      exact K.mul_mem (K.inv_mem (hNK hn)) x.property
    have hh := mul_mem_sup (show (⟨n, hNK hn⟩ : K) ∈ N.subgroupOf K from hn)
      (show (⟨k, hkK⟩ : K) ∈ f.ker.subgroupOf K from hk)
    have he' : (⟨n, hNK hn⟩ : K) * ⟨k, hkK⟩ = x := Subtype.ext he
    rwa [he'] at hh
  have hp' : IsPPerfect 2 (⊤ : Subgroup K) :=
    hp.of_surjective (topEquiv : (⊤ : Subgroup K) ≃* K).symm.toMonoidHom
      (topEquiv : (⊤ : Subgroup K) ≃* K).symm.surjective
  have hh := le_normal_of_isPPerfect_of_le_sup_pGroup ⊤ (N.subgroupOf K)
    (f.ker.subgroupOf K) hp' hk ht
  intro x hx
  exact hh (mem_top (⟨x, hx⟩ : K))

namespace ActualData
variable {S : Sylow 2 G} {q : G →* B} {hq : Function.Surjective q}
  {hker : q.ker = SectionTwo.cSubgroup S}

variable (d : ActualData S q hq hker)

abbrev E :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.E d

abbrev E_normal :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.E_normal d

abbrev E_baumann :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.E_baumann d

abbrev n :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.n d

abbrev D :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.D d

abbrev product :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.product d

abbrev independent :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.independent d

abbrev injective :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.injective d

abbrev factors :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.factors d

abbrev module_product :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.module_product d

abbrev thompson :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.thompson d

abbrev residual_image :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.residual_image d

abbrev commutator_le :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.commutator_le d

abbrev core_centralizes :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.core_centralizes d

abbrev residual_kernel :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  NativeData.residual_kernel d

noncomputable def oddFactor (i : Fin d.n) : Subgroup B :=
  (commutator (d.D i)).map (d.D i).subtype

noncomputable def factorPreimage (i : Fin d.n) : Subgroup G :=
  pResidual 2 G ⊓ (d.oddFactor i).comap q

noncomputable def residualFactor (i : Fin d.n) : Subgroup G :=
  (pResidual 2 (d.factorPreimage i)).map (d.factorPreimage i).subtype

noncomputable def support (i : Fin d.n) : Subgroup G :=
  letI := SectionTwo.quotientConjugationAction S q hq hker
  (commutatorAction (d.oddFactor i) (SectionTwo.vSubgroup S)).map
    (SectionTwo.vSubgroup S).subtype

theorem oddFactor_card (i : Fin d.n) : Nat.card (d.oddFactor i) = 3 :=
  (d.factors i).2.1.2.1

theorem oddFactor_three (i : Fin d.n) : IsPGroup 3 (d.oddFactor i) :=
  IsPGroup.of_card (n := 1) (by simpa using d.oddFactor_card i)

theorem oddFactor_twoPerfect (i : Fin d.n) : IsPPerfect 2 (d.oddFactor i) := by
  apply (pResidual_eq_top_iff 2 _).mp
  apply top_unique
  intro a _
  exact mem_pResidual_of_orderOf_coprime
    ((d.oddFactor_three i).orderOf_coprime (by decide : Nat.Coprime 3 2) a).symm

theorem oddFactor_le_image (i : Fin d.n) : d.oddFactor i ≤ (pResidual 2 G).map q := by
  rw [d.residual_image, d.product.derived.1]
  exact le_iSup (fun j : Fin d.n => (commutator (d.D j)).map (d.D j).subtype) i

theorem factorPreimage_map (i : Fin d.n) : (d.factorPreimage i).map q = d.oddFactor i := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := d.oddFactor_le_image i hx
    exact ⟨y, ⟨hy, hx⟩, rfl⟩

theorem residualFactor_map (i : Fin d.n) : (d.residualFactor i).map q = d.oddFactor i := by
  rw [residualFactor, map_embedded_pResidual, d.factorPreimage_map,
    (pResidual_eq_top_iff 2 _).mpr (d.oddFactor_twoPerfect i),
    ← MonoidHom.range_eq_map, range_subtype]

theorem residualFactor_le (i : Fin d.n) : d.residualFactor i ≤ pResidual 2 G :=
  (map_subtype_le _).trans inf_le_left

theorem residualFactor_twoPerfect (i : Fin d.n) : IsPPerfect 2 (d.residualFactor i) := by
  let e := (pResidual 2 (d.factorPreimage i)).equivMapOfInjective
    (d.factorPreimage i).subtype (d.factorPreimage i).subtype_injective
  exact (isPPerfect_pResidual 2).of_surjective e.toMonoidHom e.surjective

theorem residualFactor_normalized (i : Fin d.n) :
    pResidual 2 G ≤ normalizer (d.residualFactor i : Set G) := by
  let := SectionTwo.quotientConjugationAction S q hq hker
  have he : IsElementaryAbelian 3 ((pResidual 2 G).map q) := by
    rw [d.residual_image]
    exact SectionOne.internalOneSevenProduct_derived_isElementaryAbelian d.E d.D d.product d.factors
  let := he
  have hn : pResidual 2 G ≤ normalizer (d.factorPreimage i : Set G) := by
    apply le_normalizer_iff.mpr
    intro r hr x hx
    refine ⟨(pResidual 2 G).mul_mem ((pResidual 2 G).mul_mem hr hx.1) ((pResidual 2 G).inv_mem hr), ?_⟩
    change q (r * x * r⁻¹) ∈ d.oddFactor i
    have hc : q r * q x = q x * q r := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := (pResidual 2 G).map q)).comm
        (⟨q r, mem_map_of_mem q hr⟩ : (pResidual 2 G).map q)
        ⟨q x, mem_map_of_mem q hx.1⟩)
    simpa only [map_mul, map_inv, hc, mul_inv_cancel_right] using (show q x ∈ d.oddFactor i from hx.2)
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (d.factorPreimage i) (pResidual 2 (d.factorPreimage i)))

theorem residualFactor_subnormal (i : Fin d.n) : (d.residualFactor i).IsSubnormal :=
  IsSubnormal.step _ (pResidual 2 G) (d.residualFactor_le i)
    (inferInstance : (pResidual 2 G).Normal).isSubnormal
    ((normal_subgroupOf_iff_le_normalizer (d.residualFactor_le i)).mpr
      (d.residualFactor_normalized i))

theorem support_eq_commutator (i : Fin d.n) :
    d.support i = ⁅SectionTwo.vSubgroup S, d.residualFactor i⁆ := by
  let := SectionTwo.quotientConjugationAction S q hq hker
  have hh := centralizerQuotientAction_commutatorSubgroup_image_map
    (SectionTwo.vSubgroup S) normalClosure_normal q hq hker (d.residualFactor i) ⊤
  rw [d.residualFactor_map] at hh
  simpa only [support, ← MonoidHom.range_eq_map, range_subtype] using hh

theorem support_card (i : Fin d.n) : Nat.card (d.support i) = 4 := by
  let := SectionTwo.quotientConjugationAction S q hq hker
  rw [support, card_map_of_injective (SectionTwo.vSubgroup S).subtype_injective]
  exact (d.factors i).2.1.2.2

theorem support_le_v (i : Fin d.n) : d.support i ≤ SectionTwo.vSubgroup S :=
  map_subtype_le _

theorem support_le_core_commutator (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    d.support i ≤ ⁅pCore 2 G, pResidual 2 G⁆ := by
  rw [d.support_eq_commutator]
  exact commutator_mono (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h S).1
    (d.residualFactor_le i)

theorem core_commutator_factor (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    ⁅⁅pCore 2 G, pResidual 2 G⁆, d.residualFactor i⁆ = d.support i := by
  let V := SectionTwo.vSubgroup S
  let : V.Normal := normalClosure_normal
  let : IsElementaryAbelian 2 V :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  have hidem := commutator_isPPerfect_idempotent (d.residualFactor i) V
    (d.residualFactor_twoPerfect i) (IsElementaryAbelian.isPGroup 2 V) le_normalizer_of_normal
  apply le_antisymm
  · exact (commutator_mono d.commutator_le le_rfl).trans_eq (d.support_eq_commutator i).symm
  · rw [d.support_eq_commutator, ← hidem]
    exact commutator_mono (d.support_eq_commutator i ▸ d.support_le_core_commutator h i) le_rfl

theorem support_le_factor (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    d.support i ≤ d.residualFactor i := by
  rw [← d.core_commutator_factor h i]
  exact le_normalizer_iff_commutator_le_right.mp
    ((commutator_le_right _ _).trans (d.residualFactor_normalized i))

include d in
theorem residual_kernel_two :
    IsPGroup 2 (q.ker.subgroupOf (pResidual 2 G)) := by
  have hle : q.ker.subgroupOf (pResidual 2 G) ≤
      (pCore 2 G).subgroupOf (pResidual 2 G) := by
    intro x hx
    have hw := d.residual_kernel.le ⟨x.property, hx⟩
    exact (show ⁅pCore 2 G, pResidual 2 G⁆ ≤ pCore 2 G from commutator_le_left _ _) hw
  exact pCore_isPGroup.comap_subtype.to_le hle

theorem residualFactor_kernel_two (i : Fin d.n) :
    IsPGroup 2 (q.ker.subgroupOf (d.residualFactor i)) := by
  have hle : q.ker.subgroupOf (d.residualFactor i) ≤
      (pCore 2 G).subgroupOf (d.residualFactor i) := by
    intro x hx
    have hw := d.residual_kernel.le ⟨d.residualFactor_le i x.property, hx⟩
    exact (show ⁅pCore 2 G, pResidual 2 G⁆ ≤ pCore 2 G from commutator_le_left _ _) hw
  exact pCore_isPGroup.comap_subtype.to_le hle

theorem support_elementary (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    IsElementaryAbelian 2 (d.support i) := by
  let : IsElementaryAbelian 2 (SectionTwo.vSubgroup S) :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  exact elementary_of_injective (inclusion (d.support_le_v i)) (inclusion_injective _)

theorem factor_core_eq (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    pCore 2 (d.residualFactor i) = (d.support i).subgroupOf (d.residualFactor i) := by
  let K := d.residualFactor i
  let U := (d.support i).subgroupOf K
  let f : K →* K.map q := q.subgroupMap K
  have hKU : K ≤ normalizer (d.support i : Set G) := by
    rw [← d.core_commutator_factor h i]
    exact normalizer_commutator_ge_right _ _
  let : U.Normal := (normal_subgroupOf_iff_le_normalizer (d.support_le_factor h i)).mpr hKU
  let := SectionTwo.quotientConjugationAction S q hq hker
  have hc : Nat.card (K.map q) = 3 := by rw [d.residualFactor_map, d.oddFactor_card]
  let : IsCyclic (K.map q) := isCyclic_of_prime_card hc
  let : IsElementaryAbelian 3 (K.map q) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      simpa only [hc] using pow_card_eq_one' (x := x) }
  have hk : IsPGroup 2 f.ker := by
    have hle : f.ker ≤ q.ker.subgroupOf K := by
      intro x hx
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact (d.residualFactor_kernel_two i).to_le hle
  have hu : U ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change q x = 1
    exact MonoidHom.mem_ker.mp ((d.residual_kernel.ge (d.support_le_core_commutator h i hx)).2)
  have hkW : f.ker ≤ (⁅pCore 2 G, pResidual 2 G⁆).subgroupOf K := by
    intro x hx
    exact d.residual_kernel.le ⟨d.residualFactor_le i x.property,
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)⟩
  have hcomm : ⁅f.ker, (⊤ : Subgroup K)⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro x hx y _
    change ⁅(x : G), (y : G)⁆ ∈ d.support i
    rw [← d.core_commutator_factor h i]
    exact commutator_mem_commutator (hkW hx) y.property
  have heq := ker_eq_of_twoPerfect_of_elementary_three
    (d.residualFactor_twoPerfect i) f U hu hk hcomm
  have hbot : pCore 2 (K.map q) = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 (K.map q)) ⊤
      pCore_isPGroup ((IsElementaryAbelian.isPGroup 3 (K.map q)).to_subgroup ⊤)
    simpa only [inf_top_eq] using hd.eq_bot
  have hpre := f.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective K) hk
  rw [hbot, MonoidHom.comap_bot] at hpre
  exact hpre.symm.trans heq

theorem factor_core_elementary (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    IsElementaryAbelian 2 (pCore 2 (d.residualFactor i)) := by
  rw [d.factor_core_eq h i]
  let := d.support_elementary h i
  exact IsElementaryAbelian.subgroupOf (d.support_le_factor h i)

theorem factor_core_card (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    Nat.card (pCore 2 (d.residualFactor i)) = 4 := by
  rw [d.factor_core_eq h i, Nat.card_congr
    (subgroupOfEquivOfLe (d.support_le_factor h i)).toEquiv, d.support_card]

theorem factor_quotient_card (h : SectionTwo.Hypotheses G) (i : Fin d.n) :
    Nat.card (d.residualFactor i ⧸ pCore 2 (d.residualFactor i)) = 3 := by
  let K := d.residualFactor i
  let f : K →* K.map q := q.subgroupMap K
  have hkerCore : f.ker = pCore 2 K := by
    rw [d.factor_core_eq h i]
    ext x
    constructor
    · intro hx
      have hw : (x : G) ∈ ⁅pCore 2 G, pResidual 2 G⁆ :=
        d.residual_kernel.le ⟨d.residualFactor_le i x.property,
          congrArg Subtype.val (MonoidHom.mem_ker.mp hx)⟩
      have hxcore : x ∈ pCore 2 K := by
        have hN : f.ker ≤ pCore 2 K := le_sSup ⟨inferInstance, by
          have hh : f.ker ≤ q.ker.subgroupOf K := by
            intro y hy
            exact congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
          exact (d.residualFactor_kernel_two i).to_le hh⟩
        exact hN hx
      rwa [d.factor_core_eq h i] at hxcore
    · intro hx
      apply Subtype.ext
      exact MonoidHom.mem_ker.mp ((d.residual_kernel.ge (d.support_le_core_commutator h i hx)).2)
  rw [← hkerCore]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    (q.subgroupMap_surjective K)).toEquiv]
  rw [d.residualFactor_map, d.oddFactor_card]

theorem factor_normalized_thompson (i : Fin d.n) :
    elementaryAbelianMaxJ (S : Subgroup G) ≤ normalizer (d.residualFactor i : Set G) := by
  have hED : d.E ≤ normalizer (d.D i : Set B) := by
    have hgen : d.E = ⨆ j, d.D j := d.product.1
    rw [hgen]
    apply iSup_le
    intro j
    by_cases hji : j = i
    · subst j
      exact (d.D i).le_normalizer
    · apply le_trans _ (centralizer_le_normalizer (d.D i : Set B))
      rw [le_centralizer_iff]
      intro x hx y hy
      exact (d.product.2.2 i j (Ne.symm hji) x hx y hy).symm
  have hEF : d.E ≤ normalizer (d.oddFactor i : Set B) :=
    hED.trans (normalizer_le_normalizer_characteristic_image (d.D i) (commutator (d.D i)))
  have hpre : elementaryAbelianMaxJ (S : Subgroup G) ≤
      normalizer (d.factorPreimage i : Set G) := by
    apply le_normalizer_iff.mpr
    intro j hj x hx
    refine ⟨(inferInstance : (pResidual 2 G).Normal).conj_mem x hx.1 j, ?_⟩
    change q (j * x * j⁻¹) ∈ d.oddFactor i
    have hjE : q j ∈ d.E := by
      have hm := mem_map_of_mem q hj
      rw [d.thompson] at hm
      exact hm.2
    simpa only [map_mul, map_inv] using
      (mem_normalizer_iff.mp (hEF hjE) (q x)).mp hx.2
  exact hpre.trans (normalizer_le_normalizer_characteristic_image
    (d.factorPreimage i) (pResidual 2 (d.factorPreimage i)))

theorem oddFactor_commutator_thompson (i : Fin d.n) :
    d.oddFactor i = ⁅d.oddFactor i, (elementaryAbelianMaxJ (S : Subgroup G)).map q⁆ := by
  let := SectionTwo.quotientConjugationAction S q hq hker
  let T := (S.mapSurjective hq : Subgroup B) ⊓ d.D i
  have hTc : Nat.card T = 2 :=
    (SectionOne.sl2_family_sylow_coordinates (S.mapSurjective hq) d.E d.E_normal
      d.D d.product (fun j => (d.factors j).1)).2 i
  have hDT : d.oddFactor i ⊔ T = d.D i := by
    have hnorm : T ≤ normalizer (d.oddFactor i : Set B) :=
      inf_le_right.trans ((d.D i).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (d.D i) (commutator (d.D i))))
    have hdis : Disjoint (d.oddFactor i) T :=
      disjoint_of_coprime_natCard (by rw [d.oddFactor_card, hTc]; decide)
    apply eq_of_le_of_card_ge (sup_le (map_subtype_le _) inf_le_right)
    change Nat.card (d.D i) ≤ Nat.card (d.oddFactor i ⊔ T : Subgroup B)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm hdis,
      d.oddFactor_card, hTc, SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (d.factors i).1]
  have hTJ : T ≤ (elementaryAbelianMaxJ (S : Subgroup G)).map q := by
    rw [d.thompson]
    exact inf_le_inf_left _ (by rw [d.product.1]; exact le_iSup d.D i)
  have hcommle : ⁅d.oddFactor i, T⁆ ≤ d.oddFactor i := by
    have hm : ⁅d.oddFactor i, T⁆ ≤ ⁅d.D i, d.D i⁆ :=
      commutator_mono (map_subtype_le _) inf_le_right
    change ⁅d.oddFactor i, T⁆ ≤ (commutator (d.D i)).map (d.D i).subtype
    rwa [map_subtype_commutator]
  have hcommne : ⁅d.oddFactor i, T⁆ ≠ ⊥ := by
    intro he
    have hc := commutator_eq_bot_iff_le_centralizer.mp he
    apply SectionOne.sl2_not_normalizes_order_two (d.D i) T (d.factors i).1 hTc inf_le_right
    rw [← hDT]
    exact sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) T.le_normalizer
  let : Fact (Nat.card (d.oddFactor i)).Prime := ⟨by rw [d.oddFactor_card]; decide⟩
  have heq : ⁅d.oddFactor i, T⁆ = d.oddFactor i := by
    rcases (⁅d.oddFactor i, T⁆.subgroupOf (d.oddFactor i)).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hh := congrArg (Subgroup.map (d.oddFactor i).subtype) hb
      rw [map_subgroupOf_eq_of_le hcommle, Subgroup.map_bot] at hh
      exact (hcommne hh).elim
    · exact le_antisymm hcommle (subgroupOf_eq_top.mp ht)
  apply le_antisymm
  · exact heq.ge.trans (commutator_mono le_rfl hTJ)
  · rw [← d.residualFactor_map i, ← map_commutator]
    exact map_mono (le_normalizer_iff_commutator_le_left.mp (d.factor_normalized_thompson i))

theorem factor_commutator_thompson (i : Fin d.n) :
    d.residualFactor i = ⁅d.residualFactor i, elementaryAbelianMaxJ (S : Subgroup G)⁆ := by
  have hle := le_normalizer_iff_commutator_le_left.mp (d.factor_normalized_thompson i)
  apply le_antisymm ?_ hle
  apply le_of_twoPerfect_of_image_le (d.residualFactor i) _
    (d.residualFactor_twoPerfect i) hle (normalizer_commutator_ge_left _ _) q
    (d.residualFactor_kernel_two i)
  rw [map_commutator, d.residualFactor_map]
  exact (d.oddFactor_commutator_thompson i).le

theorem iSup_residualFactor :
    (⨆ i, d.residualFactor i) = pResidual 2 G := by
  have hle : (⨆ i, d.residualFactor i) ≤ pResidual 2 G := iSup_le d.residualFactor_le
  have hn : pResidual 2 G ≤ normalizer ((⨆ i, d.residualFactor i : Subgroup G) : Set G) :=
    (le_iInf d.residualFactor_normalized).trans (iInf_normalizer_le_normalizer_iSup _)
  apply le_antisymm hle
  apply le_of_twoPerfect_of_image_le (pResidual 2 G) _ (isPPerfect_pResidual 2)
    hle hn q (d.residual_kernel_two)
  rw [Subgroup.map_iSup]
  simp_rw [d.residualFactor_map]
  rw [d.residual_image, d.product.derived.1]
  exact le_rfl

end ActualData
end CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
