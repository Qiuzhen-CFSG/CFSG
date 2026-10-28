module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentCoveredFiveAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNaturalResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryBaumannAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationDoubledExclusion

/-!
# Excluding the ordinary doubled linear component at the original G,T

The actual doubled omega orbit supplies a cubic in the reciprocal point
centralizer. Relative normality in C_G(z) places the original residual L₁
inside K and identifies the two prime-to-three residuals. The point
centralizer is then exactly L₁T; its Thompson and Baumann subgroups agree
with those of O₂(KT). The original augmentation Baumann alternative forces
a short block, whose chief-factor budget excludes the doubled module.

These are guarded specializations of the point, residual and doubled-module
arguments in Nonsolvable/ComponentDoubled, ComponentLinearContainment,
ComponentRadicalBaumann and AugmentationDoubledExclusion. They use only
structural facts at the same G,T and retain the independent natural
LargeDistanceInput. ComponentCoveredDoubledAt completes both covering rows
and ComponentLinearModuleAt applies the exclusion to the original component.
Source: Aschbacher--Smith 13.2.2(7),13.4.10(2--4), pp.877--878,908--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

theorem component_moved_normalizes_firstResidual_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ≤
      normalizer (Solvable.firstCentralizerResidual L z : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z K
  let X := K ⊔ (T : Subgroup G)
  let C := centralizer ({z} : Set G) ⊓ normalizer (L : Set G)
  have hWX : W ≤ X := conjugateSpanBy_le
    ((show Z ≤ (T : Subgroup G) from fun _ hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans X.le_normalizer)
  have hred := component_orbit_reduced h₀ hzT hz1 hKz hTK
  let := hred.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf X).map X.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  have hWC : W ≤ C := by
    refine le_inf (hWX.trans (sup_le hKz (Solvable.original_sylow_le_centralizer hzT))) ?_
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    have hdW : m.constant.val ∈ W := le_conjugateSpanBy _ _
      (m.constant_mem_central_four_at h structural).2
    intro w hw
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨w,hw⟩ : W) ⟨m.constant.val,hdW⟩)
  have hr := Solvable.firstCentralizerResidual_eq_intersection_residual z
    (original_normalizer_residual_at h structural eL)
  rw [←hr]
  exact (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z K)).trans
    (hWC.trans (C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))))

private theorem component_sylow_in_original
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
  let X := K ⊔ (T : Subgroup G)
  let N := K.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup N).map e.toMonoidHom).map K.subtype ≤ _
  have he : ((Q : Subgroup N).map e.toMonoidHom).map K.subtype =
      ((Q : Subgroup N).map N.subtype).map X.subtype := by
    rw [map_map,map_map]
    rfl
  rw [he,hQ]
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])

/-- The doubled moved orbit supplies a cubic in the literal reciprocal
centralizer, before any containment of L₁ in K is known. -/
theorem doubled_reciprocal_cubic_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    3 ∣ Nat.card (K ⊓ normalizer (L : Set G) : Subgroup G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point_at h₀ h structural m hzT hz1 hKz hTK hKM
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  have hSw : (S : Subgroup K).map K.subtype ≤ centralizer ({w.val} : Set G) := by
    intro k hk
    have hkd : k ∈ centralizer ({m.constant.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_omegaOneCenterAmbient_iff _ _).mp
        (m.constant_mem_central_four_at h structural).2 |>.2.2 k (hS hk)
    exact (hC.le ⟨map_subtype_le _ hk,hkd⟩).2
  obtain ⟨f,hf,_⟩ := BinaryLinearThree.doubled_point_centralizer_of_sylow
    K U (normalizer_commutator_ge_right _ _) eK e he w hw S hSw
  have hd := card_dvd_of_surjective f hf
  rw [Nat.card_perm,Nat.card_fin] at hd
  have hc : K ⊓ normalizer (L : Set G) = K ⊓ centralizer ({w.val} : Set G) := by
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    exact hC
  rw [hc]
  exact (by decide : 3 ∣ Nat.factorial 4).trans hd

/-- The original ordinary-A₆ branch contains L₁ in a doubled linear-three
component; the reciprocal residual equality follows with the same embeddings. -/
theorem ordinary_doubled_component_residuals_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    Solvable.firstCentralizerResidual L z.val ≤ K ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val := by
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have h3 := doubled_reciprocal_cubic_at h₀ h structural D m hzT hz1 hKz hTK hKM eK e he
  have hJK := ordinary_firstResidual_le_of_reciprocal_cubic_at h structural D m eL z hzL hKz hHN h3
  exact ⟨hJK,component_reciprocal_residual_of_containment_at h structural m z.val hKz hHN eL hJK⟩

private theorem symmetricFour_cubic_residual :
    primeToResidual 3 (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  rw [←twoResidual_eq_primeToResidual_three,Theory.SpecificGroups.SymmetricFourResidual.residual_eq]
  rw [IsPiGroup_iff]
  intro p hp
  rw [Nat.card_perm,Nat.card_fin] at hp
  have hh : p.val ∣ 2 ^ 3 * 3 := hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp hh with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

private theorem residual_alternatingFour (C J Q : Subgroup G)
    (hJ : (primeToResidual 3 C).map C.subtype = J)
    (q : C →* Equiv.Perm (Fin 4)) (hq : Function.Surjective q)
    (hqk : q.ker = Q.subgroupOf C) :
    ∃ f : J →* alternatingGroup (Fin 4), Function.Surjective f ∧
      f.ker = Q.subgroupOf J := by
  let R := primeToResidual 3 C
  have hJC : J ≤ C := hJ ▸ map_subtype_le R
  have hr : R.map q = alternatingGroup (Fin 4) :=
    (map_primeToResidual_of_surjective 3 q hq).trans symmetricFour_cubic_residual
  let f : J →* alternatingGroup (Fin 4) :=
    (q.comp (inclusion hJC)).codRestrict _ (fun j => by
      rw [←hr]
      have hj := hJ.ge j.property
      obtain ⟨c,hc,he⟩ := hj
      have he' : c = inclusion hJC j := Subtype.ext he
      exact mem_map_of_mem q (he' ▸ hc))
  refine ⟨f,?_,?_⟩
  · intro a
    have ha : a.val ∈ R.map q := hr.symm ▸ a.property
    obtain ⟨c,hc,hca⟩ := ha
    exact ⟨⟨c.val,hJ.le (mem_map_of_mem C.subtype hc)⟩,Subtype.ext hca⟩
  · ext j
    change f j = 1 ↔ j.val ∈ Q
    rw [Subtype.ext_iff]
    change inclusion hJC j ∈ q.ker ↔ _
    rw [hqk]
    rfl

/-- The original five-dimensional short-block branch excludes the actual
doubled moved orbit. The K-side quotient and all residual normalization and
core-containment premises are constructed here from the source geometry. -/
theorem core_block_excludes_actual_doubled_component_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hJK : Solvable.firstCentralizerResidual L z.val ≤ K)
    (hb : ChapterC.IsShort L)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  let := h.quasisimple
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨eL⟩ := ordinary_original_of_linear_component_containment D m z hzL hJK eK
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point_at h₀ h structural m hzT hz1 hKz hTK hKM
  have hr := component_reciprocal_residual_of_containment_at h structural m z.val hKz hHN eL hJK
  rw [Solvable.firstCentralizerResidual_eq,hC] at hr
  have hJC : J ≤ K ⊓ centralizer ({w.val} : Set G) := by
    change Solvable.firstCentralizerResidual L z.val ≤ _
    rw [←hr]
    exact map_subtype_le _
  obtain ⟨_,hd⟩ := Solvable.firstCentralizerResidual_order_of_marking D m z hzL
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hd
  let A := zpowers (a : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,J.orderOf_coe a,ha]
  have hAJ : A ≤ J := zpowers_le.mpr a.property
  obtain ⟨p,hp,hpk⟩ := BinaryLinearThree.doubled_point_centralizer_symmetricFour K U A
    (normalizer_commutator_ge_right _ _) eK e he w hw hA
    (hAJ.trans hJK) (hAJ.trans (hJC.trans inf_le_right))
  obtain ⟨f,hf,hfk⟩ := residual_alternatingFour _ J (K.pCoreIn 2) hr p hp hpk
  exact core_block_excludes_doubled_component D m hb eL z hzL K U hJK
    (normalizer_commutator_ge_right _ _)
    (component_moved_le_twoCore h₀ hzT hz1 hKz hTK)
    (component_moved_normalizes_firstResidual_at h₀ h structural m hzT hz1 hKz hTK eL)
    eK e he f hf hfk

theorem core_block_excludes_doubled_without_containment_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  obtain ⟨eL⟩ := Solvable.ordinary_of_short_core_marking D m hb
  have hJK := (ordinary_doubled_component_residuals_at h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he).1
  exact core_block_excludes_actual_doubled_component_at h₀ h structural D m z hzT hzL
    hKz hHN hTK hKM hJK hb eK e he

private theorem twoThree_of_two_kernel_symmetric_four
    {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : IsPiGroup twoThreePrimes A := by
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hc : Nat.card A = 24 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Nat.card_perm,Nat.card_fin,hn]
    norm_num [Nat.factorial]
  rw [IsPiGroup_iff]
  intro p hp
  rw [hc] at hp
  change p.val = 2 ∨ p.val = 3
  have he : 24 * 2 ^ n = 2 ^ (n+3) * 3 := by ring
  rw [he] at hp
  rcases p.property.dvd_mul.mp hp with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

/-- The original L₁T is the full point centralizer inside KT, without
assuming the equality or discarding the outer action of T. -/
theorem ordinary_doubled_point_parabolic_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
      w ≠ 1 ∧ (T : Subgroup G) ≤ centralizer ({w.val} : Set G) ∧
      Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) =
        (K ⊔ (T : Subgroup G)) ⊓ centralizer ({w.val} : Set G) := by
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨w,hw,hTw,hX⟩ := component_fixed_generator_point_overgroup_at h₀ h structural m hzT hz1 hKz hTK hKM
  have hC : K ⊓ centralizer ({m.constant.val} : Set G) =
      K ⊓ centralizer ({w.val} : Set G) := by
    ext k
    exact ⟨fun hk => ⟨hk.1,(hX.le ⟨mem_sup_left hk.1,hk.2⟩).2⟩,
      fun hk => ⟨hk.1,(hX.ge ⟨mem_sup_left hk.1,hk.2⟩).2⟩⟩
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  obtain ⟨f,hf,hfk⟩ := BinaryLinearThree.doubled_point_centralizer_of_sylow K _
    (normalizer_commutator_ge_right _ _) eK e he w hw S (hS.trans hTw)
  have hp : IsPGroup 2 f.ker := by
    rw [hfk]
    exact (isPGroup_pCoreIn 2 K).comap_subtype
  have h23 := twoThree_of_two_kernel_symmetric_four f hf hp
  have hr := (ordinary_doubled_component_residuals_at h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he).2
  rw [Solvable.firstCentralizerResidual_eq,hC,←twoResidual_eq_primeToResidual_three h23] at hr
  refine ⟨w,hw,hTw,?_⟩
  rw [←hr]
  exact embedded_pointResidual_sup_sylow T K hTK w.val hTw

/-- The Baumann group of the original O₂(L₁T) is normalized by KT. -/
theorem ordinary_doubled_original_baumann_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ChapterB.baumann R = ChapterB.baumann ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let X := K ⊔ (T : Subgroup G)
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hUX : U ≤ X := hUK.trans le_sup_left
  let Ki := K.subgroupOf X
  let Ui := U.subgroupOf X
  let ek : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUX
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  let : Ui.Normal := hred.normal
  let : IsElementaryAbelian 2 Ui := hred.elementary
  let q0 := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let q := q0.comp ek.toMonoidHom
  have hq : Function.Surjective q :=
    (eK.surjective.comp (QuotientGroup.mk'_surjective _)).comp ek.surjective
  have hk : q.ker = pCore 2 Ki := by
    change q0.ker.comap ek.toMonoidHom = _
    have hq0 : q0.ker = pCore 2 K := by
      rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    rw [hq0]
    exact ek.toMonoidHom.comap_pCore_of_ker_isPGroup ek.surjective
      (IsPGroup.ker_isPGroup_of_injective ek.injective)
  let ei := eu.trans e
  have hei (k : Ki) (u : Ui) : (ei (MulAut.conjNormal k.val u)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (ei u).toAdd := by
    exact he (ek k) (eu u)
  have hquot : IsPGroup 2 (X ⧸ Ki) := by
    apply isPGroup_quotient_of_sup_eq_top Ki ((T : Subgroup G).subgroupOf X) T.isPGroup'.comap_subtype
    rw [←subgroupOf_sup (show K ≤ X from le_sup_left) (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  obtain ⟨w,hw,hTw,hPar⟩ := ordinary_doubled_point_parabolic_at h₀ h structural D m eL z hzT hzL
    hKz hHN hTK hKM eK e he
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eu hh)
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  let Si := S.mapSurjective (f := ek.symm.toMonoidHom) ek.symm.surjective
  have hSi : (Si : Subgroup Ki).map Ki.subtype ≤ centralizer ({wi.val} : Set X) := by
    rintro x ⟨a,ha,rfl⟩
    obtain ⟨k,hk,hka⟩ := (show a ∈ (S : Subgroup K).map ek.symm.toMonoidHom from ha)
    rw [←hka]
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTw (hS (mem_map_of_mem K.subtype hk))))
  have hb := ChapterB.doubled_overgroup_point_baumann Ki Ui q hq hk ei hei hquot
    (le_centralizer_iff.mp hred.le_centralizer_pCore) wi hwi Si hSi
  let C := centralizer ({wi.val} : Set X)
  have hCm : C.map X.subtype = Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [hPar]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hm := congrArg (fun A : Subgroup X => A.map X.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map X.subtype = (ChapterB.baumann (pCore 2 X)).map X.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective X.subtype X.subtype_injective,
    baumann_map_injective X.subtype X.subtype_injective,
    map_pCoreIn_of_injective 2 C X.subtype X.subtype_injective,hCm] at hm
  have hj := congrArg (fun A : Subgroup X => A.map X.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map X.subtype =
    (elementaryAbelianMaxJ (pCore 2 X)).map X.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    map_pCoreIn_of_injective 2 C X.subtype X.subtype_injective,hCm] at hj
  change ChapterB.baumann ((Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2) =
    ChapterB.baumann (X.pCoreIn 2) at hm
  refine ⟨hj,hm,?_⟩
  rw [hm]
  intro hbound
  exact hKM ((show K ≤ X from le_sup_left).trans ((X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      ((normalizer_le_normalizer_baumann (X.pCoreIn 2)).trans hbound)))

theorem ordinary_doubled_excluded_of_largeDistance_at
    {K : Subgroup G}
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  rcases ordinary_augmentation_baumann_alternative_of_largeDistance_at
      hl h structural D m eL z hzT hzL with hbound | hshort
  · exact (ordinary_doubled_original_baumann_at h₀ h structural D m eL z hzT hzL
      hKz hHN hTK hKM eK e he).2.2 hbound
  · exact core_block_excludes_doubled_without_containment_at h₀ h structural D m z hzT hzL
      hKz hHN hTK hKM hshort eK e he

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
