module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentDoubledAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredDoubled

/-!
# Excluding the covered doubled linear component at the original G,T

Project the original fixed generator to the actual doubled omega orbit.
Its S₄ point quotient has a two-group kernel. Cubic generation and the
original theta calculation identify R=O₂(L₁T) inside KR, preserving the
full kernel. The doubled point calculation makes K normalize Baum(R),
contradicting the original covered augmentation normalizer bound.

Together with the ordinary exclusion this removes the doubled alternative
for both original covering rows, using same-G,T structural facts.
ComponentLinearModuleAt uses the result to construct the chosen natural
module. Source: Aschbacher--Smith 13.4.10(2,4), pp.908--909.
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

private theorem nine_not_dvd_linear
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) : ¬ 9 ∣ Nat.card K := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  have he : Nat.card K = 168 * 2^n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),
      Nat.card_congr eK.toEquiv,Matrix.PSL3Two.card_SL,hn]
  rw [he]
  intro hd
  exact (by decide : ¬ 9 ∣ 168)
    (((by decide : Nat.Coprime 9 2).pow_right n).dvd_mul_right.mp hd)

private theorem twoThree_of_symmetric_four_kernel
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

/-- The doubled natural component normalizes the original covered Baumann
subgroup, by the actual Sylow-fixed point calculation inside KR. -/
theorem covered_doubled_original_baumann_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((K ⊔ R).pCoreIn 2) ∧
      ChapterB.baumann R = ChapterB.baumann ((K ⊔ R).pCoreIn 2) ∧
      K ≤ normalizer (ChapterB.baumann R : Set G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let Y := K ⊔ (T : Subgroup G)
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hRT : R ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).le_sylow_of_normalized T (le_sup_right.trans hPR)
  have hXY : X ≤ Y := sup_le le_sup_left (hRT.trans le_sup_right)
  have hYX : Y ≤ normalizer (X : Set G) := sup_le
    (le_sup_left.trans X.le_normalizer)
    ((le_inf hTK (le_sup_right.trans hPR)).trans (normalizer_inf_normalizer_le_normalizer_sup K R))
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hUX : U ≤ X := hUK.trans le_sup_left
  let Ki := K.subgroupOf X
  let Ui := U.subgroupOf X
  let ek : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUX
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer (hRT.trans hTK))
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  let : (U.subgroupOf Y).Normal := hred.normal
  have hYU : Y ≤ normalizer (U : Set G) := by
    have hn := (map_mono (f := Y.subtype)
      (show (⊤ : Subgroup Y) ≤ normalizer (U.subgroupOf Y : Set Y) from le_normalizer_of_normal)).trans
        ((U.subgroupOf Y).le_normalizer_map Y.subtype)
    rwa [←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (hUK.trans (show K ≤ Y from le_sup_left))] at hn
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer (hXY.trans hYU)
  let := hred.elementary
  let : IsElementaryAbelian 2 U := by
    have hh : IsElementaryAbelian 2 ((U.subgroupOf Y).map Y.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le (hUK.trans (show K ≤ Y from le_sup_left))] at hh
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.subgroupOf hUX
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
    apply isPGroup_quotient_of_sup_eq_top Ki (R.subgroupOf X)
      ((isPGroup_pCoreIn 2 P).comap_subtype)
    rw [←subgroupOf_sup (show K ≤ X from le_sup_left)
      (show R ≤ X from le_sup_right),subgroupOf_self]
  have hYcore : Y.pCoreIn 2 ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mp
    have hn := (map_mono (f := Y.subtype) hred.le_centralizer_pCore).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [map_subgroupOf_eq_of_le (hUK.trans (show K ≤ Y from le_sup_left))] at hn
  have hcore : pCore 2 X ≤ centralizer (Ui : Set X) := by
    intro x hx u hu
    exact Subtype.ext (hYcore
      ((pCoreIn_mono_of_normalizes hXY hYX) (mem_map_of_mem X.subtype hx)) u.val hu)
  obtain ⟨w,hw,hTw,hpoint⟩ := component_fixed_generator_point_overgroup_at h₀ h structural m
    hzT hz1 hKz hTK hKM
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
  have hb := ChapterB.doubled_overgroup_point_baumann Ki Ui q hq hk ei hei
    hquot hcore wi hwi Si hSi
  let C := centralizer ({wi.val} : Set X)
  have hCm : C.map X.subtype = X ⊓ centralizer ({m.constant.val} : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,(hpoint.ge ⟨hXY a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩).2⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp (hpoint.le ⟨hXY hx,hc⟩).2)),rfl⟩
  obtain ⟨f,hf,hfk⟩ := BinaryLinearThree.doubled_point_centralizer_of_sylow
    K U (normalizer_commutator_ge_right _ _) eK e he w hw S (hS.trans hTw)
  have hker : IsPGroup 2 f.ker := by
    rw [hfk]
    exact (isPGroup_pCoreIn 2 K).comap_subtype
  have h23 : IsPiGroup twoThreePrimes (K ⊓ normalizer (L : Set G) : Subgroup G) := by
    have hKC : K ⊓ normalizer (L : Set G) = K ⊓ centralizer ({w.val} : Set G) := by
      rw [←fixed_generator_centralizer_at h structural D m
        ⟨m.constant.property,m.constant_fixed⟩ (fun hh => m.constant_ne_one (Subtype.ext hh))]
      ext k
      exact ⟨fun hk => ⟨hk.1,(hpoint.le ⟨mem_sup_left hk.1,hk.2⟩).2⟩,
        fun hk => ⟨hk.1,(hpoint.ge ⟨mem_sup_left hk.1,hk.2⟩).2⟩⟩
    rw [hKC]
    exact twoThree_of_symmetric_four_kernel f hf hker
  have hRm : (C.pCoreIn 2).map X.subtype = R := by
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hCm]
    exact covered_component_point_radical_at h structural D m hc z hzT hzL hKz hHN h23
      (nine_not_dvd_linear eK)
  have hm := congrArg (fun A : Subgroup X => A.map X.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map X.subtype = (ChapterB.baumann (pCore 2 X)).map X.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective X.subtype X.subtype_injective,
    baumann_map_injective X.subtype X.subtype_injective,hRm] at hm
  have hj := congrArg (fun A : Subgroup X => A.map X.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map X.subtype =
    (elementaryAbelianMaxJ (pCore 2 X)).map X.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hRm] at hj
  change ChapterB.baumann R = ChapterB.baumann (X.pCoreIn 2) at hm
  refine ⟨hj,hm,?_⟩
  rw [hm]
  exact (show K ≤ X from le_sup_left).trans ((X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))).trans
      (normalizer_le_normalizer_baumann (X.pCoreIn 2)))

/-- The covered original augmentation row excludes the doubled natural component. -/
theorem covered_doubled_excluded_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  exact hKM ((covered_doubled_original_baumann_at h₀ h structural D m hc z hzT hzL
    hKz hHN hKM hTK eK e he).2.2.trans
      (covered_augmentation_baumann_normalizer_at h structural D m hc z hzT hzL))

/-- Both covering rows of the original augmentation exclude a doubled natural
component, with only the independent ordinary large-distance input retained. -/
theorem doubled_excluded_of_largeDistance_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) : False := by
  let := h.quasisimple
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (augmentationCentralQuotient D m) ho with hc | ⟨_,hc⟩
  · let eL := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hc
    exact ordinary_doubled_excluded_of_largeDistance_at hl h₀ h structural D m eL z hzT hzL
      hKz hHN hTK hKM eK e he
  · exact covered_doubled_excluded_at h₀ h structural D m hc z hzT hzL hKz hHN hKM hTK eK e he

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
