module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentContainment
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentChief
public import Theory.Representation.PSL3Two.DoubledPoint

/-!
# The actual reciprocal residual in the doubled component row

For the selected component K, its elementary omega-orbit centralizes the
original fixed line. Its moved subgroup U consequently normalizes the
original L₁=O^{3′}(C_L(z)) and lies in O₂(K). Splitting the full orbit
writes the fixed-line generator as a nonzero point of U times a K-fixed
factor, preserving its literal K-centralizer.

If L₁≤K and K/O₂(K)≅SL₃(2), cubic rank forces L/O₂(L)≅A₆.
Normal restriction then identifies L₁ with the reciprocal point residual.
A cubic of L₁ fixes the point just constructed, so its marked doubled
coordinates have S₄ stabilizer. Restricting this actual centralizer map
constructs the K-side A₄ quotient with the exact two-core kernel.
The final application contradicts the previously proved short-block chief
budget on the original five-dimensional V. It assumes no residual map,
normalization callback, or chosen-module minimality for U.

The source premises L₁≤K and IsShort L still require proof in this row.
In particular the existing four-dimensional NaturalSetup does not supply
13.2.2(7) for this augmentation core. These premises, the remaining module
rows and the comparison/commutator/graph assembly remain with
qt-d-1341-nonsolvable-source. Earlier 12.2/13.3 inputs retain their existing
producers and final discharge with qt-d-1341-fixed-core-source. Universal
nonsolvability remains separate at both escaping weights.

Source: Aschbacher–Smith, 13.4.10(2–4), printed pp.908–909;
13.2.2(7), printed pp.877–878, supplies the outstanding block alternative.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The original ordinary component is the literal cubic residual of its
normalizer. This also places reciprocal cubic residuals back in L. -/
theorem original_normalizer_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L := by
  let := h.quasisimple
  have hr := (h.source_normalizer_sqtk structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).stronglyQuasithin
      3 Nat.prime_three (by decide)
  exact (h.source_normalizer_component structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).map_primeToResidual_three_eq_of_quotient_alternating
      L.le_normalizer le_rfl (Or.inl rfl) eL hr

/-- Containment in a linear-three component already excludes the covered
original A₆ row. -/
theorem ordinary_original_of_linear_component_containment
    (D : ChosenModule T L V) (m : CoreMarking D)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (hJK : Solvable.firstCentralizerResidual L z.val ≤ K)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  have hr : primeRank 3 K ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_congr 3 eK]
    by_contra hn
    obtain ⟨E,_,hE⟩ := exists_elementary_nine_of_three_rank (by omega :
      2 ≤ primeRank 3 BinaryLinearThree.Group)
    have hd := E.card_subgroup_dvd_card
    rw [hE,Matrix.PSL3Two.card_SL] at hd
    norm_num at hd
  exact Solvable.ordinary_of_firstCentralizerResidual_threeRank D m z hz
    ((_root_.primeRank_le_of_injective 3 (inclusion hJK) (inclusion_injective _)).trans hr)

/-- Once the source L₁-containment is proved, its reciprocal residual is
literal, without requiring K to be the residual of the whole centralizer. -/
theorem component_reciprocal_residual_of_containment
    {D : ChosenModule T L V}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : G)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hJK : Solvable.firstCentralizerResidual L z ≤ K) :
    Solvable.firstCentralizerResidual K m.constant.val =
      Solvable.firstCentralizerResidual L z := by
  let H := centralizer ({z} : Set G)
  let M := normalizer (L : Set G)
  let C := H ⊓ M
  have hr := Solvable.firstCentralizerResidual_eq_intersection_residual z
    (original_normalizer_residual h structural eL)
  let N := K.subgroupOf C
  let : N.Normal := normal_subgroupOf_of_le_normalizer (inf_le_left.trans hHN)
  have hRN : primeToResidual 3 C ≤ N := by
    intro c hc
    exact hJK (hr ▸ mem_map_of_mem C.subtype hc)
  have he := congrArg (map C.subtype)
    (embedded_primeToResidual_eq_of_normal 3 N hRN)
  rw [map_embedded_primeToResidual_of_hom,subgroupOf_map_subtype] at he
  have hi : K ⊓ C = K ⊓ M := le_antisymm
    (inf_le_inf_left _ inf_le_right)
    (le_inf inf_le_left (le_inf (inf_le_left.trans hKz) inf_le_right))
  rw [hi] at he
  have hd : centralizer ({m.constant.val} : Set G) = M :=
    fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))
  rw [Solvable.firstCentralizerResidual_eq,hd]
  exact he.trans hr

/-- The actual elementary omega-orbit centralizes the original fixed line.
Consequently its moved subgroup normalizes the literal original residual. -/
theorem component_moved_normalizes_firstResidual
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    have hdW : m.constant.val ∈ W := le_conjugateSpanBy _ _
      (m.constant_mem_central_four h structural).2
    intro w hw
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨w,hw⟩ : W) ⟨m.constant.val,hdW⟩)
  have hr := Solvable.firstCentralizerResidual_eq_intersection_residual z
    (original_normalizer_residual h structural eL)
  rw [←hr]
  exact (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z K)).trans
    (hWC.trans (C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))))

/-- The moved orbit lies in the actual two-core of the selected component. -/
theorem component_moved_le_twoCore
    (h₀ : Hypothesis1331 T L) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ≤ K.pCoreIn 2 := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K
  let X := K ⊔ (T : Subgroup G)
  let U := ⁅W,K⁆
  have hWX : W ≤ X := conjugateSpanBy_le
    ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from fun _ hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans X.le_normalizer)
  have hUK : U ≤ K := le_normalizer_iff_commutator_le_right.mp
    (hWX.trans (sup_le K.le_normalizer hTK))
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  let := hred.elementary
  have hp : IsPGroup 2 U := by
    have hh : IsPGroup 2 ((U.subgroupOf X).map X.subtype) :=
      (IsElementaryAbelian.isPGroup 2 (U.subgroupOf X)).map X.subtype
    rwa [map_subgroupOf_eq_of_le (hUK.trans le_sup_left)] at hh
  exact le_pCoreIn_of_normalizes hp hUK (normalizer_commutator_ge_right W K)

/-- The reciprocal fixed-line centralizer is the point centralizer of an
actual nonzero vector of the moved orbit, even in the doubled case. -/
theorem component_fixed_generator_point
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G)) :
    ∃ w : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G),
      w ≠ 1 ∧ K ⊓ centralizer ({m.constant.val} : Set G) =
        K ⊓ centralizer ({w.val} : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z K
  let U := ⁅W,K⁆
  let C := Z ⊓ centralizer (K : Set G)
  let X := K ⊔ (T : Subgroup G)
  have hWX : W ≤ X := conjugateSpanBy_le
    ((show Z ≤ (T : Subgroup G) from fun _ hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans X.le_normalizer)
  have hred := component_orbit_reduced h₀ hzT hz1 hKz hTK
  let := hred.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf X).map X.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  have hUW : U ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z K)
  have hCW : C ≤ W := inf_le_left.trans (le_conjugateSpanBy Z K)
  have hsplit : W = U ⊔ C := component_seed_split h₀ hzT hz1 hKz hTK
  have hdW : m.constant.val ∈ W := le_conjugateSpanBy _ _
    (m.constant_mem_central_four h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hs : U.subgroupOf W ⊔ C.subgroupOf W = ⊤ := by
    rw [←subgroupOf_sup hUW hCW,←hsplit,subgroupOf_self]
  let : (U.subgroupOf W).Normal := normal_of_isMulCommutative _
  obtain ⟨a,ha,c,hc,hac⟩ := mem_sup_of_normal_left.mp
    (show (⟨m.constant.val,hdW⟩ : W) ∈ U.subgroupOf W ⊔ C.subgroupOf W from
      hs ▸ mem_top _)
  have he : a.val * c.val = m.constant.val := congrArg Subtype.val hac
  refine ⟨⟨a.val,ha⟩,?_,?_⟩
  · intro ha1
    have hh : a.val = 1 := congrArg Subtype.val ha1
    rw [hh,one_mul] at he
    exact hdK (he ▸ hc.2)
  · ext k
    constructor
    · rintro ⟨hk,hd⟩
      refine ⟨hk,mem_centralizer_singleton_iff.mpr ?_⟩
      have hck : k * c.val = c.val * k := hc.2 k hk
      have hh := mem_centralizer_singleton_iff.mp hd
      rw [←he] at hh
      have hh' : (k * a.val) * c.val = (a.val * k) * c.val := by
        simpa only [mul_assoc,←hck] using hh
      exact mul_right_cancel hh'
    · rintro ⟨hk,ha⟩
      refine ⟨hk,mem_centralizer_singleton_iff.mpr ?_⟩
      rw [←he]
      have hck : k * c.val = c.val * k := hc.2 k hk
      calc
        k * (a.val * c.val) = (k * a.val) * c.val := (mul_assoc _ _ _).symm
        _ = (a.val * k) * c.val := by rw [mem_centralizer_singleton_iff.mp ha]
        _ = a.val * (c.val * k) := by rw [mul_assoc,hck]
        _ = (a.val * c.val) * k := (mul_assoc _ _ _).symm

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
theorem core_block_excludes_actual_doubled_component
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hKz hTK hKM
  have hr := component_reciprocal_residual_of_containment h structural m z.val hKz hHN eL hJK
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
    (component_moved_normalizes_firstResidual h₀ h structural m hzT hz1 hKz hTK eL)
    eK e he f hf hfk

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
