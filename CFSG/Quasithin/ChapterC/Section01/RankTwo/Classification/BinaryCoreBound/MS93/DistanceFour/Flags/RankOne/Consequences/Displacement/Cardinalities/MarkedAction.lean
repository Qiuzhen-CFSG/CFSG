module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Cardinalities.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison.MarkedAction

/-!
# Small invariant sections for the marked MS93 action

A subgroup D of Z_alpha of order at most four, noncentral in the vertex
stabilizer and invariant modulo the literal central denominator, has order
four and intersects the vertex center trivially.

The marked fixed-plane calculation supplies the essential representation
input: residual-fixed elements of Z_beta are central. The intrinsic marked
core lies in the residual times Q_alpha, so every residual-fixed element
of Z_alpha already lies in Z_beta. If a residual-invariant section of
Z_alpha has central quotient of order two, its commutator lies in the
central denominator. Finite-parabolic commutator idempotence then makes
the whole section fixed, contradicting noncentrality. The relative-index
formula and two-group order leave index and order four, with trivial kernel.
All normality and finiteness are local to the vertex stabilizer.

The natural action compatibility theorem retains the supplied quotient
marking and equivariance, and the invariance equivalence identifies the
normalizer premise with the constructed edgeRadiusAction. The proof uses
the existing marked plane and core calculations for both flag orientations;
no independent matrix action or additional representation premise is chosen.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the first paragraph of (4.6.9), printed p.908, using the earlier
edge orders and indices on pp.902--903. The displacement and critical-path
assembly remains in the parent Cardinalities development.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem Z_alpha_le_edgeRadius : Z R (alpha R) ≤ V R (beta R) := by
  have he : (cosetGraph R).dist (alpha R) (beta R) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (base_adjacent R))
  exact le_iSup_of_le (alpha R) (le_iSup_of_le (show
    (cosetGraph R).dist (alpha R) (beta R) ≤ 2 by omega) le_rfl)

/-- The edge-radius action restricts to the supplied natural representation,
with exactly its original quotient map and marking. -/
theorem edgeRadiusAction_on_marked_natural [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (m : M) (hm : m ∈ parabolic source.projection source.flag i)
    (u : U R (alpha R)) :
    ∃ v : U R (alpha R),
      (v : FreeAmalgam R) =
        (edgeRadiusAction source geometry common.large_distance i hkernel
          ⟨embedM R m, mem_map_of_mem (embedM R) hm⟩
          ⟨u, by exact Z_alpha_le_edgeRadius (U_le_Z _ u.property)⟩ : FreeAmalgam R) ∧
      (common.natural.equiv v).toAdd =
        (common.natural.marking (source.projection m)).val.mulVec
          (common.natural.equiv u).toAdd := by
  let v : U R (alpha R) := ⟨_, le_normalizer_iff.mp common.natural.normalized
    _ (show embedM R m ∈ Mbar R from ⟨m, rfl⟩) _ u.property⟩
  refine ⟨v, ?_, common.natural.action m u v rfl⟩
  rw [edgeRadiusAction_apply]

/-- For subgroups of Z_alpha, the normalization premise is precisely invariance
under the already constructed edge-radius conjugation action. -/
theorem flag_normalizes_section_iff_edgeRadiusAction [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ Z R (alpha R)) :
    flagResidual source i ≤ normalizer (Y : Set (FreeAmalgam R)) ↔
      ∀ (p : flagResidual source i) (x : V R (beta R)),
        (edgeRadiusAction source geometry hlarge i hkernel
          ⟨p, flagResidual_le source i p.property⟩ x : FreeAmalgam R) ∈ Y ↔
            (x : FreeAmalgam R) ∈ Y := by
  constructor
  · intro hn p x
    rw [edgeRadiusAction_apply]
    exact (mem_normalizer_iff.mp (hn p.property) x).symm
  · intro ha
    apply le_normalizer_iff.mpr
    intro p hp y hy
    have hyV : y ∈ V R (beta R) := Z_alpha_le_edgeRadius (hYZ hy)
    have hh := (ha ⟨p, hp⟩ ⟨y, hyV⟩).mpr hy
    rwa [edgeRadiusAction_apply] at hh

/-- Fixed elements of the selected residual in Z_alpha are central in the whole vertex group. -/
theorem flag_fixed_Z_le_center [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) :
    Z R (alpha R) ⊓ centralizer (flagResidual source i : Set (FreeAmalgam R)) ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  rintro z ⟨hz, hc⟩
  have hQ : Q R (alpha R) ≤ centralizer ({z} : Set (FreeAmalgam R)) := by
    intro q hq
    exact mem_centralizer_singleton_iff.mpr
      ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R _ rfl)) hz q hq)
  have hH : flagResidual source i ≤ centralizer ({z} : Set (FreeAmalgam R)) := by
    intro h hh
    exact mem_centralizer_singleton_iff.mpr (hc h hh)
  have hT : Q R (beta R) ≤ centralizer ({z} : Set (FreeAmalgam R)) :=
    (hkernel ▸ flagKernel_le_residual_sup_vertexKernel source i).trans (sup_le hH hQ)
  have hzβ : z ∈ Z R (beta R) := by
    rw [Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]
    exact ⟨hz, fun q hq => mem_centralizer_singleton_iff.mp (hT hq)⟩
  exact (edgeFixedLayerAction source geometry common early i hkernel).2 ⟨hzβ, hc⟩

private theorem flag_invariant_two_idempotent [Finite M] (source : LocalSource L R)
    (i : Bool) (Y : Subgroup (FreeAmalgam R)) (hYP : Y ≤ flagParabolic source i)
    (hp : IsPGroup 2 Y)
    (hn : flagResidual source i ≤ normalizer (Y : Set (FreeAmalgam R))) :
    ⁅⁅Y, flagResidual source i⁆, flagResidual source i⁆ = ⁅Y, flagResidual source i⁆ := by
  let P := flagParabolic source i
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion (flagParabolic_le source i))
    (inclusion_injective _)
  let W := Y.subgroupOf P
  have hW : W.map P.subtype = Y := map_subgroupOf_eq_of_le hYP
  have hres : (pResidual 2 P).map P.subtype = flagResidual source i :=
    (flagResidual_eq source i).symm
  have hWN : pResidual 2 P ≤ normalizer (W : Set P) := by
    apply le_normalizer_iff.mpr
    intro h hh w hw
    exact le_normalizer_iff.mp hn h (hres ▸ mem_map_of_mem P.subtype hh) w hw
  have hi := commutator_isPPerfect_idempotent (pResidual 2 P) W
    (isPPerfect_pResidual 2) hp.comap_subtype hWN
  have hm := congrArg (Subgroup.map P.subtype) hi
  simpa only [map_commutator, hW, hres] using hm

/-- The source marked residual excludes central quotients of order two in Z_alpha. -/
theorem flag_noncentral_section_index_ne_two [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ Z R (alpha R))
    (hn : flagResidual source i ≤ normalizer (Y : Set (FreeAmalgam R)))
    (hnot : ¬ Y ≤ (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ((centralDenominator (alpha R)).map (stabilizer R (alpha R)).subtype).relIndex Y ≠ 2 := by
  let N := (centralDenominator (alpha R)).map (stabilizer R (alpha R)).subtype
  let H := flagResidual source i
  have hH : H ≤ stabilizer R (alpha R) :=
    (flagResidual_le source i).trans (flagParabolic_le source i)
  have hNC : N ≤ centralizer (H : Set (FreeAmalgam R)) := by
    change (centralDenominator (alpha R)).map (stabilizer R (alpha R)).subtype ≤ _
    rw [centralDenominator_map]
    rintro z ⟨_, c, hc, rfl⟩ h hh
    exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨h, hH hh⟩)
  have hHN : H ≤ normalizer (N : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp hNC).trans (Subgroup.centralizer_le_normalizer _)
  intro hindex
  have hcomm : ⁅Y, H⁆ ≤ N :=
    commutator_le_of_normalized_index_two Y (Y ⊓ N) H inf_le_left
      (by rw [inf_relIndex_left]; exact hindex) hn
      (le_normalizer_inf hn hHN) |>.trans inf_le_right
  have hZQ : Z R (alpha R) ≤ Q R (alpha R) := by
    rw [← common.X_eq_Z _ rfl]
    exact omegaCenter_le _
  have hYP : Y ≤ flagParabolic source i :=
    hYZ.trans (hZQ.trans ((Q_le_adjacent_h R rfl (base_adjacent R)).trans
      (hkernel ▸ flagKernel_le source i)))
  have hp : IsPGroup 2 Y :=
    (Q_isPGroup R source.two_group source.core_le (alpha R) rfl).to_le (hYZ.trans hZQ)
  have hi := flag_invariant_two_idempotent source i Y hYP hp hn
  have hzero : ⁅Y, H⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hi]
    exact (commutator_mono hcomm le_rfl).trans
      (by rw [commutator_eq_bot_iff_le_centralizer.mpr hNC])
  apply hnot
  exact (le_inf hYZ (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans
    (flag_fixed_Z_le_center source geometry common early i hkernel)

/-- Every noncentral small section invariant modulo the literal central denominator
has order four and meets the whole vertex center trivially. -/
theorem marked_small_invariant_section [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (D : Subgroup (FreeAmalgam R)) (hDZ : D ≤ Z R (alpha R))
    (hcard : Nat.card D ≤ 4)
    (hnot : ¬ D ≤ (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hn : flagResidual source i ≤ normalizer
      ((D ⊔ (centralDenominator (alpha R)).map (stabilizer R (alpha R)).subtype :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    Nat.card D = 4 ∧ Disjoint D
      ((center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) := by
  let G := stabilizer R (alpha R)
  let C := (center G).map G.subtype
  let N := (centralDenominator (alpha R)).map G.subtype
  let K := D ⊔ N
  have hN : N = Z R (alpha R) ⊓ C := centralDenominator_map _
  have hNZ : N ≤ Z R (alpha R) := hN ▸ inf_le_left
  have hNC : N ≤ C := hN ▸ inf_le_right
  have hKZ : K ≤ Z R (alpha R) := sup_le hDZ hNZ
  have hZG : Z R (alpha R) ≤ G := Z_le_stabilizer R _
  have hDG := hDZ.trans hZG
  have hNG := hNZ.trans hZG
  let := finite_stabilizer R (alpha R)
  let : Finite D := Finite.of_injective (inclusion hDG) (inclusion_injective _)
  have hNN : (N.subgroupOf G).Normal := by
    have he : N.subgroupOf G = centralDenominator (alpha R) := by
      dsimp [N, G]
      exact comap_map_eq_self_of_injective (stabilizer R (alpha R)).subtype_injective _
    rw [he]
    exact centralDenominator_normal geometry _
  let := hNN
  have hindex : N.relIndex K = N.relIndex D := by
    have he := relIndex_sup_right (D.subgroupOf G) (N.subgroupOf G)
    rw [← subgroupOf_sup hDG hNG, relIndex_subgroupOf (hKZ.trans hZG),
      relIndex_subgroupOf hDG] at he
    exact he
  have hne1 : N.relIndex D ≠ 1 := by
    intro h
    exact hnot ((relIndex_eq_one.mp h).trans hNC)
  have hne2 : N.relIndex D ≠ 2 := by
    rw [← hindex]
    exact flag_noncentral_section_index_ne_two source geometry common early i hkernel K hKZ hn
      (fun hc => hnot (le_sup_left.trans hc))
  have hZQ : Z R (alpha R) ≤ Q R (alpha R) := by
    rw [← common.X_eq_Z _ rfl]
    exact omegaCenter_le _
  have hp : IsPGroup 2 D :=
    (Q_isPGroup R source.two_group source.core_le (alpha R) rfl).to_le (hDZ.trans hZQ)
  have hd : Nat.card D = 1 ∨ Nat.card D = 2 ∨ Nat.card D = 4 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra! hh
      have he : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hh
      omega
    interval_cases n
    · exact Or.inl hn
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr hn)
  have hcount := (N.subgroupOf D).index_mul_card
  change N.relIndex D * Nat.card (N.subgroupOf D) = Nat.card D at hcount
  have hfour : Nat.card D = 4 := by
    rcases hd with h | h | h
    · have hdvd := N.relIndex_dvd_card D
      rw [h] at hdvd
      exact (hne1 (Nat.dvd_one.mp hdvd)).elim
    · have hdvd := N.relIndex_dvd_card D
      rw [h] at hdvd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdvd with hh | hh
      · exact (hne1 hh).elim
      · exact (hne2 hh).elim
    · exact h
  have hindex4 : N.relIndex D = 4 := by
    have hdvd := N.relIndex_dvd_card D
    rw [hfour] at hdvd
    have hm : N.relIndex D ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.resolve_left hne1 |>.resolve_left hne2
  have hbot : N.subgroupOf D = ⊥ := card_eq_one.mp (by rw [hfour, hindex4] at hcount; omega)
  refine ⟨hfour, disjoint_def.mpr ?_⟩
  intro d hd hdc
  have hdN : d ∈ N := hN ▸ ⟨hDZ hd, hdc⟩
  have hh : (⟨d, hd⟩ : D) ∈ N.subgroupOf D := hdN
  rw [hbot] at hh
  exact congrArg Subtype.val (mem_bot.mp hh)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
