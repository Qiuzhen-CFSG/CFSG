module

public import Stellmacher.SectionOne.OneSevenSupportTransitivity
public import Stellmacher.SectionOne.OneSevenFactorOrbitTransitivity
public import Stellmacher.SectionOne.OneSevenBaumann
public import Stellmacher.SectionOne.TwoFactorInvolutionPlaneAlgebra

/-!
# Canonical coordinates for two exchanged factors

The canonical global product identifies the Baumann subgroup with the Sylow
intersection. It therefore preserves each canonical factor. Sylow transitivity
and the supplied complement force its nonidentity element to exchange the two
factors. The module product and absence of global fixed vectors give two
complementary order-four supports for this literal action.

The coordinate action-line theorem gives a nontrivial order-two displacement
on each support. Two-group orbit parity then forces its base-fixed subgroup
to have order two, without assuming that an exchanged factor is ambient-normal.
Together with the intrinsic support transitivity theorem, these facts produce
every field needed by the involution-plane algebra of Stellmacher (9.3),
printed p50 of `refs/files/stellmacher-n-group.pdf`.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

universe u

private theorem support_fixed_card_of_commutator_card_two
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (B : Subgroup K) (support : Subgroup V) [IsInvariant B V support]
    (hB : IsPGroup 2 B) (hcard : Nat.card support = 4)
    (hcomm : Nat.card (commutatorSubgroup B V support) = 2) :
    Nat.card (support ⊓ FixedPoints.subgroup B V : Subgroup V) = 2 := by
  have hmap : Nat.card (support ⊓ FixedPoints.subgroup B V : Subgroup V) =
      Nat.card (FixedPoints.subgroup B support) := by
    rw [← fixedPoints_subgroup_map_subtype_eq_inf support,
      Subgroup.card_map_of_injective support.subtype_injective]
  have hge : 2 ≤ Nat.card (FixedPoints.subgroup B support) := by
    have hparity := hB.card_modEq_card_fixedPoints support
    change Nat.card support % 2 = Nat.card (FixedPoints.subgroup B support) % 2 at hparity
    rw [hcard] at hparity
    have hpos : 0 < Nat.card (FixedPoints.subgroup B support) := Nat.card_pos
    omega
  have hnot : ¬ support ≤ FixedPoints.subgroup B V := by
    intro hfix
    have hbot : commutatorSubgroup B V support = ⊥ := by
      apply le_bot_iff.mp
      apply (Subgroup.closure_le _).mpr
      rintro vector ⟨actor, source, hsource, rfl⟩
      change source⁻¹ * (actor • source) = 1
      rw [hfix hsource actor, inv_mul_cancel]
    have hone := Subgroup.card_eq_one.mpr hbot
    omega
  have hlt : Nat.card (support ⊓ FixedPoints.subgroup B V : Subgroup V) < 4 := by
    have hle := Subgroup.card_le_of_le
      (inf_le_left : support ⊓ FixedPoints.subgroup B V ≤ support)
    rw [hcard] at hle
    by_contra hlarge
    have heq := Subgroup.eq_of_le_of_card_ge
      (inf_le_left : support ⊓ FixedPoints.subgroup B V ≤ support)
      (by rw [hcard]; omega)
    exact hnot (heq ▸ inf_le_right)
  have hdvd : Nat.card (support ⊓ FixedPoints.subgroup B V : Subgroup V) ∣ 4 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [hmap] at hlt hdvd ⊢
  interval_cases hsize : Nat.card (FixedPoints.subgroup B support) <;> omega

public theorem oneSeven_two_factor_action_coordinates
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (S : Sylow 2 K)
    (hgen : oneE (V := V) (S : Subgroup K) ⊔ (S : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup K) ⊤)
    (hfixed : FixedPoints.subgroup (oneE (V := V) (S : Subgroup K)) V = ⊥)
    (hcount : (oneSevenFactors (G := K) (V := V)).card = 2)
    (Y : Subgroup K) (hYS : Y ≤ (S : Subgroup K)) (hYcard : Nat.card Y = 2)
    (hSY : (S : Subgroup K) = oneB (V := V) (S : Subgroup K) ⊔ Y) :
    Nonempty (SwappedFactorActionCoordinates (V := V)
      (oneB (V := V) (S : Subgroup K)) Y) := by
  classical
  let E := oneSevenGenerated (G := K) (V := V)
  let B := oneB (V := V) (S : Subgroup K)
  obtain ⟨hEnormal, hproduct, _⟩ := oneSeven_global_product h S
  have hB : B = (S : Subgroup K) ⊓ E :=
    (oneSeven_baumann_eq_j h S).trans (oneSeven_global_identification h S).1
  have hEfixed : FixedPoints.subgroup E V = ⊥ := by
    rwa [(oneSeven_global_identification h S).2] at hfixed
  obtain ⟨D, F, hne, hfactors⟩ := Finset.card_eq_two.mp hcount
  have hDmem : D ∈ oneSevenFactors (G := K) (V := V) := by rw [hfactors]; simp
  have hFmem : F ∈ oneSevenFactors (G := K) (V := V) := by rw [hfactors]; simp
  have hD := (mem_oneSevenFactors_iff D).mp hDmem
  have hF := (mem_oneSevenFactors_iff F).mp hFmem
  have hDE : D ≤ E := le_sSup hD
  have hFE : F ≤ E := le_sSup hF
  have hED : E ≤ Subgroup.normalizer (D : Set K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp (hproduct.2.1 D hDmem)
  have hBD : B ≤ Subgroup.normalizer (D : Set K) := by
    rw [hB]
    exact inf_le_right.trans hED
  have hswap : ∃ swap : Y, D.conjBy (swap : K) ≠ D := by
    by_contra hnone
    have hYnorm : Y ≤ Subgroup.normalizer (D : Set K) := by
      intro actor hactor
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      exact not_not.mp (fun hmove => hnone ⟨⟨actor, hactor⟩, hmove⟩)
    have hSnorm : (S : Subgroup K) ≤ Subgroup.normalizer (D : Set K) := by
      rw [hSY]
      exact sup_le hBD hYnorm
    obtain ⟨actor, hactor⟩ := oneSeven_factor_orbit_transitive h S hgen hunique
      D hDmem F hFmem
    exact hne ((Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hSnorm actor.property)).symm.trans hactor)
  obtain ⟨swap, hswapne, huniqueY⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hYcard
  have hswap : D.conjBy (swap : K) ≠ D := by
    obtain ⟨moving, hmoving⟩ := hswap
    have hmovingne : moving ≠ 1 := by
      intro heq
      apply hmoving
      simp only [heq, OneMemClass.coe_one, Subgroup.conjBy_one]
    rwa [huniqueY moving hmovingne] at hmoving
  have hswapF : D.conjBy (swap : K) = F := by
    have hmem := (mem_oneSevenFactors_iff _).mpr (hD.conjBy D (swap : K))
    rw [hfactors] at hmem
    exact (Finset.mem_insert.mp hmem).resolve_left hswap |> Finset.mem_singleton.mp
  have hEgen : E = D ⊔ F := by
    apply le_antisymm
    · apply sSup_le
      intro factor hfactor
      have hmem := (mem_oneSevenFactors_iff _).mpr hfactor
      rw [hfactors] at hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact le_sup_left
      · have heq := Finset.mem_singleton.mp hmem
        rw [heq]
        exact le_sup_right
    · exact sup_le hDE hFE
  let family : Fin 2 → Subgroup K := ![D, F]
  have hfamily (index : Fin 2) : IsOneSevenFactor (V := V) (family index) := by
    fin_cases index
    · exact hD
    · exact hF
  have hfamilymem (index : Fin 2) : family index ∈ oneSevenFactors (G := K) (V := V) :=
    (mem_oneSevenFactors_iff _).mpr (hfamily index)
  have hinj : Function.Injective family := by
    intro index other heq
    fin_cases index <;> fin_cases other <;> simp [family] at heq ⊢ <;>
      first | contradiction | exact (hne heq.symm).elim
  have hfamilygen : E = ⨆ index, family index := by
    rw [hEgen]
    apply le_antisymm
    · exact sup_le (le_iSup family 0) (le_iSup family 1)
    · apply iSup_le
      intro index
      fin_cases index
      · exact le_sup_left
      · exact le_sup_right
  have hfamilyprod : IsInternalDirectProductFamily E family := by
    refine ⟨hfamilygen, ?_, ?_⟩
    · intro index other hdistinct
      exact hproduct.2.2.1 _ (hfamilymem index) _ (hfamilymem other)
        (fun heq => hdistinct (hinj heq))
    · intro index other hdistinct
      exact hproduct.2.2.2 _ (hfamilymem index) _ (hfamilymem other)
        (fun heq => hdistinct (hinj heq))
  have hmodule := oneSevenFactor_module_product h family hfamily hinj E hfamilygen
  have hdisj : Disjoint (commutatorAction D V) (commutatorAction F V) := by
    exact hmodule.2.1 (some 0) (some 1) (by decide)
  have hspan : commutatorAction D V ⊔ commutatorAction F V = ⊤ := by
    have hspan := hmodule.1
    rw [iSup_option, hEfixed, bot_sup_eq] at hspan
    apply top_unique
    rw [hspan]
    apply iSup_le
    intro index
    fin_cases index
    · exact le_sup_left
    · exact le_sup_right
  have hsupportmap : (commutatorAction D V).map
      (MulDistribMulAction.toMulAut K V (swap : K)).toMonoidHom =
      commutatorAction F V := by
    rw [RankOneThreeGroupAssembly.commutatorAction_conjBy, hswapF]
  let _ : IsInvariant B V (commutatorAction D V) :=
    commutatorAction_isInvariant_of_normalizing_actor B D hBD
  have hBtwo : IsPGroup 2 B := S.isPGroup'.of_injective
    (Subgroup.inclusion (show B ≤ (S : Subgroup K) by rw [hB]; exact inf_le_left))
    (Subgroup.inclusion_injective _)
  have hsupports : Pairwise fun index other =>
      Disjoint (commutatorAction (family index) V) (commutatorAction (family other) V) := by
    intro index other hdistinct
    exact hmodule.2.1 (some index) (some other) (by simpa using hdistinct)
  have hline := oneSevenFactor_sylow_coordinate_action_lines h.action_faithful
    S E hEnormal family hfamilyprod hfamily hsupports 0
  have hcommcard : Nat.card (commutatorSubgroup B V (commutatorAction D V)) = 2 := by
    rw [hB]
    change Nat.card (commutatorSubgroup (↥((S : Subgroup K) ⊓ E)) V
      (commutatorAction (family 0) V)) = 2
    rw [hline.1]
    exact hline.2
  refine ⟨{
    swap := swap
    swap_ne_one := hswapne
    support := commutatorAction D V
    factor := D
    support_card := hD.2.2.1
    support_disjoint := by rw [hsupportmap]; exact hdisj
    support_span := by rw [hsupportmap]; exact hspan
    factor_cross_fixed := ?_
    factor_conjugate_commute := ?_
    factor_transitive := oneSevenFactor_support_transitive D hD
    base_preserves := ?_
    swap_normalizes_base := ?_
    base_fixed_card := support_fixed_card_of_commutator_card_two B
      (commutatorAction D V) hBtwo hD.2.2.1 hcommcard }⟩
  · intro actor hactor vector hvector
    have hmoved : (swap : K) • vector ∈ commutatorAction F V := by
      rw [← hsupportmap]
      exact ⟨vector, hvector, rfl⟩
    exact (oneSevenFactor_commutatorAction_le_fixedPoints h D F hD hF hne hmoved)
      ⟨actor, hactor⟩
  · intro actor hactor
    apply (oneSevenFactor_eq_or_commute h D F hD hF).resolve_left hne actor hactor
    rw [← hswapF]
    exact ⟨actor, hactor, rfl⟩
  · intro actor hactor vector hvector
    exact (IsInvariant.invariant (A := B) (H := commutatorAction D V)
      ⟨actor, hactor⟩ vector).mp hvector
  · intro actor hactor
    change (swap : K)⁻¹ * actor * (swap : K) ∈ B
    change actor ∈ B at hactor
    rw [hB] at hactor ⊢
    exact ⟨S.mul_mem (S.mul_mem (S.inv_mem (hYS swap.property)) hactor.1)
      (hYS swap.property), by simpa using hEnormal.conj_mem actor hactor.2 (swap : K)⁻¹⟩

end Stellmacher.SectionOne
