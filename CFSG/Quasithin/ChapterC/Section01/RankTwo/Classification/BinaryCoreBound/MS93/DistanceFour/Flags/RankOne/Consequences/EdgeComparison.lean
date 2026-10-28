module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison.MarkedAction

/-!
# The MS93 edge-generator comparison

For a neighbor t of beta, the index-two quotient Z_t/Z_beta puts
[Z_t,Q_beta] in Z_beta. The residual displacement bound already proved
in Residual lies in every neighboring Z-layer. Thus the selected marked
residual normalizes Z_t and its commutator with the edge kernel.

For t in nu(alpha), centrality of [Z_t,Q_beta] would put Z_t in the
literal quotient centralizer Bzero. The explicit equality Bzero = B_alpha
contradicts nu. EarlyFacts supplies the order four. These deductions reduce
the comparison to uniqueness of a noncentral invariant four-group in Z_beta.
Coprime commutator idempotence in the finite marked parabolic proves the
required uniqueness once its moving subgroup and fixed points in Z_beta
are identified. MarkedAction constructs both action facts from CommonFacts
and EarlyFacts using the actual marked natural subgroup and parabolic.
The final theorem discharges these action premises, retaining the explicit
equality Bzero = B_alpha for the separate displacement argument to supply.

All normality is relative to the original embedded parabolic, and the
free amalgam is not assumed finite. No core containment or radius conclusion
is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The quotient Z_t/Z_beta of order two has trivial edge-kernel action. -/
theorem edgeGenerator_le_edge_Z (geometry : Geometry R)
    (early : EarlyFacts R geometry) (t : Vertex R)
    (ht : color R t = false) (hbt : Adjacent R (beta R) t) :
    ⁅Z R t, Q R (beta R)⁆ ≤ Z R (beta R) := by
  have hZ : Z R (beta R) = omegaCenter (Q R (beta R)) := by
    rw [Z, if_neg (show color R (beta R) ≠ false by change true ≠ false; decide)]
    rfl
  apply commutator_le_of_normalized_index_two _ _ _
    (edge_Z_le t (beta R) ht (adjacent_symm R hbt))
    (early.edge_Z_index t (beta R) ht (adjacent_symm R hbt))
    ((show Q R (beta R) ≤ stabilizer R t from fun _ hx => hx.2 t hbt).trans
      (Z_normalized R t))
  rw [hZ]
  intro q hq
  rw [mem_normalizer_iff_map_conj_eq, ← omegaCenter_map _ _ (MulAut.conj q).injective,
    mem_normalizer_iff_map_conj_eq.mp ((Q R (beta R)).le_normalizer hq)]

/-- Centrality of an edge generator contradicts the defining noncontainment in nu. -/
theorem edgeGenerator_noncentral [Finite M] (geometry : Geometry R)
    (early : EarlyFacts R geometry) (hlarge : 2 < geometry.b R)
    (hzero : Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)))
    (t : Vertex R) (ht : nu R geometry (alpha R) t) :
    ¬ ⁅Z R t, Q R (beta R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  intro hc
  apply ht.2
  rw [← hzero]
  have hZV : Z R t ≤ V R (alpha R) :=
    le_iSup_of_le t (le_iSup_of_le ht.1.le le_rfl)
  have hVQ := V_le_Q geometry hlarge (alpha R) rfl
  apply (le_Bzero_iff geometry (alpha R)
    (geometry.V_local (alpha R) rfl hlarge) _).mpr
  refine ⟨hZV, le_inf ?_ ?_⟩
  · exact (commutator_mono hZV hVQ).trans (early.commutator_le_Z (alpha R) rfl)
  · exact (commutator_mono le_rfl
      (hVQ.trans (Q_le_adjacent_h R rfl (base_adjacent R)))).trans hc

/-- The selected residual preserves each neighboring Z-layer and its edge commutator. -/
theorem edgeGenerator_normalized [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (early : EarlyFacts R geometry)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (htriple : ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hzero : Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)))
    (t : Vertex R) (ht : color R t = false) (hbt : Adjacent R (beta R) t) :
    flagResidual source i ≤ normalizer ((⁅Z R t, Q R (beta R)⁆ :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hZV : Z R t ≤ V R (beta R) := by
    rw [V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact le_iSup_of_le t (le_iSup_of_le hbt le_rfl)
  have hnormZ : flagResidual source i ≤ normalizer (Z R t : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hZV le_rfl).trans
      (flag_commutator_le_edge_Z_of_Bzero source geometry hlarge early i hkernel
        htriple hzero)).trans (edge_Z_le t (beta R) ht (adjacent_symm R hbt))
  have hnormQ : flagResidual source i ≤ normalizer (Q R (beta R) : Set (FreeAmalgam R)) := by
    rw [← hkernel]
    exact (flagResidual_le source i).trans (flagKernel_normalized source i)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hnormZ hg),
    mem_normalizer_iff_map_conj_eq.mp (hnormQ hg)]

/-- Reduction to uniqueness of the noncentral invariant four-group in the edge fixed layer.
The marked-action rigidity premise remains to be proved before the source comparison follows. -/
theorem edgeGeneratorComparison_of_fixedLayerRigidity [Finite M]
    (source : LocalSource L R) (geometry : Geometry R)
    (early : EarlyFacts R geometry) (hlarge : 2 < geometry.b R)
    (control : FlagControl source)
    (hzero : Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)))
    (rigidity : ∀ (i : Bool), flagKernel source i = Q R (beta R) →
      ∀ D : Subgroup (FreeAmalgam R), D ≤ Z R (beta R) → Nat.card D = 4 →
      (¬ D ≤ (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) →
      flagResidual source i ≤ normalizer (D : Set (FreeAmalgam R)) →
      D = ⁅Z R (alpha R), Q R (beta R)⁆) :
    ∀ t, nu R geometry (alpha R) t → Adjacent R (beta R) t →
      ⁅Z R t, Q R (beta R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ := by
  obtain ⟨i, hkernel, htriple⟩ := control
  intro t ht hbt
  have hcolor : color R t = false := by
    have hc := adjacent_color_ne R hbt
    change true ≠ color R t at hc
    cases hh : color R t <;> simp_all
  exact rigidity i hkernel _ (edgeGenerator_le_edge_Z geometry early t hcolor hbt)
    (early.edge_commutator_card t (beta R) hcolor (adjacent_symm R hbt))
    (edgeGenerator_noncentral geometry early hlarge hzero t ht)
    (edgeGenerator_normalized source geometry early hlarge i hkernel htriple hzero t
      hcolor hbt)

private theorem four_eq_commutator_of_idempotent {G : Type*} [Group G]
    (D H : Subgroup G) (hcard : Nat.card D = 4)
    (hn : H ≤ normalizer (D : Set G)) (hne : ⁅D, H⁆ ≠ ⊥)
    (hi : ⁅⁅D, H⁆, H⁆ = ⁅D, H⁆) : ⁅D, H⁆ = D := by
  let C := ⁅D, H⁆
  have hCD : C ≤ D := le_normalizer_iff_commutator_le_left.mp hn
  let : Finite D := Nat.finite_of_card_ne_zero (by omega : Nat.card D ≠ 0)
  let : Finite C := Finite.of_injective (inclusion hCD) (inclusion_injective _)
  have hd := card_dvd_of_le hCD
  rw [hcard] at hd
  have hc : Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 4 := by
    have hm : Nat.card C ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hc with hc | hc | hc
  · exact (hne (card_eq_one.mp hc)).elim
  · have hb : ⁅C, H⁆ ≤ ⊥ := commutator_le_of_normalized_index_two C ⊥ H bot_le
      (by simpa only [relIndex_bot_left] using hc)
      (normalizer_commutator_ge_right D H)
      (le_normalizer_iff_commutator_le_right.mpr (by rw [commutator_bot_right]))
    exact (hne (le_bot_iff.mp (hi ▸ hb))).elim
  · exact eq_of_le_of_card_ge hCD (by rw [hcard, hc])

/-- A nontrivial residual action on a normalized group of order four moves the whole group.
Idempotence is computed inside the finite marked parabolic and then embedded. -/
theorem flag_four_eq_commutator [Finite M] (source : LocalSource L R)
    (i : Bool) (D : Subgroup (FreeAmalgam R))
    (hDP : D ≤ flagParabolic source i) (hcard : Nat.card D = 4)
    (hn : flagResidual source i ≤ normalizer (D : Set (FreeAmalgam R)))
    (hne : ⁅D, flagResidual source i⁆ ≠ ⊥) :
    ⁅D, flagResidual source i⁆ = D := by
  apply four_eq_commutator_of_idempotent D (flagResidual source i) hcard hn hne
  let P := flagParabolic source i
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion (flagParabolic_le source i))
    (inclusion_injective _)
  let W := D.subgroupOf P
  have hW : W.map P.subtype = D := map_subgroupOf_eq_of_le hDP
  have hres : (pResidual 2 P).map P.subtype = flagResidual source i :=
    (flagResidual_eq source i).symm
  have hWN : pResidual 2 P ≤ normalizer (W : Set P) := by
    apply le_normalizer_iff.mpr
    intro h hh w hw
    exact le_normalizer_iff.mp hn h (hres ▸ mem_map_of_mem P.subtype hh) w hw
  have hp : IsPGroup 2 W := by
    have hc : Nat.card W = 2 ^ 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hDP).toEquiv).trans hcard
    exact IsPGroup.of_card hc
  have hi := commutator_isPPerfect_idempotent (pResidual 2 P) W
    (isPPerfect_pResidual 2) hp hWN
  have hm := congrArg (Subgroup.map P.subtype) hi
  simpa only [map_commutator, hW, hres] using hm

/-- The precise moving and fixed layers determine every noncentral invariant four-group. -/
theorem fixedLayerRigidity_of_markedAction [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (hmove : ⁅Z R (beta R), flagResidual source i⁆ = ⁅Z R (alpha R), Q R (beta R)⁆)
    (hfixed : Z R (beta R) ⊓ centralizer (flagResidual source i : Set (FreeAmalgam R)) ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (D : Subgroup (FreeAmalgam R)) (hDZ : D ≤ Z R (beta R)) (hcard : Nat.card D = 4)
    (hnoncentral : ¬ D ≤ (center (stabilizer R (alpha R))).map
      (stabilizer R (alpha R)).subtype)
    (hn : flagResidual source i ≤ normalizer (D : Set (FreeAmalgam R))) :
    D = ⁅Z R (alpha R), Q R (beta R)⁆ := by
  have hZQ : Z R (beta R) ≤ Q R (beta R) := by
    rw [Z, if_neg (show color R (beta R) ≠ false by change true ≠ false; decide)]
    exact omegaCenter_le _
  have hDP : D ≤ flagParabolic source i :=
    hDZ.trans (hZQ.trans (hkernel ▸ flagKernel_le source i))
  have hne : ⁅D, flagResidual source i⁆ ≠ ⊥ := by
    intro h
    exact hnoncentral ((le_inf hDZ (commutator_eq_bot_iff_le_centralizer.mp h)).trans hfixed)
  have hD := flag_four_eq_commutator source i D hDP hcard hn hne
  have hle : D ≤ ⁅Z R (alpha R), Q R (beta R)⁆ := by
    rw [← hmove, ← hD]
    exact commutator_mono hDZ le_rfl
  let := finite_stabilizer R (alpha R)
  let : Finite (Z R (alpha R)) := Finite.of_injective
    (inclusion (Z_le_stabilizer R _)) (inclusion_injective _)
  have hDZ' : ⁅Z R (alpha R), Q R (beta R)⁆ ≤ Z R (alpha R) :=
    (edgeGenerator_le_edge_Z geometry early (alpha R) rfl
      (adjacent_symm R (base_adjacent R))).trans
      (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
  let : Finite (⁅Z R (alpha R), Q R (beta R)⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hDZ') (inclusion_injective _)
  apply eq_of_le_of_card_ge hle
  rw [hcard, early.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)]

/-- Reduction of the source comparison to the two marked-action facts. -/
theorem edgeGeneratorComparison_of_markedAction [Finite M]
    (source : LocalSource L R) (geometry : Geometry R)
    (early : EarlyFacts R geometry) (hlarge : 2 < geometry.b R)
    (control : FlagControl source)
    (hzero : Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)))
    (action : ∀ (i : Bool), flagKernel source i = Q R (beta R) →
      ⁅Z R (beta R), flagResidual source i⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ ∧
      Z R (beta R) ⊓ centralizer (flagResidual source i : Set (FreeAmalgam R)) ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ∀ t, nu R geometry (alpha R) t → Adjacent R (beta R) t →
      ⁅Z R t, Q R (beta R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ := by
  apply edgeGeneratorComparison_of_fixedLayerRigidity source geometry early hlarge control hzero
  intro i hi
  exact fixedLayerRigidity_of_markedAction source geometry early i hi
    (action i hi).1 (action i hi).2

/-- The edge-generator clause of MS93 (4.6.9), conditional on the source
equality Bzero = B_alpha. The marked moving and fixed layers are supplied
by the actual natural action, with the flag chosen by FlagControl. -/
theorem edgeGeneratorComparison [Finite M]
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (control : FlagControl source)
    (hzero : Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R))) :
    ∀ t, nu R geometry (alpha R) t → Adjacent R (beta R) t →
      ⁅Z R t, Q R (beta R)⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ := by
  apply edgeGeneratorComparison_of_markedAction source geometry early
    (by rw [hb]; decide) control hzero
  exact edgeFixedLayerAction source geometry common early

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
