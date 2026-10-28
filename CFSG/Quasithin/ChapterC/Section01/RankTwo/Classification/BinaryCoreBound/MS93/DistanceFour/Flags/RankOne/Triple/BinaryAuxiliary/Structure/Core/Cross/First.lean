module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.ComparisonData

/-!
# The first full-actor triple from the midpoint comparison

A nonzero fixed vector in the binary natural plane contains every
matrix displacement in its line. For the actual midpoint-conjugated X,
the original Z_alpha supplies this vector. The original edge commutator
bound shows it is fixed by Q_beta, and the midpoint comparison makes its
line fixed by the transported full first actor modulo Z_middle.

Conjugating back gives one original incident pair. Full-actor transitivity
on the original coset representatives then proves the bound for every
incident pair. All these deductions keep the midpoint comparison explicit;
they do not construct its two central-layer containments.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), final two paragraphs of printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

private theorem binary_displacement_of_fixed : ∀ (a : SL2) (v w : Fin 2 → ZMod 2),
    v ≠ 0 → a.val.mulVec v = v →
    a.val.mulVec w - w = 0 ∨ a.val.mulVec w - w = v := by decide

private theorem factor_commutator_le_of_nonzero_fixed {G : Type*} [Group G]
    {P H N : Subgroup G} (n : RankOnePairing.RankOneFactor P H N)
    (Z E : Subgroup G) (hZH : Z ≤ H) (hZN : ¬ Z ≤ N) (hEP : E ≤ P)
    (hZE : ⁅Z,E⁆ ≤ N) : ⁅H,E⁆ ≤ Z ⊔ N := by
  obtain ⟨z, hz, hzn⟩ := SetLike.not_le_iff_exists.mp hZN
  let v : H := ⟨z, hZH hz⟩
  have hv : (n.coordinates v).toAdd ≠ 0 := by
    intro h
    apply hzn
    have hk : v ∈ n.coordinates.ker := by
      apply MonoidHom.mem_ker.mpr
      exact Multiplicative.toAdd.injective h
    rw [n.kernel] at hk
    exact hk
  rw [commutator_comm]
  apply commutator_le.mpr
  intro e he y hy
  let a : P := ⟨e, hEP he⟩
  let c (u : H) : H := ⟨e * (u : G) * e⁻¹,
    (mem_normalizer_iff.mp (n.normalized a.property) _).mp u.property⟩
  have hc (u : H) : (n.coordinates (c u * u⁻¹)).toAdd =
      (n.projection a).val.mulVec (n.coordinates u).toAdd - (n.coordinates u).toAdd := by
    rw [map_mul, map_inv]
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [n.action a u (c u) rfl]
  have hfix : (n.projection a).val.mulVec (n.coordinates v).toAdd =
      (n.coordinates v).toAdd := by
    have hk : c v * v⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      exact (commutator_comm E Z ▸ hZE) (commutator_mem_commutator he hz)
    have hh := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hk)
    rw [hc] at hh
    exact sub_eq_zero.mp hh
  let u : H := ⟨y, hy⟩
  rcases binary_displacement_of_fixed (n.projection a) (n.coordinates v).toAdd
      (n.coordinates u).toAdd hv hfix with h | h
  · have hk : c u * u⁻¹ ∈ n.coordinates.ker := by
      apply MonoidHom.mem_ker.mpr
      apply Multiplicative.toAdd.injective
      rw [hc]
      exact h
    rw [n.kernel] at hk
    exact mem_sup_right hk
  · have hh : n.coordinates (c u * u⁻¹) = n.coordinates v := by
      apply Multiplicative.toAdd.injective
      rw [hc]
      exact h
    have hk : (c u * u⁻¹) * v⁻¹ ∈ n.coordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hh, mul_inv_cancel]
    rw [n.kernel] at hk
    have ht := (Z ⊔ N).mul_mem (mem_sup_right hk) (mem_sup_left hz)
    change (e * y * e⁻¹ * y⁻¹) * z⁻¹ * z ∈ Z ⊔ N at ht
    simpa only [inv_mul_cancel_right, commutatorElement_def] using ht

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Transitivity of the full second actor on incident first actors and cores,
using common representatives in the original coset geometry. -/
theorem exists_incident_flag_transporter (source : LocalSource L R) (i : Bool)
    (d g h : M) (hg : flagIncident source i g d) (hh : flagIncident source i h d) :
    ∃ a : M, embedM R a ∈ localFlagActor source (!i) d ∧
      localConjugate (localFlagKernel source i g) a = localFlagKernel source i h ∧
      localConjugate (localFlagActor source i g) a = localFlagActor source i h := by
  obtain ⟨m, hgm, hdm⟩ := hg
  obtain ⟨n, hhn, hdn⟩ := hh
  have hKm : localFlagKernel source i m = localFlagKernel source i g := by
    simpa only [mul_inv_cancel_left] using
      localFlagKernel_right_mul source i g (g⁻¹ * m) hgm
  have hKn : localFlagKernel source i n = localFlagKernel source i h := by
    simpa only [mul_inv_cancel_left] using
      localFlagKernel_right_mul source i h (h⁻¹ * n) hhn
  have hPm : localFlagActor source i m = localFlagActor source i g := by
    simpa only [mul_inv_cancel_left] using
      localFlagActor_right_mul source i g (g⁻¹ * m) hgm
  have hPn : localFlagActor source i n = localFlagActor source i h := by
    simpa only [mul_inv_cancel_left] using
      localFlagActor_right_mul source i h (h⁻¹ * n) hhn
  refine ⟨n * m⁻¹, ?_, ?_, ?_⟩
  · refine ⟨embedM R ((d⁻¹ * n) * (d⁻¹ * m)⁻¹),
      ⟨_, (parabolic source.projection source.flag (!i)).mul_mem hdn
        ((parabolic source.projection source.flag (!i)).inv_mem hdm), rfl⟩, ?_⟩
    change embedM R d * embedM R ((d⁻¹ * n) * (d⁻¹ * m)⁻¹) *
      (embedM R d)⁻¹ = embedM R (n * m⁻¹)
    simp only [map_mul, map_inv]
    group
  · rw [← hKm]
    change localConjugate (localConjugate (flagKernel source i) m) (n * m⁻¹) = _
    rw [← localConjugate_mul, inv_mul_cancel_right]
    exact hKn
  · rw [← hPm]
    change localConjugate (localConjugate (flagParabolic source i) m) (n * m⁻¹) = _
    rw [← localConjugate_mul, inv_mul_cancel_right]
    exact hPn

/-- One incident first-actor triple bound propagates to every incident first
actor; the conjugating element fixes X through the full second actor. -/
theorem first_triple_all_of_one [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (i : Bool) (d g : M) (hg : flagIncident source i g d)
    (htriple : ⁅⁅X source i d, localFlagKernel source i g⁆,
      localFlagActor source i g⁆ ≤ Z R (alpha R)) :
    ∀ h : M, flagIncident source i h d →
      ⁅⁅X source i d, localFlagKernel source i h⁆,
        localFlagActor source i h⁆ ≤ Z R (alpha R) := by
  intro h hh
  obtain ⟨a, ha, hK, hP⟩ := exists_incident_flag_transporter source i d g h hg hh
  have hX : localConjugate (X source i d) a = X source i d :=
    mem_normalizer_iff_map_conj_eq.mp (X_normalized source geometry hlarge i d ha)
  have hZ := Incident.localConjugate_Z (R := R) a
  have ht := map_mono (f := (MulAut.conj (embedM R a)).toMonoidHom) htriple
  rw [map_commutator, map_commutator] at ht
  change ⁅⁅localConjugate (X source i d) a,
      localConjugate (localFlagKernel source i g) a⁆,
      localConjugate (localFlagActor source i g) a⁆ ≤
      localConjugate (Z R (alpha R)) a at ht
  simpa only [hX, hK, hP, hZ] using ht

/-- Simultaneous original-vertex conjugation transports the first triple. -/
theorem first_triple_conjugate [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (i : Bool) (a d g : M)
    (htriple : ⁅⁅X source i d, localFlagKernel source i g⁆,
      localFlagActor source i g⁆ ≤ Z R (alpha R)) :
    ⁅⁅X source i (a * d), localFlagKernel source i (a * g)⁆,
      localFlagActor source i (a * g)⁆ ≤ Z R (alpha R) := by
  have ht := map_mono (f := (MulAut.conj (embedM R a)).toMonoidHom) htriple
  rw [map_commutator, map_commutator] at ht
  change ⁅⁅localConjugate (X source i d) a,
    localConjugate (localConjugate (flagKernel source i) g) a⁆,
    localConjugate (localConjugate (flagParabolic source i) g) a⁆ ≤
      localConjugate (Z R (alpha R)) a at ht
  simpa only [X_conjugate source geometry hlarge, ← localConjugate_mul,
    Incident.localConjugate_Z, localFlagKernel, localFlagActor] using ht

/-- A bound at one incident pair gives the first triple at every original
second flag and every incident first flag. -/
theorem first_triple_at_of_incident_pair [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (i : Bool) (e d : M) (he : flagIncident source i 1 e)
    (htriple : ⁅⁅X source i e, flagKernel source i⁆,
      flagParabolic source i⁆ ≤ Z R (alpha R)) :
    ∀ g : M, flagIncident source i g d →
      ⁅⁅X source i d, localFlagKernel source i g⁆,
        localFlagActor source i g⁆ ≤ Z R (alpha R) := by
  have ht : ⁅⁅X source i e, localFlagKernel source i 1⁆,
      localFlagActor source i 1⁆ ≤ Z R (alpha R) := by
    simpa only [localFlagKernel, localFlagActor, localConjugate_one] using htriple
  have hh := first_triple_conjugate source geometry hlarge i (d * e⁻¹) e 1 ht
  simp only [inv_mul_cancel_right, mul_one] at hh
  apply first_triple_all_of_one source geometry hlarge i d (d * e⁻¹) _ hh
  have hi := (Incident.flagIncident_left source i (d * e⁻¹) 1 e).mpr he
  simpa only [mul_one, inv_mul_cancel_right] using hi

/-- The original center escapes the midpoint center: these conjugate finite
centers have equal order, and equality contradicts the selected U exclusion. -/
theorem alpha_Z_not_le_middle_Z [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle) :
    ¬ Z R (alpha R) ≤ Z R p.middle := by
  intro h
  let : Finite (stabilizer R p.middle) := finite_stabilizer R p.middle
  let : Finite (Z R p.middle) := Finite.of_injective
    (inclusion (Z_le_stabilizer R p.middle)) (inclusion_injective _)
  have hc := Nat.card_congr (t.conjugation.subgroupMap (Z R (alpha R))).toEquiv
  change Nat.card (Z R (alpha R)) =
    Nat.card ((Z R (alpha R)).map t.conjugation.toMonoidHom) at hc
  rw [t.map_Z_alpha] at hc
  have he := eq_of_le_of_card_ge h hc.symm.le
  exact p.middle_not_le (he ▸ Z_le_secondFlagLayer source i p.delta0)

/-- The two central-layer containments in the midpoint comparison imply all
first triple bounds. The proof uses actual natural coordinates: every matrix
fixing a nonzero vector displaces into its line. -/
theorem first_triple_of_middle_comparison [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (x : XFactor source i p.delta0) (e : M) (he : flagIncident source i 1 e)
    (hZX : Z R (alpha R) ≤ (X source i e).map t.conjugation.toMonoidHom)
    (hZP : ⁅Z R (alpha R), (flagParabolic source i).map t.conjugation.toMonoidHom⁆ ≤
      Z R p.middle) :
    ∀ (d g : M), flagIncident source i g d →
      ⁅⁅X source i d, localFlagKernel source i g⁆,
        localFlagActor source i g⁆ ≤ Z R (alpha R) := by
  obtain ⟨xe⟩ : Nonempty (XFactor source i e) := by
    simpa only [inv_mul_cancel_right] using
      XFactor_conjugate source geometry hlarge i (e * p.delta0⁻¹) p.delta0 x
  have n : RankOnePairing.RankOneFactor
      ((localFlagActor source (!i) e).map t.conjugation.toMonoidHom)
      ((X source i e).map t.conjugation.toMonoidHom) (Z R p.middle) := by
    simpa only [t.map_Z_alpha] using factorMap t.conjugation xe.val
  have hQ : Q R (beta R) ≤
      (localFlagActor source (!i) e).map t.conjugation.toMonoidHom :=
    (t.map_first_kernel source i hkernel).symm.le.trans
      (map_mono (Incident.flagKernel_le_incidentActor source i e he))
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases h : color R p.middle <;> simp_all
  have hZQ : ⁅Z R (alpha R), Q R (beta R)⁆ ≤ Z R p.middle :=
    (edge_commutator_le_edgeZ_of_early early (alpha R) (beta R) rfl
      (base_adjacent R)).trans
      (edge_Z_le p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor))
  have hbound := factor_commutator_le_of_nonzero_fixed n (Z R (alpha R))
    (Q R (beta R)) hZX (alpha_Z_not_le_middle_Z source geometry i p t) hQ hZQ
  have hnorm : (flagParabolic source i).map t.conjugation.toMonoidHom ≤
      normalizer (Z R p.middle) := by
    rw [← t.map_Z_alpha]
    exact (map_mono ((flagParabolic_le source i).trans (Z_normalized R _))).trans
      (le_normalizer_map _)
  have hZa : Z R (alpha R) ≤ stabilizer R p.middle :=
    ((Z_le_secondFlagLayer source i p.delta0).trans
      (t.second_le_range source geometry hlarge i p.delta0 p.middle_neighbor)).trans_eq
        t.embedding_range
  have hpre : Z R (alpha R) ⊔ Z R p.middle ≤
      commutatorPreimage (stabilizer R p.middle)
        ((flagParabolic source i).map t.conjugation.toMonoidHom) (Z R p.middle) :=
    sup_le (le_commutatorPreimage hZa hZP)
      (le_commutatorPreimage (Z_le_stabilizer R p.middle)
        (le_normalizer_iff_commutator_le_left.mp hnorm))
  have htriple : ⁅⁅(X source i e).map t.conjugation.toMonoidHom, Q R (beta R)⁆,
      (flagParabolic source i).map t.conjugation.toMonoidHom⁆ ≤ Z R p.middle :=
    (commutator_mono (hbound.trans hpre) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (Z_normalized R p.middle))
  have hbase : ⁅⁅X source i e, flagKernel source i⁆, flagParabolic source i⁆ ≤
      Z R (alpha R) := by
    apply (map_le_map_iff_of_injective (f := t.conjugation.toMonoidHom)
      t.conjugation.injective).mp
    simpa only [map_commutator, t.map_first_kernel source i hkernel, t.map_Z_alpha]
      using htriple
  intro d
  exact first_triple_at_of_incident_pair source geometry hlarge i e d he hbase

/-- Conditional first-bound assembly from the literal midpoint comparison.
Constructing that comparison remains a separate source obligation. -/
theorem first_triple_of_comparison [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i)
    (x : XFactor source i p.delta0) (c : MiddleComparison source geometry i p) :
    ∀ (d g : M), flagIncident source i g d →
      ⁅⁅X source i d, localFlagKernel source i g⁆,
        localFlagActor source i g⁆ ≤ Z R (alpha R) :=
  first_triple_of_middle_comparison source geometry hlarge early i hkernel p c.transport
    x c.flag c.incident c.center_le_X c.center_action

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
