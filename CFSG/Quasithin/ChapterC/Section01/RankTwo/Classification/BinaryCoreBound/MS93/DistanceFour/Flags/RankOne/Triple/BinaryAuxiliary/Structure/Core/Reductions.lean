module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Midpoint

/-!
# Reductions for the binary auxiliary core calculation

The original nonzero triple propagates to every second flag by conjugation.
A marked natural factor detects its exact actor kernel by ambient
commutators. Applied to X at the selected delta0, it forces X to escape
Q_middle: otherwise the endpoint commutator and edge index two would put
Z_middle in X, contrary to the source selection. The incident core pencil
then selects the transported lambda0 escaped by X.

Finally, full-actor transitivity on the incident fixed preimages shows that
[U,L] <= X implies the printed decomposition of U at every first neighbor.
Thus the remaining core calculation must construct natural coordinates and
prove the two cross-commutator bounds. The escape lemmas here take those
coordinates explicitly; they do not construct them.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), final two paragraphs of printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

/-- Trivial action on a marked natural factor detects precisely the prescribed
core of the full actor, in either direction. -/
theorem markedFactor_commutator_iff {G : Type*} [Group G] {P H N K : Subgroup G}
    (n : MarkedFactor P H N K) (E : Subgroup G) (hEP : E ≤ P) :
    ⁅H, E⁆ ≤ N ↔ E ≤ K := by
  constructor
  · intro h g hg
    let l : P := ⟨g, hEP hg⟩
    have hk : l ∈ n.val.projection.ker := by
      apply Subtype.ext
      apply Matrix.ext_iff_mulVec.mpr
      intro v
      obtain ⟨x, hx⟩ := n.val.coordinates_surjective (Multiplicative.ofAdd v)
      have hy : g * (x : G) * g⁻¹ ∈ H :=
        (mem_normalizer_iff.mp (n.val.normalized l.property) _).mp x.property
      let y : H := ⟨_, hy⟩
      have hd : y * x⁻¹ ∈ n.val.coordinates.ker := by
        rw [n.val.kernel]
        exact (show ⁅E,H⁆ ≤ N by rwa [commutator_comm])
          (commutator_mem_commutator hg x.property)
      have he : n.val.coordinates y = n.val.coordinates x := by
        have hh := MonoidHom.mem_ker.mp hd
        rw [map_mul, map_inv, mul_inv_eq_one] at hh
        exact hh
      have ha := n.val.action l x y rfl
      rw [he, hx] at ha
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
        toAdd_ofAdd] using ha.symm
    rw [n.property] at hk
    exact hk
  · intro h
    rw [commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro g hg x hx
    let l : P := ⟨g, hEP hg⟩
    let a : H := ⟨x, hx⟩
    let b : H := ⟨g * x * g⁻¹,
      (mem_normalizer_iff.mp (n.val.normalized l.property) _).mp hx⟩
    have hl : n.val.projection l = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [n.property]
      exact h hg
    have ha := n.val.action l a b rfl
    rw [hl, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at ha
    have he : n.val.coordinates b = n.val.coordinates a :=
      congrArg Multiplicative.ofAdd ha
    have hk : b * a⁻¹ ∈ n.val.coordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [n.val.kernel] at hk
    exact hk

variable {M : Type*} [Group M] {L R : Subgroup M}
/-- The genuine nonzero source triple persists at every second flag.
The proof transports the original nonzero witness, rather than replacing it
with a nontriviality assumption on D. -/
theorem Y_core_triple_not_le (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) (p : SourceFlagPreparatoryData source geometry i) (d : M) :
    ¬ ⁅⁅Y source i d, localFlagKernel source (!i) d⁆,
      localFlagActor source (!i) d⁆ ≤ Z R (alpha R) := by
  have hbase : ¬ ⁅⁅Y source i p.delta2, localFlagKernel source (!i) p.delta2⁆,
      localFlagActor source (!i) p.delta2⁆ ≤ Z R (alpha R) := by
    intro h
    apply p.second_triple
    have hf : V R (beta R) ≤ Y source i p.delta2 := by
      simpa only [firstFlagLayer, localConjugate_one] using
        first_le_Y source i 1 p.delta2 p.delta2_neighbor
    exact (commutator_mono (commutator_mono hf le_rfl)
      (map_mono (flagResidual_le source (!i)))).trans h
  intro h
  apply hbase
  let a := p.delta2 * d⁻¹
  have ha : a * d = p.delta2 := by simp only [a, mul_assoc, inv_mul_cancel, mul_one]
  have hh := map_mono (f := (MulAut.conj (embedM R a)).toMonoidHom) h
  rw [map_commutator, map_commutator] at hh
  change ⁅⁅localConjugate (Y source i d) a,
    localConjugate (localConjugate (flagKernel source (!i)) d) a⁆,
    localConjugate (localConjugate (flagParabolic source (!i)) d) a⁆ ≤
      localConjugate (Z R (alpha R)) a at hh
  simpa only [Y_conjugate, ← localConjugate_mul, Incident.localConjugate_Z, ha, localFlagKernel, localFlagActor] using hh

private theorem index_two_generation {G : Type*} [Group G]
    (H B C N : Subgroup G) (hBN : B ≤ N) (hCH : C ≤ H)
    (hi : B.relIndex H = 2) (hnot : ¬ C ≤ N) : H ≤ C ⊔ N := by
  obtain ⟨a, _, _, hcosets⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hi
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxa : x * a ∈ B := (hcosets x (hCH hx)).resolve_right (fun h => hxn (hBN h))
  have ha : a ∈ C ⊔ N := by
    have hh := (C ⊔ N).mul_mem ((C ⊔ N).inv_mem (mem_sup_left hx))
      (mem_sup_right (hBN hxa))
    simpa only [inv_mul_cancel_left] using hh
  intro y hy
  rcases hcosets y hy with hya | hyb
  · have hh := (C ⊔ N).mul_mem (mem_sup_right (hBN hya)) ((C ⊔ N).inv_mem ha)
    simpa only [mul_inv_cancel_right] using hh
  · exact mem_sup_right (hBN hyb)

private def coreCriticalData {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : SourceFlagPreparatoryData source geometry i) : FlagCriticalData source geometry i where
  middle := p.middle
  endpoint := p.endpoint
  critical := p.critical
  middle_neighbor := p.middle_neighbor
  first_distance := p.first_distance
  second_distance := p.second_distance
  middle_triple := p.middle_triple

variable [Finite M]

/-- At the selected delta0, naturality alone forces the p.907 escape from
Q_middle. The endpoint gives a nonzero commutator, and the edge index two
would otherwise put Z_middle in X, contradicting its exclusion from U.
The first-triple identity and the later p.908 escapes are not inputs. -/
theorem X_selected_not_le_middle_core (source : LocalSource L R) (geometry : Geometry R)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i)
    (n : XFactor source i p.delta0) : ¬ X source i p.delta0 ≤ Q R p.middle := by
  intro hX
  have hlarge : 2 < geometry.b R := by omega
  let c := coreCriticalData p
  have hEP : Z R p.endpoint ≤ localFlagActor source (!i) p.delta0 :=
    Incident.endpoint_le_incidentActor source geometry hb i hkernel c
      p.delta0 p.delta0_neighbor
  have hnon : ¬ ⁅X source i p.delta0, Z R p.endpoint⁆ ≤ Z R (alpha R) := by
    rw [markedFactor_commutator_iff n _ hEP]
    exact p.endpoint_not_le
  have hEV : Z R p.endpoint ≤ V R p.middle := by
    apply le_iSup_of_le p.endpoint
    apply le_iSup_of_le (show (cosetGraph R).dist p.endpoint p.middle ≤ 2 by
      rw [SimpleGraph.dist_comm]; exact p.second_distance.le)
    exact le_rfl
  have hcomm : ⁅X source i p.delta0, Z R p.endpoint⁆ ≤ Z R p.middle := by
    rw [commutator_comm]
    exact (commutator_mono hEV hX).trans (early.commutator_le_Z p.middle c.middle_color)
  have hm : Z R p.middle ≤ ⁅X source i p.delta0, Z R p.endpoint⁆ ⊔ Z R (alpha R) :=
    index_two_generation _ (Z R (beta R)) _ _
      (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)) hcomm
      (early.edge_Z_index p.middle (beta R) c.middle_color
        (adjacent_symm R p.middle_neighbor)) hnon
  have hcX : ⁅X source i p.delta0, Z R p.endpoint⁆ ≤ X source i p.delta0 :=
    le_normalizer_iff_commutator_le_left.mp
      (hEP.trans (X_normalized source geometry hlarge i p.delta0))
  apply p.middle_not_le
  exact (hm.trans (sup_le hcX le_sup_right)).trans (X_le_second source geometry hlarge i p.delta0)

/-- The later p.907 choice can be made to escape a transported core with X
itself. Both the incident flag and the actual midpoint conjugation are kept. -/
theorem exists_middle_X_crossing (source : LocalSource L R) (geometry : Geometry R)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (n : XFactor source i p.delta0) :
    ∃ e : M, flagIncident source i 1 e ∧
      ¬ X source i p.delta0 ≤
        (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom := by
  obtain ⟨e, hi, _, hm, _⟩ := Incident.exists_incident_core_pencil source i
  by_cases h₀ : X source i p.delta0 ≤
      (localFlagKernel source (!i) (e 0)).map t.conjugation.toMonoidHom
  · refine ⟨e 1, hi 1, ?_⟩
    intro h₁
    apply X_selected_not_le_middle_core source geometry hb early i hkernel p n
    have hh := le_inf h₀ h₁
    rw [← map_inf _ _ _ t.conjugation.injective, hm 0 1 (by decide), t.map_Q_alpha] at hh
    exact hh
  · exact ⟨e 0, hi 0, h₀⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary


open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem conjugate_le_sup_of_commutator {G : Type*} [Group G]
    (H U P N : Subgroup G) (hHU : H ≤ U) (hcomm : ⁅U, P⁆ ≤ N)
    (a : G) (ha : a ∈ P) : H.map (MulAut.conj a).toMonoidHom ≤ H ⊔ N := by
  rintro y ⟨x, hx, rfl⟩
  have hc : ⁅a,x⁆ ∈ N := by
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator ha (hHU hx))
  have h := (H ⊔ N).mul_mem (mem_sup_right hc) (mem_sup_left hx)
  change a * x * a⁻¹ ∈ H ⊔ N
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using h

/-- Two incident first layers are conjugate by an element of the same full
second actor, through their original common coset representatives. -/
theorem exists_incident_first_transporter (source : LocalSource L R) (i : Bool)
    (natural : FlagNaturalSection source i) (d g h : M)
    (hg : flagIncident source i g d) (hh : flagIncident source i h d) :
    ∃ a : M, embedM R a ∈ localFlagActor source (!i) d ∧
      localConjugate (firstFlagLayer (R := R) g) a = firstFlagLayer (R := R) h := by
  obtain ⟨m, hgm, hdm⟩ := hg
  obtain ⟨n, hhn, hdn⟩ := hh
  have hmg : firstFlagLayer (R := R) m = firstFlagLayer (R := R) g := by
    simpa only [mul_inv_cancel_left] using
      firstFlagLayer_right_mul source i natural g (g⁻¹ * m) hgm
  have hnh : firstFlagLayer (R := R) n = firstFlagLayer (R := R) h := by
    simpa only [mul_inv_cancel_left] using
      firstFlagLayer_right_mul source i natural h (h⁻¹ * n) hhn
  refine ⟨n * m⁻¹, ?_, ?_⟩
  · refine ⟨embedM R ((d⁻¹ * n) * (d⁻¹ * m)⁻¹),
      ⟨_, (parabolic source.projection source.flag (!i)).mul_mem hdn
        ((parabolic source.projection source.flag (!i)).inv_mem hdm), rfl⟩, ?_⟩
    change embedM R d * embedM R ((d⁻¹ * n) * (d⁻¹ * m)⁻¹) *
      (embedM R d)⁻¹ = embedM R (n * m⁻¹)
    simp only [map_mul, map_inv]
    group
  · rw [← hmg]
    change localConjugate (localConjugate (V R (beta R)) m) (n * m⁻¹) = _
    rw [← localConjugate_mul, inv_mul_cancel_right]
    exact hnh

/-- Once the full second actor acts trivially on U/X, any one incident
fixed preimage generates U together with X. -/
theorem second_decomposition_of_commutator [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (i : Bool) (natural : FlagNaturalSection source i) (d : M)
    (hcomm : ⁅secondFlagLayer source i d, localFlagActor source (!i) d⁆ ≤ X source i d)
    (g : M) (hg : flagIncident source i g d) :
    secondFlagLayer source i d =
      commutatorPreimage (firstFlagLayer (R := R) g) (localFlagKernel source (!i) d)
        (Z R (alpha R)) ⊔ X source i d := by
  let F := fun h : M => commutatorPreimage (firstFlagLayer (R := R) h)
    (localFlagKernel source (!i) d) (Z R (alpha R))
  have hF (h : M) (hh : flagIncident source i h d) : F h ≤ secondFlagLayer source i d :=
    le_iSup_of_le h (le_iSup_of_le hh le_rfl)
  apply le_antisymm
  · apply iSup_le
    intro h
    apply iSup_le
    intro hh
    obtain ⟨a, ha, hfirst⟩ := exists_incident_first_transporter source i natural d g h hg hh
    have hKP : localFlagActor source (!i) d ≤ normalizer (localFlagKernel source (!i) d) :=
      (map_mono (flagKernel_normalized source (!i))).trans (le_normalizer_map _)
    have hK : (localFlagKernel source (!i) d).map
        (MulAut.conj (embedM R a)).toMonoidHom = localFlagKernel source (!i) d :=
      mem_normalizer_iff_map_conj_eq.mp (hKP ha)
    have hZ : (Z R (alpha R)).map (MulAut.conj (embedM R a)).toMonoidHom =
        Z R (alpha R) := mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized R _ (localFlagActor_le_stabilizer source (!i) d ha))
    have hFconj : localConjugate (F g) a = F h := by
      unfold localConjugate F
      rw [commutatorPreimage_map_equiv _ _ _ _
        ((firstFlagLayer_le_radius g).trans ((geometry.V_local _ rfl hlarge).trans
          (Z_normalized R _))), hK, hZ]
      exact congrArg (fun A => commutatorPreimage A (localFlagKernel source (!i) d)
        (Z R (alpha R))) hfirst
    change F h ≤ F g ⊔ X source i d
    rw [← hFconj]
    exact conjugate_le_sup_of_commutator (F g) _ _ _ (hF g hg) hcomm (embedM R a) ha
  · exact sup_le (hF g hg) (X_le_second source geometry hlarge i d)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
