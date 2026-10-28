module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData

/-!
# The geometric reductions for the auxiliary escapes

Faithfulness of the actual natural factor X/Z_alpha detects the endpoint
outside the opposite core. If X lay in Q_middle, the endpoint commutator
would lie in Z_middle. The binary edge index then puts Z_middle in
[X,Q_beta] Z_alpha, contradicting the first-actor triple.

For the second escape, Q_middle is normal inside Q_beta. Thus the printed
product X Q_middle has the underlying set of the subgroup join. Containment
of Y in this product gives the literal bound [Y,Z_endpoint] ≤ Z_middle X.
The further fixed-preimage calculation D = U is not asserted here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), final paragraph on printed p.908, using the explicit local
structure on p.907. All quotients and actors retain their original marking.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

private theorem natural_actor_kernel {G : Type*} [Group G] {P H N : Subgroup G}
    (n : RankOnePairing.RankOneFactor P H N) (E : Subgroup G) (_hEP : E ≤ P)
    (hcomm : ⁅H,E⁆ ≤ N) : E.subgroupOf P ≤ n.projection.ker := by
  intro g hg
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨x, hx⟩ := n.coordinates_surjective (Multiplicative.ofAdd v)
  have hy : (g : G) * (x : G) * (g : G)⁻¹ ∈ H :=
    (mem_normalizer_iff.mp (n.normalized g.property) _).mp x.property
  let y : H := ⟨_, hy⟩
  have hd : y * x⁻¹ ∈ n.coordinates.ker := by
    rw [n.kernel]
    exact (show ⁅E,H⁆ ≤ N by rwa [commutator_comm])
      (commutator_mem_commutator hg x.property)
  have he : n.coordinates y = n.coordinates x := by
    have hh := MonoidHom.mem_ker.mp hd
    rw [map_mul, map_inv, mul_inv_eq_one] at hh
    exact hh
  have ha := n.action g x y rfl
  rw [he, hx] at ha
  simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, toAdd_ofAdd] using ha.symm

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

private theorem commutator_join_bound {G : Type*} [Group G]
    (A B P T N : Subgroup G) (hAT : A ≤ T) (hBT : B ≤ T)
    (hTN : T ≤ normalizer N) (hA : ⁅A,P⁆ ≤ N) (hB : ⁅B,P⁆ ≤ N) :
    ⁅A ⊔ B,P⁆ ≤ N := by
  have h : A ⊔ B ≤ commutatorPreimage T P N :=
    sup_le (le_commutatorPreimage hAT hA) (le_commutatorPreimage hBT hB)
  exact (commutator_mono h le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hTN)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private def criticalData {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : SourceFlagPreparatoryData source geometry i) : FlagCriticalData source geometry i where
  middle := p.middle
  endpoint := p.endpoint
  critical := p.critical
  middle_neighbor := p.middle_neighbor
  first_distance := p.first_distance
  second_distance := p.second_distance
  middle_triple := p.middle_triple

/-- The endpoint acts nontrivially on the actual natural factor X/Z_alpha. -/
theorem X_endpoint_commutator_not_le (source : LocalSource L R) (geometry : Geometry R)
    (hb : geometry.b R = 4) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (d : M)
    (hd : flagIncident source i 1 d) (s : LocalStructure source i d)
    (hE : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d) :
    ¬ ⁅X source i d, Z R p.endpoint⁆ ≤ Z R (alpha R) := by
  intro h
  have hEP := Incident.endpoint_le_incidentActor source geometry hb i hkernel (criticalData p) d hd
  have hk := natural_actor_kernel s.natural (Z R p.endpoint) hEP h
  rw [s.natural_actor_kernel] at hk
  exact hE (fun x hx => hk (show (⟨x, hEP hx⟩ : localFlagActor source (!i) d) ∈
    (Z R p.endpoint).subgroupOf (localFlagActor source (!i) d) from hx))

/-- The first escape in the last paragraph of MS93 (4.6.8), p.908. -/
theorem X_not_le_middle_kernel (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (d : M)
    (hd : flagIncident source i 1 d) (s : LocalStructure source i d)
    (hE : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d) :
    ¬ X source i d ≤ Q R p.middle := by
  intro hX
  let c := criticalData p
  have hEV : Z R p.endpoint ≤ V R p.middle := by
    apply le_iSup_of_le p.endpoint
    apply le_iSup_of_le (show (cosetGraph R).dist p.endpoint p.middle ≤ 2 by
      rw [SimpleGraph.dist_comm]; exact p.second_distance.le)
    exact le_rfl
  have hXE : ⁅X source i d,Z R p.endpoint⁆ ≤ Z R p.middle := by
    rw [commutator_comm]
    exact (commutator_mono hEV hX).trans (early.commutator_le_Z p.middle c.middle_color)
  have hm : Z R p.middle ≤ ⁅X source i d,Q R (beta R)⁆ ⊔ Z R (alpha R) :=
    (index_two_generation _ (Z R (beta R)) _ _
      (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)) hXE
      (early.edge_Z_index p.middle (beta R) c.middle_color (adjacent_symm R p.middle_neighbor))
      (X_endpoint_commutator_not_le source geometry hb i hkernel p d hd s hE)).trans
        (sup_le_sup (commutator_mono le_rfl (c.endpoint_le_edgeKernel hb)) le_rfl)
  have hfirst : ⁅⁅X source i d,Q R (beta R)⁆,flagParabolic source i⁆ ≤ Z R (alpha R) := by
    simpa only [localFlagKernel, localFlagActor, localConjugate_one, hkernel] using s.first_triple 1 hd
  have hXG : X source i d ≤ stabilizer R (alpha R) :=
    (X_le_second source geometry common.large_distance i d).trans
      ((secondFlagLayer_le_radius source i d).trans (geometry.V_local _ rfl common.large_distance))
  have hQG : Q R (beta R) ≤ stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))
  have hc : ⁅Z R p.middle,flagParabolic source i⁆ ≤ Z R (alpha R) :=
    (commutator_mono hm le_rfl).trans (commutator_join_bound _ _ _ (stabilizer R (alpha R)) _
      ((Subgroup.commutator_le_sup _ _).trans (sup_le hXG hQG)) (Z_le_stabilizer R _)
      (Z_normalized R _) hfirst
      (le_normalizer_iff_commutator_le_left.mp ((flagParabolic_le source i).trans (Z_normalized R _))))
  apply p.middle_triple
  have hr : ⁅Z R p.middle,flagResidual source i⁆ ≤ Z R (alpha R) :=
    (commutator_mono le_rfl (flagResidual_le source i)).trans hc
  exact ((commutator_mono hr (V_le_Q geometry common.large_distance _ rfl)).trans_eq
    (geometry.centralizes (alpha R) rfl)).trans bot_le

/-- X is normal in the actual edge kernel, by incidence of its local actor. -/
theorem edge_kernel_normalizes_X (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    Q R (beta R) ≤ normalizer (X source i d) := by
  rw [← hkernel]
  exact (Incident.flagKernel_le_incidentActor source i d hd).trans
    (X_normalized source geometry hlarge i d)

/-- The source product X_delta Q_middle is a subgroup product inside Q_beta.
The midpoint core is normalized by Q_beta, which contains X; hence the
underlying set of the product is the join. -/
theorem X_middle_kernel_product (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (d : M) :
    ((X source i d ⊔ Q R p.middle : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) =
      (X source i d : Set (FreeAmalgam R)) * (Q R p.middle : Set (FreeAmalgam R)) := by
  have hXQ : X source i d ≤ Q R (beta R) :=
    (X_le_second source geometry hlarge i d).trans
      ((secondFlagLayer_le_radius source i d).trans ((V_le_Q geometry hlarge _ rfl).trans
        (Q_le_adjacent_h R rfl (base_adjacent R))))
  have hQM : Q R (beta R) ≤ stabilizer R p.middle := fun _ hx => hx.2 _ p.middle_neighbor
  exact coe_mul_of_left_le_normalizer_right _ _ (hXQ.trans (hQM.trans (Q_normalized R p.middle)))

/-- The literal endpoint commutator containment in the second p.908 argument.
All normality is relative to Q_beta and the original midpoint is retained. -/
theorem Y_endpoint_commutator_le_of_contained (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (d : M)
    (hd : flagIncident source i 1 d)
    (hY : Y source i d ≤ X source i d ⊔ Q R p.middle) :
    ⁅Y source i d,Z R p.endpoint⁆ ≤ Z R p.middle ⊔ X source i d := by
  let c := criticalData p
  have hlarge : 2 < geometry.b R := by omega
  have hXP : X source i d ≤ Q R (beta R) :=
    (X_le_second source geometry hlarge i d).trans
      ((secondFlagLayer_le_radius source i d).trans ((V_le_Q geometry hlarge _ rfl).trans
        (Q_le_adjacent_h R rfl (base_adjacent R))))
  have hQP : Q R p.middle ≤ Q R (beta R) :=
    Q_le_adjacent_h R rfl (adjacent_symm R p.middle_neighbor)
  have hQG : Q R (beta R) ≤ stabilizer R p.middle := fun _ hx => hx.2 _ p.middle_neighbor
  have hPX := edge_kernel_normalizes_X source geometry hlarge i hkernel d hd
  have hPN : Q R (beta R) ≤ normalizer (Z R p.middle ⊔ X source i d : Subgroup (FreeAmalgam R)) :=
    (le_inf (hQG.trans (Z_normalized R p.middle)) hPX).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hEV : Z R p.endpoint ≤ V R p.middle := by
    apply le_iSup_of_le p.endpoint
    apply le_iSup_of_le (show (cosetGraph R).dist p.endpoint p.middle ≤ 2 by
      rw [SimpleGraph.dist_comm]; exact p.second_distance.le)
    exact le_rfl
  have hQE : ⁅Q R p.middle,Z R p.endpoint⁆ ≤ Z R p.middle := by
    rw [commutator_comm]
    exact (commutator_mono hEV le_rfl).trans (early.commutator_le_Z p.middle c.middle_color)
  exact (commutator_mono hY le_rfl).trans
    (commutator_join_bound _ _ _ (Q R (beta R)) _ hXP hQP hPN
      ((le_normalizer_iff_commutator_le_left.mp ((c.endpoint_le_edgeKernel hb).trans hPX)).trans le_sup_right)
      (hQE.trans le_sup_left))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
