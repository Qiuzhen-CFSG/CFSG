module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Inputs
public import Theory.GroupTheory.Commutator.ResidualMovementModulo
public import Theory.GroupTheory.TransverseCommutatorIndex

/-!
# Critical-plane geometry without a natural subgroup complement

The literal maximal plane generates its normal orbit in the finite vertex
carrier. Its edge commutator bound survives normal closure, and conjugating
one edge layer places the entire base Z-layer in that orbit. These arguments
use only the distance-two graph and its actual embeddings.

Adapted from Chapter C's SymplecticDistanceTwo/Orbit, OrbitEdge and
OrbitCommutator, removing their unused natural-subgroup hypotheses.
Source: MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
variable {G : Type*} [Group G]
private theorem bounded_commutator_set_is_subgroup
    (A Q B : Subgroup G) [IsMulCommutative A] (hBA : B ≤ A) :
    ∃ Y : Subgroup G,
      ∀ x, x ∈ Y ↔ x ∈ A ∧ ∀ q ∈ Q, ⁅q,x⁆ ∈ B := by
  let Y : Subgroup G := {
    carrier := {x | x ∈ A ∧ ∀ q ∈ Q, ⁅q,x⁆ ∈ B}
    one_mem' := ⟨A.one_mem,fun q hq => by simp⟩
    mul_mem' := by
      rintro x y ⟨hx,hcx⟩ ⟨hy,hcy⟩
      refine ⟨A.mul_mem hx hy,fun q hq => ?_⟩
      have hc : x * ⁅q,y⁆ = ⁅q,y⁆ * x := congrArg Subtype.val
        (mul_comm (⟨x,hx⟩ : A) ⟨⁅q,y⁆,hBA (hcy q hq)⟩)
      rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅q,x⁆ x,
        hc,←mul_assoc,mul_inv_cancel_right]
      exact B.mul_mem (hcx q hq) (hcy q hq)
    inv_mem' := by
      rintro x ⟨hx,hcx⟩
      refine ⟨A.inv_mem hx,fun q hq => ?_⟩
      have hc : x⁻¹ * ⁅q,x⁆⁻¹ = ⁅q,x⁆⁻¹ * x⁻¹ := congrArg Subtype.val
        (mul_comm (⟨x⁻¹,A.inv_mem hx⟩ : A)
          ⟨⁅q,x⁆⁻¹,A.inv_mem (hBA (hcx q hq))⟩)
      rw [commutatorElement_inv_right,←commutatorElement_inv,hc,mul_assoc,inv_mul_cancel,mul_one]
      exact B.inv_mem (hcx q hq) }
  exact ⟨Y,fun x => Iff.rfl⟩

variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geo : Geometry R)

private theorem opposite_Z_elementary (hb : geo.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl)) :
    IsElementaryAbelian 2 (Z R c) := by
  have hcol := critical_endpoint_color R (alpha R) rfl _ hc
  have hpos : 0 < criticalDistance R c (geo.exists_critical c hcol) := by
    rw [geo.distance_constant c hcol]
    change 0 < geo.b R
    rw [hb]
    decide
  let : IsElementaryAbelian 2 (X R c) := omegaCenter_elementary (Q R c)
  exact IsElementaryAbelian.of_le (geo.omega_bound c hcol hpos)

omit [Finite M] in
private theorem edge_Z_le_opposite {c t : Vertex R}
    (hc : color R c = false) (hat : Adjacent R (alpha R) t)
    (hct : Adjacent R c t) : Z R t ≤ Z R c := by
  have ht := edge_color hat
  simp only [Z,hc,ht,Bool.true_eq_false,if_true,if_false]
  exact le_iSup_of_le t (le_iSup_of_le hct le_rfl)

/-- Membership is the source's literal maximal-plane condition. -/
theorem mem_criticalPlane_iff (hb : geo.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t)
    (x : FreeAmalgam R) :
    x ∈ criticalPlane R c t ↔
      x ∈ Z R c ∧ ∀ q ∈ Q R (alpha R), ⁅q,x⁆ ∈ Z R t := by
  let := opposite_Z_elementary geo hb hc
  obtain ⟨Y,hY⟩ := bounded_commutator_set_is_subgroup
    (Z R c) (Q R (alpha R)) (Z R t)
    (edge_Z_le_opposite (critical_endpoint_color R (alpha R) rfl _ hc) hat hct)
  have he : criticalPlane R c t = Y := by
    apply le_antisymm
    · exact (closure_le _).mpr (fun x hx => (hY x).mpr hx)
    · intro x hx
      exact subset_closure ((hY x).mp hx)
  rw [he,hY]

/-- The maximal plane has exactly the required edge commutator bound. -/
theorem criticalPlane_commutator_le (hb : geo.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    ⁅Q R (alpha R),criticalPlane R c t⁆ ≤ Z R t := by
  apply commutator_le.mpr
  intro q hq y hy
  exact ((mem_criticalPlane_iff geo hb hc hat hct y).mp hy).2 q hq

private theorem criticalPlane_le_range (hb : geo.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (t : Vertex R) : criticalPlane R c t ≤ (embedM R).range := by
  apply (criticalPlane_le_opposite (R := R) c t).trans
  change Z R c ≤ Mbar R
  rw [←stabilizer_m_base R]
  have hcol := critical_endpoint_color R (alpha R) rfl _ hc
  apply Z_le_stabilizer_of_dist_two R geo c hcol
  · rw [geo.distance_constant c hcol]
    change 0 < geo.b R
    rw [hb]
    decide
  · rw [SimpleGraph.dist_comm]
    exact hc.1.trans hb

theorem criticalPlane_le_orbit (hb : geo.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (t : Vertex R) : criticalPlane R c t ≤ criticalOrbit R c t := by
  have he : ((criticalPlane R c t).comap (embedM R)).map (embedM R) =
      criticalPlane R c t :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr (criticalPlane_le_range geo hb hc t))
  rw [←he]
  exact map_mono le_normalClosure

/-- Normal closure carries the source plane bound to the whole actual orbit. -/
theorem criticalOrbit_commutator_le (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hb : geo.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    ⁅Q R (alpha R),criticalOrbit R c t⁆ ≤ Z R (alpha R) := by
  let B := (Z R (alpha R)).comap (embedM R)
  let Y := (criticalPlane R c t).comap (embedM R)
  let : B.Normal := ChapterC.NaturalSixControl.SymplecticSeed.Z_comap_normal R
  have hcomm : ⁅pCore 2 M,Y⁆ ≤ B := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,←Q_alpha R hp hQR]
    apply (commutator_mono le_rfl (map_comap_le _ _)).trans
    exact (criticalPlane_commutator_le geo hb hc hat hct).trans
      (edge_Z_le_opposite rfl hat hat)
  have hn := commutator_normalClosure_le_of_normal (pCore 2 M) Y B hcomm
  have hh := map_mono (f := embedM R) hn
  rw [map_commutator,←Q_alpha R hp hQR] at hh
  exact hh.trans (map_comap_le _ _)

/-- The common edge layer itself lies in the maximal plane. -/
theorem edge_Z_le_criticalPlane
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    Z R t ≤ criticalPlane R c t := by
  have hcol := critical_endpoint_color R (alpha R) rfl _ hc
  have ht := edge_color hat
  have hZ : Z R t ≤ Z R c := by
    simp only [Z,hcol,ht,Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le t (le_iSup_of_le hct le_rfl)
  apply le_criticalPlane_of_commutator_le _ hZ
  exact le_normalizer_iff_commutator_le_right.mp
    ((Q_le_adjacent_h R ht hat).trans
      ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t)))

/-- The two endpoints use the same literal fixed edge layer. -/
theorem edge_Z_eq_fixed_opposite (hb : geo.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    Z R c ⊓ centralizer (Q R t : Set (FreeAmalgam R)) = Z R t := by
  have ht := edge_color hat
  have hcol := critical_endpoint_color R (alpha R) rfl _ hc
  have hpos : 0 < criticalDistance R c (geo.exists_critical c hcol) := by
    rw [geo.distance_constant c hcol]
    change 0 < geo.b R
    omega
  have hZQ : Z R c ≤ Q R c :=
    (geo.omega_bound c hcol hpos).trans (omegaCenter_le _)
  have hQc : Q R c ≤ Q R t := Q_le_adjacent_h R ht hct
  have hZt : Z R t = omegaCenter (Q R t) := by
    simp only [Z,ht,Bool.true_eq_false,if_false,edgeOmega]
  have hZ : Z R t ≤ Z R c := by
    simp only [Z,hcol,ht,Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le t (le_iSup_of_le hct le_rfl)
  apply le_antisymm
  · rintro x ⟨hx,hfix⟩
    rw [hZt,mem_omegaCenter_iff]
    let := Z_elementary_of_positive R geo c hcol hpos
    exact ⟨hQc (hZQ hx),elemPow_eq_one_of_isElementaryAbelian x hx,hfix⟩
  · intro x hx
    refine ⟨hZ hx,?_⟩
    rw [hZt,mem_omegaCenter_iff] at hx
    exact hx.2.2

/-- The plane has exactly the same edge-fixed subgroup as the opposite layer. -/
theorem criticalPlane_inf_edge_centralizer (hb : geo.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    criticalPlane R c t ⊓ centralizer (Q R t : Set (FreeAmalgam R)) = Z R t := by
  apply le_antisymm
  · exact (inf_le_inf_right _ (criticalPlane_le_opposite c t)).trans_eq
      (edge_Z_eq_fixed_opposite geo hb hc hat hct)
  · apply le_inf (edge_Z_le_criticalPlane geo hc hat hct)
    rw [←edge_Z_eq_fixed_opposite geo hb hc hat hct]
    exact inf_le_right

theorem Z_le_criticalOrbit {c b : Vertex R}
    (hb : geo.b R = 2)
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    Z R (alpha R) ≤ criticalOrbit R c b := by
  have hB := (edge_Z_le_criticalPlane geo hc hab hcb).trans (criticalPlane_le_orbit geo hb hc b)
  rw [Z,if_pos (show color R (alpha R) = false from rfl)]
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  obtain ⟨g,hg,hgd⟩ := stabilizer_transitive_neighbors R (alpha R) hab hd
  have hAg : (criticalOrbit R c b).map (MulAut.conj g⁻¹).toMonoidHom =
      criticalOrbit R c b := mem_normalizer_iff_map_conj_eq.mp
        (criticalOrbit_normalized (R := R) c b ((stabilizer R (alpha R)).inv_mem hg))
  have he := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hB
  rw [hAg,←Z_act,hgd] at he
  simpa only [Z,DistanceTwo.NaturalCore.edge_color hd,Bool.true_eq_false,if_false] using he


/-- The actual orbit contains the full base central layer. -/
theorem layer_le_orbit (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    orbitLayer R ≤ criticalOrbitNative R c b := by
  have hh := comap_mono (f := embedM R) (Z_le_criticalOrbit geo hb hc hab hcb)
  simpa only [orbitLayer,criticalOrbit,comap_map_eq_self_of_injective (embedM_injective R)] using hh

/-- Native version of the normal-closure commutator bound. -/
theorem orbit_commutator_le_layer (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ⁅pCore 2 M,criticalOrbitNative R c b⁆ ≤ orbitLayer R := by
  apply map_le_iff_le_comap.mp
  rw [map_commutator,←Q_alpha R hp hQR]
  exact criticalOrbit_commutator_le geo hp hQR hb hc hab hcb

/-- Removing the two-group supplement converts movement by the vertex group
into full component movement modulo the actual base Z-layer. -/
theorem full_movement_of_plane
    (K : Subgroup M) [K.Normal] (hp : IsPGroup 2 R) (hgen : K ⊔ R = ⊤)
    (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hAQ : criticalOrbitNative R c b ≤ pCore 2 M)
    (hY : criticalPlane R c b ≤
      ⁅criticalOrbit R c b,stabilizer R (alpha R)⁆ ⊔ Z R (alpha R)) :
    criticalOrbitNative R c b = ⁅K,criticalOrbitNative R c b⁆ ⊔ orbitLayer R := by
  let A := criticalOrbitNative R c b
  let Z0 := orbitLayer R
  have hZmap : Z0.map (embedM R) = Z R (alpha R) :=
    map_comap_eq_self ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hGa : (⊤ : Subgroup M).map (embedM R) = stabilizer R (alpha R) := by
    rw [←MonoidHom.range_eq_map]
    exact (stabilizer_m_base R).symm
  let N := ⁅A,⊤⁆ ⊔ Z0
  have hNmap : N.map (embedM R) =
      ⁅criticalOrbit R c b,stabilizer R (alpha R)⁆ ⊔ Z R (alpha R) := by
    rw [Subgroup.map_sup,map_commutator,hGa,hZmap]
    rfl
  have hfullmove : A ≤ ⁅A,⊤⁆ ⊔ Z0 := by
    apply normalClosure_le_normal
    intro y hy
    have hh : embedM R y ∈ N.map (embedM R) := hNmap.symm ▸ hY hy
    obtain ⟨z,hz,he⟩ := hh
    exact embedM_injective R he ▸ hz
  have hAp : IsPGroup 2 A := (pCore_isPGroup (p := 2) (G := M)).of_injective
    (inclusion hAQ) (inclusion_injective _)
  have hm := normal_p_subgroup_moved_modulo_supplement A K R Z0 hAp hp hgen hfullmove
  rw [commutator_comm A K] at hm
  exact le_antisymm hm (sup_le (commutator_le_right _ _)
    (layer_le_orbit geo hb hc hab hcb))

/-- A three-subgroups argument puts the genuine fixed preimage in the
center of the orbit; it never assumes a complement to its central layer. -/
theorem fixedKernel_central_of_full_movement
    (K : Subgroup M) [K.Normal] (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {c b : Vertex R} (hAQ : criticalOrbitNative R c b ≤ pCore 2 M)
    (hcent : ⁅⁅pCore 2 M,criticalOrbitNative R c b⁆,K⁆ = ⊥)
    (hmove : criticalOrbitNative R c b = ⁅K,criticalOrbitNative R c b⁆ ⊔ orbitLayer R) :
    orbitFixedKernel K R c b ≤ centralizer (criticalOrbitNative R c b : Set M) := by
  let A := criticalOrbitNative R c b
  let D := orbitFixedKernel K R c b
  have hZQ : ⁅orbitLayer R,pCore 2 M⁆ = ⊥ := by
    apply (map_injective (embedM_injective R))
    rw [map_commutator,Subgroup.map_bot,←Q_alpha R hp hQR]
    apply le_bot_iff.mp
    exact (commutator_mono (map_comap_le _ _) le_rfl).trans_eq
      (Z_centralizes_Q R (alpha R) rfl)
  have hDZ : ⁅D,K⁆ ≤ orbitLayer R :=
    commutator_commutatorPreimage_le A K (orbitLayer R) le_normalizer_of_normal
  have hDA : D ≤ A := orbitFixedKernel_le K R c b
  have h1 : ⁅⁅D,K⁆,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hDZ hAQ).trans_eq hZQ)
  have h2 : ⁅⁅A,D⁆,K⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono hAQ hDA) le_rfl).trans_eq hcent)
  have h3 : ⁅⁅K,A⁆,D⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h2 h1
  have h4 : ⁅orbitLayer R,D⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl (hDA.trans hAQ)).trans_eq hZQ)
  apply le_centralizer_iff.mp
  rw [hmove]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp h3)
    (commutator_eq_bot_iff_le_centralizer.mp h4)

omit [Finite M] in
/-- Nonzero residual movement forces the generating plane to escape the
canonical fixed preimage. -/
theorem plane_not_fixed_of_movement
    (K : Subgroup M) [K.Normal] {c b : Vertex R}
    (hne : ¬ ⁅criticalOrbitNative R c b,K⁆ ≤ orbitLayer R) :
    ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel K R c b := by
  intro hy
  have hA : criticalOrbitNative R c b ≤ orbitFixedKernel K R c b :=
    normalClosure_le_normal (fun _ hx => hy hx)
  exact hne ((commutator_mono hA le_rfl).trans (commutator_commutatorPreimage_le
    (criticalOrbitNative R c b) K (orbitLayer R) le_normalizer_of_normal))

/-- The full edge image moves the plane, because its fixed part is the
edge layer and that layer is already in the canonical fixed kernel. -/
theorem plane_movement_of_full_image
    (K : Subgroup M) [K.Normal] (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b)
    (hnot : ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel K R c b) :
    ⁅criticalOrbit R c b,criticalPlane R c b⁆ ≠ ⊥ := by
  intro he
  have hA := commutator_eq_bot_iff_le_centralizer.mp he
  have hQ : Q R c ≤ centralizer (criticalPlane R c b : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R c (critical_endpoint_color R (alpha R) rfl _ hc)))).trans
        (centralizer_le (criticalPlane_le_opposite c b))
  have hB : Q R b ≤ centralizer (criticalPlane R c b : Set (FreeAmalgam R)) :=
    himage ▸ sup_le hA hQ
  have hY : criticalPlane R c b ≤ Z R b := by
    rw [←criticalPlane_inf_edge_centralizer geo hb hc hab hcb]
    exact le_inf le_rfl (le_centralizer_iff.mp hB)
  apply hnot
  exact (comap_mono (hY.trans (edge_Z_le_opposite rfl hab hab))).trans
    (orbitLayer_le_fixedKernel K R c b (layer_le_orbit geo hb hc hab hcb))

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
