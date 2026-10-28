module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.LocalGeometry
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# The actual critical-plane orbit at symplectic distance two

The plane is the largest subgroup of the opposite elementary Z-layer whose
commutator with the original two-core lies in the common edge Z-layer.
Its orbit is the normal closure inside the original finite vertex group,
followed by the specified embedding in the amalgam. The elementary seed,
relative normality, and commutator bound therefore use actual graph groups.

Source: MS93 (3.6), the symplectic paragraph on printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo

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

variable {M : Type*} [Group M] (R : Subgroup M)

/-- The maximal plane with the commutator bound in MS93 (3.6). -/
def criticalPlane (c t : Vertex R) : Subgroup (FreeAmalgam R) :=
  closure {x | x ∈ Z R c ∧ ∀ q ∈ Q R (alpha R), ⁅q,x⁆ ∈ Z R t}

/-- The conjugate span before the specified embedding in the amalgam. -/
def criticalOrbitNative (c t : Vertex R) : Subgroup M :=
  normalClosure (((criticalPlane R c t).comap (embedM R) : Subgroup M) : Set M)

/-- Its actual conjugate span in the finite original vertex group. -/
def criticalOrbit (c t : Vertex R) : Subgroup (FreeAmalgam R) :=
  (criticalOrbitNative R c t).map (embedM R)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

private theorem opposite_Z_elementary (hb : s.geometry.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl)) :
    IsElementaryAbelian 2 (Z R c) := by
  have hcol := critical_endpoint_color R (alpha R) rfl _ hc
  have hpos : 0 < criticalDistance R c (s.geometry.exists_critical c hcol) := by
    rw [s.geometry.distance_constant c hcol]
    change 0 < s.geometry.b R
    rw [hb]
    decide
  let : IsElementaryAbelian 2 (X R c) := omegaCenter_elementary (Q R c)
  exact IsElementaryAbelian.of_le (s.geometry.omega_bound c hcol hpos)

omit [Finite M] [L.Normal] [W.Normal] s in
private theorem edge_Z_le_opposite {c t : Vertex R}
    (hc : color R c = false) (hat : Adjacent R (alpha R) t)
    (hct : Adjacent R c t) : Z R t ≤ Z R c := by
  have ht := edge_color hat
  simp only [Z,hc,ht,Bool.true_eq_false,if_true,if_false]
  exact le_iSup_of_le t (le_iSup_of_le hct le_rfl)

/-- Membership is the source's literal maximal-plane condition. -/
theorem mem_criticalPlane_iff (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t)
    (x : FreeAmalgam R) :
    x ∈ criticalPlane R c t ↔
      x ∈ Z R c ∧ ∀ q ∈ Q R (alpha R), ⁅q,x⁆ ∈ Z R t := by
  let := s.opposite_Z_elementary hb hc
  obtain ⟨Y,hY⟩ := bounded_commutator_set_is_subgroup
    (Z R c) (Q R (alpha R)) (Z R t)
    (edge_Z_le_opposite (critical_endpoint_color R (alpha R) rfl _ hc) hat hct)
  have he : criticalPlane R c t = Y := by
    apply le_antisymm
    · exact (closure_le _).mpr (fun x hx => (hY x).mpr hx)
    · intro x hx
      exact subset_closure ((hY x).mp hx)
  rw [he,hY]

omit [Finite M] [L.Normal] [W.Normal] s in
theorem criticalPlane_le_opposite (c t : Vertex R) :
    criticalPlane R c t ≤ Z R c :=
  (closure_le _).mpr (fun _ hx => hx.1)

theorem criticalPlane_elementary (hb : s.geometry.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) : IsElementaryAbelian 2 (criticalPlane R c t) := by
  let := s.opposite_Z_elementary hb hc
  exact IsElementaryAbelian.of_le (criticalPlane_le_opposite (R := R) c t)

/-- The maximal plane has exactly the required edge commutator bound. -/
theorem criticalPlane_commutator_le (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    ⁅Q R (alpha R),criticalPlane R c t⁆ ≤ Z R t := by
  apply commutator_le.mpr
  intro q hq y hy
  exact ((s.mem_criticalPlane_iff hb hc hat hct y).mp hy).2 q hq

omit [Finite M] [L.Normal] [W.Normal] s in
/-- Every subgroup satisfying the plane condition is contained in this one. -/
theorem le_criticalPlane_of_commutator_le (A : Subgroup (FreeAmalgam R))
    {c t : Vertex R} (hA : A ≤ Z R c)
    (hcomm : ⁅Q R (alpha R),A⁆ ≤ Z R t) : A ≤ criticalPlane R c t := by
  intro x hx
  exact subset_closure ⟨hA hx,fun q hq =>
    hcomm (commutator_mem_commutator hq hx)⟩

private theorem criticalPlane_le_range (hb : s.geometry.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) : criticalPlane R c t ≤ (embedM R).range := by
  apply (criticalPlane_le_opposite (R := R) c t).trans
  change Z R c ≤ Mbar R
  rw [←stabilizer_m_base R]
  have hcol := critical_endpoint_color R (alpha R) rfl _ hc
  apply Z_le_stabilizer_of_dist_two R s.geometry c hcol
  · rw [s.geometry.distance_constant c hcol]
    change 0 < s.geometry.b R
    rw [hb]
    decide
  · rw [SimpleGraph.dist_comm]
    exact hc.1.trans hb

theorem criticalPlane_le_orbit (hb : s.geometry.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) : criticalPlane R c t ≤ criticalOrbit R c t := by
  have he : ((criticalPlane R c t).comap (embedM R)).map (embedM R) =
      criticalPlane R c t :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr (s.criticalPlane_le_range hb hc t))
  rw [←he]
  exact map_mono le_normalClosure

omit [Finite M] [L.Normal] [W.Normal] s in
private theorem normal_comap_base (N : Subgroup (FreeAmalgam R))
    (hN : stabilizer R (alpha R) ≤ normalizer (N : Set (FreeAmalgam R))) :
    (N.comap (embedM R)).Normal := by
  constructor
  intro x hx m
  change embedM R (m*x*m⁻¹) ∈ N
  rw [map_mul,map_mul,map_inv]
  apply le_normalizer_iff.mp hN _ _ _ hx
  rw [show alpha R = mVertex R 1 from rfl,stabilizer_m_base]
  exact ⟨m,rfl⟩

omit [Finite M] [L.Normal] [W.Normal] s in
theorem criticalOrbit_normalized (c t : Vertex R) :
    stabilizer R (alpha R) ≤ normalizer (criticalOrbit R c t : Set (FreeAmalgam R)) := by
  let A := criticalOrbitNative R c t
  let : A.Normal := normalClosure_normal
  rw [show alpha R = mVertex R 1 from rfl,stabilizer_m_base]
  change (embedM R).range ≤ normalizer (A.map (embedM R) : Set (FreeAmalgam R))
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map] using A.le_normalizer_map (embedM R)

/-- Normal closure carries the source plane bound to the whole actual orbit. -/
theorem criticalOrbit_commutator_le (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    ⁅Q R (alpha R),criticalOrbit R c t⁆ ≤ Z R (alpha R) := by
  let B := (Z R (alpha R)).comap (embedM R)
  let Y := (criticalPlane R c t).comap (embedM R)
  let : B.Normal := normal_comap_base _ (Z_normalized R (alpha R))
  have hcomm : ⁅pCore 2 M,Y⁆ ≤ B := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,←Q_alpha R s.two_group s.core_le]
    apply (commutator_mono le_rfl (map_comap_le _ _)).trans
    exact (s.criticalPlane_commutator_le hb hc hat hct).trans
      (edge_Z_le_opposite rfl hat hat)
  have hn := commutator_normalClosure_le_of_normal (pCore 2 M) Y B hcomm
  have hh := map_mono (f := embedM R) hn
  rw [map_commutator,←Q_alpha R s.two_group s.core_le] at hh
  exact hh.trans (map_comap_le _ _)

/-- The critical-plane orbit is generated by involutions on its actual carrier. -/
theorem criticalOrbitNative_seed_square (hb : s.geometry.b R = 2)
    {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (t : Vertex R) (y : M) (hy : y ∈ (criticalPlane R c t).comap (embedM R)) :
    y ^ 2 = 1 := by
  let := s.criticalPlane_elementary hb hc t
  apply embedM_injective R
  rw [map_pow,map_one]
  exact elemPow_eq_one_of_isElementaryAbelian (A := criticalPlane R c t) (embedM R y) hy

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
