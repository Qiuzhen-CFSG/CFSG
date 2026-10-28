module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Orbit

/-!
# The common edge acts on the symplectic critical plane

The actual common edge kernel fixes both endpoints, so it normalizes their
Z-layers and the maximal critical plane. Omega-one of its center is exactly
its fixed subgroup on each endpoint Z-layer and on the critical plane.
These identities supply the literal edge action in the orbit estimates of
MS93 (3.6), printed p.871; no splitting of the endpoint module is asserted.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- The common edge kernel normalizes the source's maximal critical plane. -/
theorem criticalPlane_normalized_edge (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    Q R t ≤ normalizer (criticalPlane R c t : Set (FreeAmalgam R)) := by
  have htGa : Q R t ≤ stabilizer R (alpha R) :=
    fun k hk => hk.2 (alpha R) (adjacent_symm R hat)
  have htGc : Q R t ≤ stabilizer R c :=
    fun k hk => hk.2 c (adjacent_symm R hct)
  apply le_normalizer_iff.mpr
  intro k hk y hy
  apply (s.mem_criticalPlane_iff hb hc hat hct _).mpr
  have hy' := (s.mem_criticalPlane_iff hb hc hat hct y).mp hy
  refine ⟨le_normalizer_iff.mp (Z_normalized R c) k (htGc hk) y hy'.1,?_⟩
  intro q hq
  have hq' : k⁻¹*q*k ∈ Q R (alpha R) := by
    simpa only [inv_inv] using
      le_normalizer_iff.mp (Q_normalized R (alpha R)) k⁻¹
        (htGa ((Q R t).inv_mem hk)) q hq
  have hm := hy'.2 (k⁻¹*q*k) hq'
  have hconj : (MulAut.conj k) ⁅k⁻¹*q*k,y⁆ ∈ Z R t :=
    le_normalizer_iff.mp (Z_normalized R t) k hk.1 _ hm
  rw [map_commutatorElement] at hconj
  have he : (MulAut.conj k) (k⁻¹*q*k) = q := by
    simp [MulAut.conj_apply,mul_assoc]
  rw [he] at hconj
  exact hconj

/-- The common edge layer itself lies in the maximal plane. -/
theorem edge_Z_le_criticalPlane
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
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

omit [Finite M] [L.Normal] [W.Normal] s in
/-- The part of the opposite layer already central in Q-alpha is always in Y. -/
theorem opposite_inf_X_le_criticalPlane {c t : Vertex R} :
    Z R c ⊓ X R (alpha R) ≤ criticalPlane R c t := by
  apply le_criticalPlane_of_commutator_le _ inf_le_left
  apply le_trans (commutator_mono le_rfl inf_le_right)
  rw [commutator_eq_bot_iff_le_centralizer.mpr (Q_le_centralizer_X R (alpha R))]
  exact bot_le

/-- On the original endpoint, the edge Z-layer is exactly the fixed subgroup
of the actual edge kernel on Z-alpha. -/
theorem edge_Z_eq_fixed_original {t : Vertex R}
    (hat : Adjacent R (alpha R) t) :
    Z R (alpha R) ⊓ centralizer (Q R t : Set (FreeAmalgam R)) = Z R t := by
  have ht := edge_color hat
  have hQa : Q R (alpha R) ≤ Q R t := Q_le_adjacent_h R ht hat
  have hZt : Z R t = omegaCenter (Q R t) := by
    simp only [Z,ht,Bool.true_eq_false,if_false,edgeOmega]
  have hZ : Z R t ≤ Z R (alpha R) := by
    simp only [Z,show color R (alpha R) = false from rfl,ht,
      Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le t (le_iSup_of_le hat le_rfl)
  apply le_antisymm
  · rintro x ⟨hx,hfix⟩
    rw [hZt,mem_omegaCenter_iff]
    let := s.Z_elementary
    exact ⟨hQa (omegaCenter_le _ (s.Z_le_X hx)),
      elemPow_eq_one_of_isElementaryAbelian x hx,hfix⟩
  · intro x hx
    refine ⟨hZ hx,?_⟩
    rw [hZt,mem_omegaCenter_iff] at hx
    exact hx.2.2

/-- The two endpoints use the same literal fixed edge layer. -/
theorem edge_Z_eq_fixed_opposite (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    Z R c ⊓ centralizer (Q R t : Set (FreeAmalgam R)) = Z R t := by
  have ht := edge_color hat
  have hcol := critical_endpoint_color R (alpha R) rfl _ hc
  have hpos : 0 < criticalDistance R c (s.geometry.exists_critical c hcol) := by
    rw [s.geometry.distance_constant c hcol]
    change 0 < s.geometry.b R
    omega
  have hZQ : Z R c ≤ Q R c :=
    (s.geometry.omega_bound c hcol hpos).trans (omegaCenter_le _)
  have hQc : Q R c ≤ Q R t := Q_le_adjacent_h R ht hct
  have hZt : Z R t = omegaCenter (Q R t) := by
    simp only [Z,ht,Bool.true_eq_false,if_false,edgeOmega]
  have hZ : Z R t ≤ Z R c := by
    simp only [Z,hcol,ht,Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le t (le_iSup_of_le hct le_rfl)
  apply le_antisymm
  · rintro x ⟨hx,hfix⟩
    rw [hZt,mem_omegaCenter_iff]
    let := Z_elementary_of_positive R s.geometry c hcol hpos
    exact ⟨hQc (hZQ hx),elemPow_eq_one_of_isElementaryAbelian x hx,hfix⟩
  · intro x hx
    refine ⟨hZ hx,?_⟩
    rw [hZt,mem_omegaCenter_iff] at hx
    exact hx.2.2

/-- The plane has exactly the same edge-fixed subgroup as the opposite layer. -/
theorem criticalPlane_inf_edge_centralizer (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    criticalPlane R c t ⊓ centralizer (Q R t : Set (FreeAmalgam R)) = Z R t := by
  apply le_antisymm
  · exact (inf_le_inf_right _ (criticalPlane_le_opposite c t)).trans_eq
      (s.edge_Z_eq_fixed_opposite hb hc hat hct)
  · apply le_inf (s.edge_Z_le_criticalPlane hc hat hct)
    rw [←s.edge_Z_eq_fixed_opposite hb hc hat hct]
    exact inf_le_right

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
