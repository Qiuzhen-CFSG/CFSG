module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSliceShift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRestrictedOrbit
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusAlignment

/-!
# The actual small-slice orbit line in the cubic plane branch

Use the single forward endpoint and residual conjugator of SmallSliceShift.
Its full centralizer orbit lies in the old endpoint core, and its shifted
critical image is small on both covers. The original plane radius comparison
therefore identifies its full reverse-kernel commutator R₃ with the entire
last-edge radius-kernel commutator. This is an order-two line in the midpoint
seed, noncentral at the endpoint and aligned with the critical line modulo
the entire endpoint center.

Adjoining the midpoint seed does not change R₃, by the actual radius-kernel
identity, so the alignment theorem applies without a false containment of
the midpoint seed in the original orbit. No point-core image is assumed and
no full predecessor-core equality is claimed. The remaining source choice
independence and span comparison are separate obligations.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed p.921.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- The actual shifted orbit has a full-kernel line of order two, with its
complete endpoint-center alignment and noncentrality retained. -/
theorem plane_orbitDisplacement_alignment
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let c := p.walk.getVert 2
    let z := s.endpoint
    let t := s.path.walk.getVert (s.path.walk.length-1)
    let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
    Nat.card s.orbitDisplacement = 2 ∧
      ⁅V Rg c ⊓ Q Rg t,Z Rg z ⊓ Q Rg c⁆ = s.orbitDisplacement ∧
      s.orbitDisplacement ≤ Z Rg c ∧
      s.orbitDisplacement < ⁅s.seedOrbit,Z Rg z⁆ ∧
      s.orbitDisplacement ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ ∧
      s.orbitDisplacement ⊔ C = ⁅Z Rg c,Z Rg z⁆ ⊔ C := by
  have hb2 : 2 < sourceDistance h := by omega
  have hel := (plane_critical_paths h e hz hk u hR p).2.2.2
  have hs : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    rw [(s.shifted_indices e hz hk hb hsmall hslice hel).1]
    decide
  have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  let c := p.walk.getVert 2
  let t := s.path.walk.getVert (s.path.walk.length-1)
  have hzt : Adjacent Rg s.endpoint t := by
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
    rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
      s.path.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [s.path.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpre : s.path.walk.getVert (s.path.walk.length-2) = a' := by
    have hp : p.walk.length = sourceDistance h := p.length_eq_b
    rw [show s.path.walk.length-2=p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  have hpred : Q Rg a' ≤ Q Rg t := by
    rw [←hpre]
    apply Q_le_adjacent_h Rg ht
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
    rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hDt : s.seedOrbit ≤ Q Rg t :=
    (s.centralizer_orbits_le_old_endpoint_core e hz hk hb hsmall hslice hel).1.trans hpred
  have hDV := (s.seedOrbit_radius_and_escape e hz hb2).1
  have hn := s.seedOrbit_endpoint_commutator_not_le e hz hb2
  have hd := plane_radius_subactor_kernel_line h e hz hk u hR s.path hs
    s.seedOrbit hDV hDt hn
  let Y := s.seedOrbit ⊔ Z Rg c
  have hZt : Z Rg c ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ s.path.start_color)
    rw [(sourceGeometry h).distance_constant _ s.path.start_color,
      s.path.dist_start (Nat.sub_le _ _)]
    change s.path.walk.length-1 < sourceDistance h
    omega
  have hYV : Y ≤ V Rg c := sup_le hDV (Z_le_VBall Rg c 2)
  have hYt : Y ≤ Q Rg t := sup_le hDt hZt
  have he : ⁅Y,Z Rg s.endpoint ⊓ Q Rg c⁆ = s.orbitDisplacement :=
    le_antisymm ((commutator_mono (le_inf hYV hYt) le_rfl).trans_eq hd.2.1)
      (commutator_mono le_sup_left le_rfl)
  have ha := plane_radius_kernel_alignment h e hz hk u hR s.path hs
    Y hYV hYt le_sup_right
    (fun hh => hn ((commutator_mono le_sup_left le_rfl).trans hh))
  rw [he] at ha
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,ha.2.2.2.2.1,ha.2.2.2.2.2⟩

end SmallSliceShift
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
