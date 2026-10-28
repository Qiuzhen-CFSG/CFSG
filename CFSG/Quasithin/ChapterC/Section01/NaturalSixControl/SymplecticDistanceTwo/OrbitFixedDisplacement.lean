module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitLinearMovement
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitIndex
public import Theory.Representation.BinaryConjugationSection.FixedDisplacement

/-!
# The actual critical-orbit fixed-kernel displacement bound

The representation-theoretic fixed-space containment is pulled back through
the original orbit quotient and projected actor, then mapped through the
specified free-amalgam embedding. Thus its output is the literal graph bound
D <= [A,B]Z-alpha used in the paired-orbit elementary-kernel argument. The
linear input is the output of natural-section and augmentation-cover
recognition for the same orbit action; no subgroup identification is replaced
by an abstract model.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem orbitFixedKernel_le_commutator_sup_of_linear_bound
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    [IsElementaryAbelian 2 (OrbitQuotient R c b)]
    (hsurj : Function.Surjective s.projection)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hfix : fixedSpace (s.orbitFullRepresentation hb hc hab hcb hsurj) (alternatingGroup (Fin 6)) ≤
      subspaceCommutator (s.orbitFullRepresentation hb hc hab hcb hsurj) ⊤ (s.orbitActorImage B)) :
    (orbitFixedKernel L R c b).map (embedM R) ≤
      ⁅criticalOrbit R c b,B⁆ ⊔ Z R (alpha R) := by
  let ρ := s.orbitFullRepresentation hb hc hab hcb hsurj
  let π := s.projection.comp (⊤ : Subgroup M).subtype
  let B0 := B.comap (embedM R)
  have hLmap : (L.subgroupOf ⊤).map π = alternatingGroup (Fin 6) := by
    rw [show π = s.projection.comp (⊤ : Subgroup M).subtype from rfl,←Subgroup.map_map,
      map_subgroupOf_eq_of_le (show L ≤ ⊤ from le_top),s.component_image]
  have hBmap : (B0.subgroupOf ⊤).map π = s.orbitActorImage B := by
    rw [show π = s.projection.comp (⊤ : Subgroup M).subtype from rfl,←Subgroup.map_map,
      map_subgroupOf_eq_of_le (show B0 ≤ ⊤ from le_top)]
    rfl
  have hfix0 : fixedSpace (ρ.comp π) (L.subgroupOf ⊤) ≤
      subspaceCommutator (ρ.comp π) ⊤ (B0.subgroupOf ⊤) := by
    rw [fixedSpace_comp_map,subspaceCommutator_comp_map,hLmap,hBmap]
    exact hfix
  have hh := (s.orbitFullSection hb hc hab hcb hsurj).fixedPreimage_le_commutator_sup_of_fixed_le_moved
    L B0 le_top le_top (by rw [normalizer_eq_top];exact le_top) hfix0
  have hBG : B ≤ stabilizer R (alpha R) :=
    (hBQ.trans (Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color hab) hcb)).trans
      (fun _ hx => hx.2 _ (adjacent_symm R hab))
  have hBm : B0.map (embedM R) = B := by
    rw [show B0 = B.comap (embedM R) from rfl,map_comap_eq,inf_eq_right.mpr]
    exact hBG.trans_eq (stabilizer_m_base R)
  have hZm : (orbitLayer R).map (embedM R) = Z R (alpha R) := by
    change ((Z R (alpha R)).comap (embedM R)).map (embedM R) = _
    rw [map_comap_eq,inf_eq_right.mpr]
    exact (Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R)
  have hm := map_mono (f := embedM R) hh
  rw [Subgroup.map_sup,map_commutator,hBm,hZm] at hm
  exact hm
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
