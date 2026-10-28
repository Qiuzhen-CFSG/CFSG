module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitMovement
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitFaithful
public import Theory.Representation.BinaryConjugationSection.FullMovement
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Whole component movement of the actual orbit representation

The native full-edge calculation gives A=[A,L]Z-alpha. Pullback along the
literal free-amalgam embedding and the actual orbit coordinates show that the
whole orbit quotient is moved by its A6 component. Transport to the specified
S6 projection keeps the same representation and component marking. This
supplies the full-movement input to natural central-cover recognition in
MS93 (3.6), printed p.871.
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

theorem criticalOrbitNative_eq_commutator_sup_layer
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b) :
    criticalOrbitNative R c b = ⁅L,criticalOrbitNative R c b⁆ ⊔ orbitLayer R := by
  apply map_injective (embedM_injective R)
  rw [Subgroup.map_sup,map_commutator,←s.residual,←Ltilde_alpha]
  have hz : (orbitLayer R).map (embedM R) = Z R (alpha R) := by
    change ((Z R (alpha R)).comap (embedM R)).map (embedM R) = _
    rw [map_comap_eq,inf_eq_right.mpr]
    exact (Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R)
  rw [hz,commutator_comm]
  exact s.criticalOrbit_eq_commutator_sup_Z_of_full_image h t hfull hb hlarge hc hab hcb himage

theorem orbitRepresentation_component_movement
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b)
    [IsElementaryAbelian 2 (OrbitQuotient R c b)] :
    subspaceCommutator (orbitRepresentation R c b) ⊤ (L.subgroupOf ⊤) = ⊤ :=
  (orbitSection R c b (s.orbitLayer_le_orbit hb hc hab hcb)).subspaceCommutator_eq_top_of_movement
    L le_top (s.criticalOrbitNative_eq_commutator_sup_layer h t hfull hb hlarge hc hab hcb himage)

theorem orbitFullRepresentation_component_movement
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b)
    [IsElementaryAbelian 2 (OrbitQuotient R c b)]
    (hsurj : Function.Surjective s.projection) :
    subspaceCommutator (s.orbitFullRepresentation hb hc hab hcb hsurj) ⊤
      (alternatingGroup (Fin 6)) = ⊤ := by
  have hm := (s.orbitFullSection hb hc hab hcb hsurj).subspaceCommutator_eq_top_of_movement
    L le_top (s.criticalOrbitNative_eq_commutator_sup_layer h t hfull hb hlarge hc hab hcb himage)
  rw [subspaceCommutator_comp_map,←Subgroup.map_map,
    map_subgroupOf_eq_of_le (show L ≤ ⊤ from le_top),s.component_image] at hm
  exact hm
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
