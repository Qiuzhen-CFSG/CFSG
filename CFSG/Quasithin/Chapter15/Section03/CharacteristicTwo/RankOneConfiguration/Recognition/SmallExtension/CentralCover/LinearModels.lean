module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels.Marking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels.StarCompatibility

/-!
# The marked coefficient models for the three surviving binary MS cases

Starting from the genuine classified module configurations in C.1.34(1)--(3),
these constructors realize Z(Q)/C_Z(Q)(L) for Q = [O₂(L),L]. Cases (1) and
(2) start with coordinates on Q; case (3) starts with coordinates on its full
center. A natural constituent contains the marked V₂-plane, and the relative
normalizer is the source parabolic M ∩ L. The earlier identity
Y₊ = O^{3′}(M ∩ L) then gives both marked matrices after a simultaneous change
of coordinates on the quotient actor and every natural copy.

The result retains the actual quotient isomorphism, literal center quotient,
conjugation compatibility, elementary whole center and O₂(L)-centralization.
It feeds LinearThree's already proved extension calculation. No cocycle
detection, marked-matrix membership or recognition conclusion is an input.
The earlier MS classification and construction of the source V₂-plane remain
explicit inputs, as required by this conditional model-construction contract.

For the source application take E = V₂, P = M ∩ L and Y = Y₊. The ambient
residual equality is supplied by LocalGeometry.componentIntersection_residual
in the earlier parabolic development. StarCompatibility uses the actual
relative-normality/Sylow quotient comparison from SmallExtension.Quotient.

Source: Aschbacher--Smith, C.1.31--34, B.4.8, I.1.5--6, and the proof of
15.3.31, printed pp.1130--1132 (PDF pp.1147--1149). The model witnesses here
supply the binary SL₃ calculation, whose group is absent from I.2.3's list.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
open LinearThree LinearModels
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable {L : Subgroup G} {ρ : Representation (ZMod 2) SL V}

/-- The result includes the chosen coordinates and their quotient marking. -/
structure MarkedModel (c : FullCenter L ρ) (Y : Subgroup G) where
  model : CenterModel L ρ
  changeOfCoordinates : SL
  quotient_marking : model.quotientIso = c.quotientIso.trans (MulAut.conj changeOfCoordinates)
  whole_coordinates : ∀ z : coreCenter L, model.coordinates z =
    Multiplicative.ofAdd (ρ changeOfCoordinates (c.equiv z).toAdd)
  elementary : IsElementaryAbelian 2 (coreCenter L)
  transvection_mem : planeTransvection ∈ (Y.subgroupOf L).map model.actorMap
  rotation_mem : planeRotation ∈ (Y.subgroupOf L).map model.actorMap

namespace MarkedModel

/-- The new quotient marking is an explicitly chosen inner change of coordinates. -/
theorem actorMap_eq {c : FullCenter L ρ} {Y : Subgroup G}
    (m : MarkedModel c Y) (l : L) :
    m.model.actorMap l = m.changeOfCoordinates * c.actor l * m.changeOfCoordinates⁻¹ := by
  change m.model.quotientIso (QuotientGroup.mk' (pCore 2 L) l) = _
  rw [m.quotient_marking]
  rfl

/-- In particular the marking still commutes with the literal component star map. -/
theorem actorMap_eq_star (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hn : (c.L.subgroupOf I).Normal)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = d.S)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    {ρ : Representation (ZMod 2) SL V} (f : FullCenter c.L ρ)
    (q : d.starImage I c.L ≃* SL)
    (hq : f.quotientIso = (coreQuotientEquivStar d c hn S hS).trans q)
    {Y : Subgroup G} (m : MarkedModel f Y) (l : c.L) :
    m.model.actorMap l =
      m.changeOfCoordinates * q (componentMap d c l) * m.changeOfCoordinates⁻¹ := by
  rw [m.actorMap_eq]
  change m.changeOfCoordinates * f.quotientIso (QuotientGroup.mk' (pCore 2 c.L) l) * _ = _
  rw [hq]
  rfl

end MarkedModel

private theorem construct [Finite G] (c : FullCenter L ρ)
    {E Y : Subgroup G} (m : MarkedPlane c E)
    (hres : Y.subgroupOf L = (primeToResidual 3 ((normalizer (E : Set G)).subgroupOf L)).map
      ((normalizer (E : Set G)).subgroupOf L).subtype)
    (hfixed : ∀ v : V, (∀ a : SL, ρ a v = v) → v = 0) :
    Nonempty (MarkedModel c Y) := by
  obtain ⟨a,ha⟩ := PlaneGeometry.exists_plane_coordinates m.space m.dimension
  let c' := c.recoordinate a
  let model := c'.model hfixed
  have hmem := PlaneGeometry.marked_mem_image c.actor
    ((normalizer (E : Set G)).subgroupOf L) (Y.subgroupOf L) hres
    m.space m.parabolic_image a ha
  exact ⟨⟨model, a, rfl, fun _ => rfl, c.elementary, hmem.1, hmem.2⟩⟩

private theorem natural_fixed (v : Space) (h : ∀ a : SL, natural a v = v) : v = 0 :=
  fixed_marked_matrices_eq_zero v (h _) (h _)

private theorem two_natural_fixed (v : Space × Space)
    (h : ∀ a : SL, (natural.prod natural) a v = v) : v = 0 := by
  apply Prod.ext
  · exact natural_fixed v.1 (fun a => congrArg Prod.fst (h a))
  · exact natural_fixed v.2 (fun a => congrArg Prod.snd (h a))

private theorem residual_subgroupOf [Finite G] (P : Subgroup G) (hPL : P ≤ L) :
    ((primeToResidual 3 P).map P.subtype).subgroupOf L =
      (primeToResidual 3 (P.subgroupOf L)).map (P.subgroupOf L).subtype := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hPL),
    map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le hPL]

private theorem residual_normalizer [Finite G] {E P Y : Subgroup G}
    (hP : P = L ⊓ normalizer (E : Set G))
    (hY : Y = (primeToResidual 3 P).map P.subtype) :
    Y.subgroupOf L = (primeToResidual 3 ((normalizer (E : Set G)).subgroupOf L)).map
      ((normalizer (E : Set G)).subgroupOf L).subtype := by
  have hPL : P ≤ L := hP ▸ inf_le_left
  rw [hY, residual_subgroupOf P hPL]
  have hP' : P.subgroupOf L = (normalizer (E : Set G)).subgroupOf L := by
    ext l
    change (l : G) ∈ P ↔ (l : G) ∈ normalizer (E : Set G)
    rw [hP, mem_inf]
    exact and_iff_right l.property
  rw [hP']

/-- Case (3), using its actual whole natural center and the source marked plane. -/
theorem caseThree [Finite G] (c : FullCenter L natural)
    {E P Y : Subgroup G} (m : MarkedPlane c E)
    (hP : P = L ⊓ normalizer (E : Set G))
    (hY : Y = (primeToResidual 3 P).map P.subtype) :
    Nonempty (MarkedModel c Y) :=
  construct c m (residual_normalizer hP hY) natural_fixed

/-- Case (1), starting with coordinates on Q rather than assuming Z(Q)=Q. -/
theorem caseOne [Finite G] (c : AbelianCore L natural)
    {E P Y : Subgroup G} (m : MarkedPlane c.fullCenter E)
    (hP : P = L ⊓ normalizer (E : Set G))
    (hY : Y = (primeToResidual 3 P).map P.subtype) :
    Nonempty (MarkedModel c.fullCenter Y) :=
  construct c.fullCenter m (residual_normalizer hP hY) natural_fixed

/-- Case (2): both isomorphic natural copies retain one common actor marking. -/
theorem caseTwo [Finite G] (c : AbelianCore L (natural.prod natural))
    {E P Y : Subgroup G} (m : MarkedPlane c.fullCenter E)
    (hP : P = L ⊓ normalizer (E : Set G))
    (hY : Y = (primeToResidual 3 P).map P.subtype) :
    Nonempty (MarkedModel c.fullCenter Y) :=
  construct c.fullCenter m (residual_normalizer hP hY) two_natural_fixed

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels
