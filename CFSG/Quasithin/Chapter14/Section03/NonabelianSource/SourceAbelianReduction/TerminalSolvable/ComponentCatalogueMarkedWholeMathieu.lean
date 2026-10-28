module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeGeometry
public import CFSG.Quasithin.ChapterG.Section11.WholeSporadic
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.ElementaryFixed

/-!
# Excluding the whole marked M₁₂ component

The original G.9 degree bound recognizes the ten-dimensional heart.
The actual normal-component action extends to Aut(M₁₂), preserving its original
coordinates. The marked actor then has order sixteen and fixes at least a
plane, whereas every involution displaces more than two dimensions. Both
branches of the original FixedPointAlternative are impossible.

Source: Aschbacher–Smith G.11.7, printed p.367, and H.11.1.
-/
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

open Module ChapterH.Section10To12 ChapterH.Section10To12.M12Calculations
open Sporadic.Mathieu

/-- The two original fixed-point alternatives exclude the actual whole M₁₂. -/
theorem not_whole_mathieu_twelve (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    (e : L ≃* M12) : False := by
  have h9 := s.componentHypothesis_of_whole hi
  rw [hHL] at h9
  rcases s.fixedPointAlternative with hfix | ⟨a,_,hr,hva⟩
  swap
  · exact ChapterG.Section11.WholeSporadic.not_mathieu_twelve s.hypothesis h9
      ⟨a,a.property,hr,hva⟩ e
  let := h9.normal_H
  let := h9.irreducible
  have hd := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hd
  have hb := M12AutomorphismRank.twoRank_le_four
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  obtain ⟨f⟩ := Representation.MathieuSmall.M12Recognition.equiv_heart_of_faithful_finrank_le_ten
    σ (s.hypothesis.faithful.comp (L.subtype_injective.comp e.symm.injective)) (by omega)
  have hf (l : L) (u : Additive F.Uhat) :
      f (F.terminalRepresentation l u) = m12HeartRepresentation (e l) (f u) := by
    have hh := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (e l) u
    change f (F.terminalRepresentation (e.symm (e l)) u) = m12HeartRepresentation (e l) (f u) at hh
    rwa [e.symm_apply_apply] at hh
  let φ : F.TerminalHdot →* MulAut M12 :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := L))
  have hφ (a : F.TerminalHdot) (u : Additive F.Uhat) :
      f (F.terminalRepresentation a u) = Ambient.automorphismRepresentation (φ a) (f u) :=
    Representation.BinaryNormalExtension.equivariant F.terminalRepresentation L m12HeartRepresentation
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_inner
      (fun c hc => Ambient.heart_centralizer c hc) e f.toLinearEquiv hf a u
  have hφi : Function.Injective φ := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply s.hypothesis.faithful
    ext u
    apply f.injective
    rw [map_one,Module.End.one_apply]
    change f (F.terminalRepresentation a u) = f u
    simpa only [ha,map_one,Module.End.one_apply] using hφ a u
  let A := (F.terminalDot (F.X g)).map φ
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hdim := f.toLinearEquiv.finrank_eq
  rw [finrank_m12Heart] at hdim
  have hm := s.actor_dimension
  have hm4 : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 := by omega
  have hcard : Nat.card A = 16 := by
    rw [←Nat.card_congr ((F.terminalDot (F.X g)).equivMapOfInjective φ hφi).toEquiv]
    rw [h9.card_actor,hm4]
    norm_num
  have hlo := Ambient.ElementaryFixed.two_le_fixed_of_sixteen A hcard
  have he := fixedSpace_map_equivariant F.terminalRepresentation
    Ambient.automorphismRepresentation φ f.toLinearEquiv hφ (F.terminalDot (F.X g))
  have heq := (Submodule.equivMapOfInjective f.toLinearEquiv.toLinearMap f.injective
    (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)))).finrank_eq
  rw [he] at heq
  rw [←heq,hfix,finrank_span_singleton s.hypothesis.point_ne_zero] at hlo
  omega

/-- The impossible whole Mathieu row closes the literal original local lift. -/
theorem local_lift_of_whole_mathieu_twelve (hi : I = ⊤)
    (hHL : componentOrbit L ⊤ = L) (e : L ≃* M12) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_mathieu_twelve hi hHL e).elim

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
