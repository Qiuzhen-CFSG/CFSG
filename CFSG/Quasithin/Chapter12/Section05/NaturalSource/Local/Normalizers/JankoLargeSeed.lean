module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoActorSeed
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoLocalAlignment
public import Theory.SpecificGroups.Janko4.Model.SylowOvergroups.PrimeTwentyThree

/-!
# The native large-seed branch for the original J₄ actor

The actor seed constructed from the literal original `Y`-closure is retained
through the point-component equivalence.  If its order reaches the native
`2^11` threshold, the checked J₄ Sylow-overgroup placement puts the *same*
projected actor in a conjugate of the native Mathieu local.  The parabolic and
actor still use the original point-core map and the original full Sylow; the
existing Sylow alignment then removes the conjugator from the actor side.

This is the source-faithful large-seed branch of 12.5.4.  It does not assert
the missing threshold or the cross-row incidence theorem; those remain the
precise premises for the eventual native cover application.
Source: Aschbacher--Smith 12.5.4, printed p.819/PDF p.836, together with the
native J₄ Sylow-overgroup placement.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- A large elementary seed in the actual original actor gives a native max1
placement for that actor, and hence the original ambient normalizer. -/
theorem local_normalizer_le_M_of_janko_large_elementary_seed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hlarge : 2048 ≤ Nat.card
      (omegaCenterIn ((conjugateSpanBy
        (((s.pointCoreImage s.Y).subgroupOf (s.pointCoreImage K)).map e.toMonoidHom)
        (((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map e.toMonoidHom)).pCoreIn 2))) :
    s.marking.Gi i ≤ s.marking.M := by
  let C := s.pointCoreImage K
  let Y := (s.pointCoreImage s.Y).subgroupOf C
  let A0 := (s.localPointProjection K i).subgroupOf C
  let U := Y.map e.toMonoidHom
  let A := A0.map e.toMonoidHom
  let N := conjugateSpanBy U A
  let E := omegaCenterIn (N.pCoreIn 2)
  have hseed := s.point_projection_janko_elementary_seed h hK hN e
    (Or.inl hplace) i hi
  dsimp only [C, Y, A0, U, A, N, E] at hseed ⊢
  rcases hseed with ⟨_, hcoreA, hEne, hEelem, hEA, hAnorm⟩
  obtain ⟨S, hS, hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRA : (R : Subgroup Janko4.Model) ≤ A := map_mono hSA
  let EA : Subgroup A := E.subgroupOf A
  let : EA.Normal := (normal_subgroupOf_iff_le_normalizer hEA).mpr hAnorm
  let : IsElementaryAbelian 2 EA := IsElementaryAbelian.subgroupOf hEA
  have hEAcard : Nat.card EA = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv
  change 2048 ≤ Nat.card E at hlarge
  have hlargeA : 2048 ≤ Nat.card EA := hlarge.trans_eq hEAcard.symm
  obtain ⟨g, hAg⟩ := Janko4.SylowOvergroups.normal_large_placement R A hRA EA hlargeA
  apply s.local_normalizer_le_M_of_janko_conjugate_max1 h hK hLK hN e hplace i hi g
  exact hAg

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
