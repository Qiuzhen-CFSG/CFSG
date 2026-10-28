module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.PlaneGeometry

/-!
# The fifth-case obstruction inside the source MS-group

Let P be the actual Sylow subgroup of the MS-group H, embedded in the original
S. The moving plane U lies in [O₂(L),L]. The genuine component embedding
identifies that subgroup with the image of [O₂(H),L], so U lies in P.
It is P-invariant, elementary and nontrivial, hence meets Ω₁(Z(P)).
Case (5) centralizes this omega subgroup, contradicting the absence of
nonidentity Y_L-fixed points on U.

Only containment of the embedded P in S is required; equality is not assumed.
All clauses of FifthCase, including the natural quotient action and the
index-seven point radical, remain in the interface. ResidualPlaneFactors
is supplied by the separate source residual-action reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.34(5), printed p.137, and 15.3.23, printed p.1128.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
variable {G : Type*} [Group G] [Finite G]

/-- The fifth-case obstruction in the actual MS-group. Its local Sylow only
has to embed into S. The component-core bound supplies containment of U in
that local Sylow, so equality with the original S is unnecessary. -/
theorem fifthCase_impossible_in_local_group (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (H : Subgroup G) (hLH : c.L ≤ H) (hcomp : (c.L.subgroupOf H).IsCComponent)
    (P : Sylow 2 H) (hPS : (P : Subgroup H).map H.subtype ≤ d.S)
    (R : Subgroup H)
    (e : ((c.L.subgroupOf H) ⧸ pCore 2 (c.L.subgroupOf H)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hf : ResidualPlaneFactors d c.L)
    (hfive : FifthCase (c.L.subgroupOf H) R P e) : False := by
  let U := movingPlane d c.L
  have hUQ : U ≤ commutatorCore c.L :=
    (movingPlane_le_coreCenter d c hSL hcore hR).trans (map_subtype_le _)
  have hUlocal : U ≤ (sourceQ (c.L.subgroupOf H)).map H.subtype := by
    rw [CoreActions.sourceQ_map_subtype hLH hcomp]
    exact hUQ
  have hQmap : (sourceQ (c.L.subgroupOf H)).map H.subtype ≤
      (P : Subgroup H).map H.subtype :=
    map_mono ((commutator_le_left _ _).trans (pCore_isPGroup.le_sylow_of_normal P))
  have hUH : U ≤ H := hUlocal.trans (map_subtype_le _)
  have hUP : U.subgroupOf H ≤ (P : Subgroup H) := by
    intro u hu
    obtain ⟨p, hp, he⟩ := mem_map.mp (hQmap (hUlocal hu))
    have he' : p = u := Subtype.ext he
    exact he' ▸ hp
  obtain ⟨hcard, _, hn, _, hfix⟩ := movingPlane_geometry d c.L h7 hf
  have hn' : (P : Subgroup H) ≤ normalizer (U.subgroupOf H : Set H) := by
    apply le_normalizer_iff.mpr
    intro p hp u hu
    exact (hn (hPS (mem_map_of_mem H.subtype hp)) (u : G)).mp hu
  have hne : U.subgroupOf H ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map H.subtype) he
    rw [map_subgroupOf_eq_of_le hUH, Subgroup.map_bot] at hh
    change U = ⊥ at hh
    change Nat.card U = 4 at hcard
    rw [hh] at hcard
    norm_num at hcard
  have hUV : U ≤ d.V := by
    obtain ⟨_, j, _, hm, _, _, _, _⟩ := movingPlane_coordinates d c.L h7 hf
    change movingPlane d c.L ≤ d.V
    exact hm ▸ d.action.plane_le j
  let _ := d.action.elementary_of_le hUV
  let _ : IsElementaryAbelian 2 (U.subgroupOf H) :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hUH).symm.toMonoidHom
      (subgroupOfEquivOfLe hUH).symm.surjective
  have hYLH : YL d c.L ≤ H :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right).trans hLH
  have hfix' : U.subgroupOf H ⊓ centralizer ((YL d c.L).subgroupOf H : Set H) = ⊥ := by
    apply eq_bot_iff.mpr
    rintro u ⟨hu, hc⟩
    apply mem_bot.mpr
    apply Subtype.ext
    apply hfix.le
    refine ⟨hu, ?_⟩
    intro a ha
    exact congrArg Subtype.val (hc ⟨a, hYLH ha⟩ ha)
  apply centralOmega_not_le_centralizer (P : Subgroup H) (U.subgroupOf H)
    ((YL d c.L).subgroupOf H) P.isPGroup' hUP hn' hne hfix'
  intro u hu a _
  exact mem_center_iff.mp (hfive.central_omega hu) a

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
end
