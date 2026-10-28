module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AmbientTransport
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels

/-!
# The actual X_E image in the marked point parabolic

X_E is two-perfect and T_E is a normalizing two-group. Thus adjoining
T_E leaves the embedded two-residual equal to X_E. Residuals commute
with homomorphic images, so the same quotient and point-parabolic marking
used by the natural module sends X_E to O²(S₄). The existing compatible
parabolic action identifies that actual residual with A₄.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.67–68 and the terminal argument, printed pp.1153–1155.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G] [Finite G]

/-- Under the constructed point-parabolic marking, the actual image of X_E
is its full two-residual, hence is the compatible alternating-four group. -/
theorem terminal_lineX_marked_image (T : Sylow 2 G) (Y E F : Subgroup G)
    (f : amalgamGroup Y T E F →* Matrix.PSL3Two.SL)
    (hmark : ((secondAmalgamGroup T E).subgroupOf (amalgamGroup Y T E F)).map f =
      Matrix.PSL3Two.pointParabolicSL) :
    ((lineX E).subgroupOf (amalgamGroup Y T E F)).map f =
      Matrix.PSL3Two.MarkedAutomorphisms.residual Matrix.PSL3Two.pointParabolicSL ∧
    Nonempty ((((lineX E).subgroupOf (amalgamGroup Y T E F)).map f) ≃*
      alternatingGroup (Fin 4)) := by
  let H := amalgamGroup Y T E F
  let X := (lineX E).subgroupOf H
  let S := (lineT T E).subgroupOf H
  have hXH : lineX E ≤ H := le_sup_left.trans le_sup_right
  have hSH : lineT (T : Subgroup G) E ≤ H := le_sup_right.trans le_sup_left
  have hp : IsPPerfect 2 X := (lineX_twoPerfect E).of_surjective
    (subgroupOfEquivOfLe hXH).symm.toMonoidHom (subgroupOfEquivOfLe hXH).symm.surjective
  have hs : IsPGroup 2 S := (T.isPGroup'.to_le (show lineT (T : Subgroup G) E ≤ T from inf_le_left)).comap_subtype
  have hn : S ≤ normalizer (X : Set H) := by
    apply le_trans ?_ ((lineX E).le_normalizer_comap H.subtype)
    exact fun _ ht => lineNormalizer_le_normalizer_lineX E ht.2
  have hr := embedded_pResidual_join_pGroup X S hp hs hn
  have hjoin : X ⊔ S = (secondAmalgamGroup T E).subgroupOf H :=
    (subgroupOf_sup hXH hSH).symm
  rw [hjoin] at hr
  have hm := congrArg (fun A : Subgroup H => A.map f) hr
  rw [map_embedded_pResidual,hmark] at hm
  have he : X.map f = Matrix.PSL3Two.MarkedAutomorphisms.residual Matrix.PSL3Two.pointParabolicSL := hm.symm
  exact ⟨he,⟨(MulEquiv.subgroupCongr he).trans
    Matrix.PSL3Two.MarkedAutomorphisms.pointResidualEquivAlternating⟩⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
