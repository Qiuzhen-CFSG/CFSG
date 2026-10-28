module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction.Reduction
public import Theory.ElementaryAbelian.FivePlaneGeometry

/-!
# Elementary geometry for the Sylow-five orbit calculation

The two numerical premises of
`FourLineFrame.twoOrbitConclusion_of_plane_geometry_and_recognition` are
proved here for the original elementary abelian group and its actual
subgroup of automorphisms. The stabilizer uses precisely the pointwise
subgroup action, so `h • L` is `L.map h.val.toMonoidHom`.

The projective-line count and full-automorphism transitivity are proved in
`Theory.ElementaryAbelian.FivePlaneGeometry`. This adapter discharges `h6`
and `hstab` in the final paragraph of Aschbacher, *Sporadic Groups* (1994),
47.2, printed p.261. Recognition of the order-twelve actor and the final
`TwoOrbitConclusion` assembly remain with the linear-calculation consumer.
-/

open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 5 E]

/-- The exact `h6` and `hstab` inputs of the existing two-orbit calculation,
with no frame or recognition hypothesis. -/
public theorem plane_geometry (hE : Nat.card E = 25) (H : Subgroup (MulAut E)) :
    (Nat.card {L : Subgroup E // Nat.card L = 5} = 6) ∧
      ∀ L : Subgroup E, Nat.card L = 5 → Nat.card (MulAction.stabilizer H L) ∣ 80 :=
  ⟨IsElementaryAbelian.FivePlaneGeometry.card_lines hE,
    IsElementaryAbelian.FivePlaneGeometry.stabilizer_card_dvd hE H⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
