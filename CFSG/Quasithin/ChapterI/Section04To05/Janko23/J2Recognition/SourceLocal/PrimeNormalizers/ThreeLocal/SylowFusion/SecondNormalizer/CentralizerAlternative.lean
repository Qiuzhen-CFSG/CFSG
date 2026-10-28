module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative.Descent
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative.Splitting
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.SmallBranch
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# Recognition and lifting of the second cubic centralizer alternatives

The selected geometry constructs the full local involution geometry, giving
the Brauer–Suzuki–Wall configuration on the actual quotient C_G(⟨y⟩)/⟨y⟩,
whose possibilities are A₄ and A₅.
In the A₄ case the quotient Sylow four-group is normal. A central-kernel
normalizer comparison lifts this to normality of the original root
four-group itself. In the A₅ case the central three-kernel splits.

This proves the centralizer alternative in Aschbacher, *Sporadic Groups*
(1994), 47.3, printed p.262. Every involution is covered by the Sylow and
fusion calculations, not just the selected root involution. The normal
and nonnormal cases are retained by the A₄/A₅ recognition alternative.
The final family theorem discharges all local-geometry premises using
`SelectedGeometry`; neither ambient simplicity nor the ambient order is
needed. Neither the first cubic centralizer nor the second-normalizer
conclusion is used.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

variable {G : Type*} [Group G] [Finite G] {D : Seed G}
private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Normality lifts to the actual root four-group across the central kernel,
provided its literal placement as a Sylow subgroup has been established. -/
theorem rootNormal_of_quotientRoot_normal
    {S : InvolutionGeometry.SelectedGeometry D} {y : G}
    (hS : ∃ P : Sylow 2 (cubicCentralizer y),
      (P : Subgroup (cubicCentralizer y)) = centralizerRoot S y)
    (hN : (quotientRoot S y).Normal) : RootNormal S y := by
  obtain ⟨P, hP⟩ := hS
  have hk : (cubicQuotientMap y).ker ≤ center (cubicCentralizer y) := by
    rw [cubicQuotientMap_ker]
    exact cubicKernel_le_center y
  have hn := P.normalizer_comap_of_central_kernel (cubicQuotientMap y)
    (cubicQuotientMap_surjective y) hk
  have himage : (P.mapSurjective (cubicQuotientMap_surjective y) :
      Subgroup (CubicQuotient y)) =
      quotientRoot S y := by
    change (P : Subgroup (cubicCentralizer y)).map (cubicQuotientMap y) = _
    rw [hP]
    rfl
  change (normalizer ((P.mapSurjective (cubicQuotientMap_surjective y) :
    Subgroup (CubicQuotient y)) :
    Set (CubicQuotient y))).comap (cubicQuotientMap y) =
    normalizer ((P : Subgroup (cubicCentralizer y)) : Set (cubicCentralizer y)) at hn
  rw [himage, normalizer_eq_top_iff.mpr hN, comap_top] at hn
  have hPN : (P : Subgroup (cubicCentralizer y)).Normal :=
    normalizer_eq_top_iff.mp hn.symm
  rw [hP] at hPN
  exact hPN

private theorem rootNormal_of_quotient_alternatingFour
    {S : InvolutionGeometry.SelectedGeometry D} {y : G}
    (hS : ∃ P : Sylow 2 (cubicCentralizer y),
      (P : Subgroup (cubicCentralizer y)) = centralizerRoot S y)
    (e : CubicQuotient y ≃* alternatingGroup (Fin 4)) : RootNormal S y := by
  obtain ⟨P, hP⟩ := hS
  let Q := P.mapSurjective (cubicQuotientMap_surjective y)
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let : Subsingleton (Sylow 2 (alternatingGroup (Fin 4))) :=
    alternatingGroup.subsingleton_two_sylow (by simp)
  have hR : (R : Subgroup (alternatingGroup (Fin 4))).Normal := R.normal_of_subsingleton
  have hQ : (Q : Subgroup (CubicQuotient y)).Normal := hR.of_map_injective e.injective
  apply rootNormal_of_quotientRoot_normal ⟨P, hP⟩
  change ((centralizerRoot S y).map (cubicQuotientMap y)).Normal
  rw [← hP]
  exact hQ

/-- Recognition of the quotient and both lifting arguments, with the
geometric computations still explicit. -/
theorem centralizer_alternative_of_local_geometry
    {S : InvolutionGeometry.SelectedGeometry D} {y : G} (hyo : orderOf y = 3)
    (L : CubicLocalGeometry S y) :
    RootNormal S y ∨ Nonempty (cubicCentralizer y ≃*
      (Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) := by
  obtain ⟨h⟩ := quotient_dihedral_geometry hyo L
  obtain ⟨b, _, _, hk⟩ := h.exists_brauerSuzukiWallHypotheses
  have htwo : Nat.card b.K = 2 := by simpa using hk
  rcases CFSG.Quasithin.alternating_four_or_five_of_bsw_card_two b htwo with h4 | h5
  · exact Or.inl (rootNormal_of_quotient_alternatingFour L.root_sylow h4.some)
  · exact Or.inr (cubicCentralizer_equiv_of_quotient_alternatingFive hyo h5.some)

/-- Consumer of an explicit local-geometry family at every cubic element of
the literal component. The source assembly below constructs this family. -/
theorem centralizerAlternatives_of_local_geometry
    (S : InvolutionGeometry.SelectedGeometry D)
    (hlocal : ∀ y : G, y ∈ InvolutionGeometry.rootComponent S.t → orderOf y = 3 →
      Nonempty (CubicLocalGeometry S y)) : CentralizerAlternatives S := by
  intro y hy hyo
  obtain ⟨L⟩ := hlocal y hy hyo
  exact centralizer_alternative_of_local_geometry hyo L

/-- The source alternative for each cubic element in the selected component:
the actual root four-group is normal in its centralizer, or that centralizer
is C₃ × A₅. All involution geometry is supplied by the selected model. -/
theorem centralizer_alternative (S : InvolutionGeometry.SelectedGeometry D)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent S.t) (hyo : orderOf y = 3) :
    RootNormal S y ∨ Nonempty (cubicCentralizer y ≃*
      (Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) := by
  obtain ⟨L⟩ := Geometry.nonempty_cubicLocalGeometry S hy hyo
  exact centralizer_alternative_of_local_geometry hyo L

/-- The complete centralizer-alternative family from the earlier selected
geometry. This discharges the recognition premise of
`normal_root_of_centralizer_alternatives` without using its first-centralizer
or five-local hypotheses. -/
theorem centralizerAlternatives (S : InvolutionGeometry.SelectedGeometry D) :
    CentralizerAlternatives S := by
  intro y hy hyo
  exact centralizer_alternative S hy hyo

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
