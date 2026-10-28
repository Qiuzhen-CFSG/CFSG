module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.WholeActor
public import CFSG.Quasithin.ChapterB.Section02.WreathThompson
/-!
# The cyclic-four Thompson step on the original outside omega orbit

For the original outside group H, the whole natural quotient action is
already supplied by 13.2.8. The reduced omega-orbit module lies in O₂(H),
so it lies in the source subgroup R. If the image of R is cyclic of order
four and its centralizer intersection is exactly O₂(H), the actual
maximum-elementary offender argument proves J(R)=J(O₂(H)). Normality is
then transported to the ambient G, giving H≤N_G(J(R)).

The construction of R and the stated image/kernel facts are the preceding
part of original 13.2.9, retained with its assembly. No fixed-space bound,
Thompson containment, or complement hypothesis is assumed here.

Source: Aschbacher–Smith, original 13.2.9, final paragraph, printed p.881.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]
/-- The actual source omega-orbit action forces H to normalize the original
Thompson subgroup whenever the preceding R-construction has cyclic-four image. -/
theorem source_cyclicFour_thompson
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (R : Subgroup H) :
    let U := (omegaOrbit T H).subgroupOf H
    let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
    let := hU.normal
    let := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    pCore 2 H ≤ R →
    pCore 2 H = R ⊓ centralizer (U : Set H) →
    IsCyclic (R.map q) → Nat.card (R.map q) = 4 →
      ChapterB.thompsonJ R 0 = ChapterB.thompsonJ (pCore 2 H) 0 ∧
        (ChapterB.thompsonJ R 0).Normal ∧
        H ≤ normalizer (ChapterB.thompsonJ (R.map H.subtype) 0 : Set G) := by
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  dsimp only
  intro hQR hcore hcyclic hcard
  let := hcyclic
  have hresult := ChapterB.smallNatural_thompson_eq_of_cyclicFour_image U
    (QuotientGroup.mk' (centralizer (U : Set H)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    R (hU.le_pCore.trans hQR) hQR hcore
    (source_solvable_whole_omega_action d hH hB hZ hs) hcard
  let := hresult.2
  refine ⟨hresult.1,hresult.2,?_⟩
  have hn : H ≤ normalizer ((ChapterB.thompsonJ R 0).map H.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] using
      (ChapterB.thompsonJ R 0).le_normalizer_map H.subtype
  simpa only [ChapterB.thompsonJ_zero,
    elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective] using hn
end CFSG.Quasithin.Chapter13.Section02.A5Outside
