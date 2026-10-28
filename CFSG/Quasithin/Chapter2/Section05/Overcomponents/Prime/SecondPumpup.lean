module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.OrdinarySource

/-!
# The second ordinary pumpup retaining the original small component

At the second application of I.3.2, the seed is a larger component P,
not the original K. An embedding of K supplies the rank needed to promote
the invariant two-component to an ordinary component. The exchanged case
is ordinary by the existing nonnormal two-component theorem.

Source: Aschbacher–Smith 2.5.19, printed pp.563–564.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection

/-- Apply I.3.2 to a larger seed admitting the original source K. -/
theorem source_embedded_seed_pumpup_ordinary {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (P : Subgroup G) (f₀ : K →* P) (hf₀ : Function.Injective f₀)
    (i j : G) (hi : orderOf i = 2) (hij : Commute i j)
    (hPj : P ≤ centralizer ({j} : Set G))
    (hPi : IsComponentIn P (centralizer ({i} : Set G)))
    (hj : orderOf j = 2) :
    ∃ hiJ : i ∈ centralizer ({j} : Set G),
      let Gj := centralizer ({j} : Set G)
      let iJ : Gj := ⟨i, hiJ⟩
      let D := P.subgroupOf Gj
      let L := componentOrbit D (oddELayer Gj)
      (IsComponent Gj L ∧ L.map (MulAut.conj iJ).toMonoidHom = L) ∨
        ∃ J : Subgroup Gj, IsComponent Gj J ∧ J ≠ J.map (MulAut.conj iJ).toMonoidHom ∧
          L = J ⊔ J.map (MulAut.conj iJ).toMonoidHom ∧
          Nonempty ((J ⧸ oddTwoCore J) ≃* (P ⧸ oddTwoCore P)) := by
  have hGj := hG.involution_centralizer_sqtk hj
  obtain ⟨hiJ, _, hcases⟩ := twoComponent_pumpup P i j hi hij hPj hPi
  let Gj := centralizer ({j} : Set G)
  let iJ : Gj := ⟨i, hiJ⟩
  let D := P.subgroupOf Gj
  let L := componentOrbit D (oddELayer Gj)
  refine ⟨hiJ, ?_⟩
  rcases hcases with ⟨hL,hfix⟩ | ⟨J,hJ,hne,hL,he⟩
  · let e : D ≃* P := subgroupOfEquivOfLe hPj
    let f : K →* L := (inclusion (le_componentOrbit D (oddELayer Gj))).comp
      (e.symm.toMonoidHom.comp f₀)
    have hf : Function.Injective f := (inclusion_injective (le_componentOrbit D
      (oddELayer Gj))).comp (e.symm.injective.comp hf₀)
    exact Or.inl ⟨⟨hL.1.subnormal,
      source_twoComponent_quasisimple c hG hempty hgen hb hGj hL f hf⟩,hfix⟩
  · have hn : ¬ J.Normal := fun h => hne ((normal_iff_map_conj_eq.mp h iJ).symm)
    exact Or.inr ⟨J,⟨hJ.1.subnormal,
      ChapterI.RankTwoSource.twoComponent_quasisimple_of_not_normal hGj hJ hn⟩,
      hne,hL,he⟩

end CFSG.Quasithin.Chapter2.Section05.Overcomponents
