module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Seeds
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.GroupTheory.CComponent.ResidualLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.Quasithin.Rank
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Lifting a moved component into the literal local family

The kernel of the star action is not assumed solvable. Instead, A.3.9(1)
applied in the component preimage, after its two-core quotient, gives the
residual-generation theorem needed to lift a C-component. The universal
A.3.8(3) implication gives one or two conjugates in G_v, hence the Sylow
orbit is normal. Perfectness and Thompson commutator generation give all
remaining X-family clauses; 13.6.12 then supplies actual movement of z.

The lifted subgroup belongs to Chapter 1's genuine local family by 1.2.6.
Its star image is the specified ordinary component, whose two-core is
trivial because the ambient star two-core is trivial.

This is a conditional lifting theorem. Producing the moved component
from the FF classification and the solvable exclusion is a separate
obligation, retained by Existence. It is not a proof of Y_z nonemptiness
from the earlier local setup alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
paragraph following 13.6.13 on printed p.929, with 1.2.1 and 1.2.6,
printed pp.503–506.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem sqtk_twoCore_quotient {𝒦 : GroupClass.{u}} (h : IsSQTK 𝒦 G) :
    IsSQTK 𝒦 (G ⧸ pCore 2 G) := by
  refine ⟨?_, h.isKGroup.quotient (pCore 2 G)⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

/-- Lift a specified Thompson-generated component, retaining its exact star
image, ambient C-component status, and every literal Y_z clause. The full
universal A.3.8(3) and A.3.9(1) implications are explicit earlier-source inputs. -/
theorem exists_mem_Yz_of_moved_component {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel B)
    (L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hcore : Gv v ∈ Chapter1.H G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (E : Subgroup (Gstar z v)) (hE : IsComponent (Gstar z v) E)
    (hcomm : ⁅E, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ = E) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn (Gv v) ∧
      starImage z v K = E ∧ K ∈ Yz L T z v := by
  have hgen : cComponentLayer (E.comap (starMk z v)) =
      solvableResidual (E.comap (starMk z v)) :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9 hA39
      (sqtk_twoCore_quotient (hlocal.subgroup _))
  obtain ⟨B, hB, hBE⟩ := exists_cComponent_map_eq_of_preimage_layer
    (starMk z v) (starMk_surjective z v) hE.isCComponent hgen
  let K := B.map (Gv v).subtype
  have hKG : K ≤ Gv v := map_subtype_le B
  have hBK : K.subgroupOf (Gv v) = B :=
    comap_map_eq_self_of_injective (Gv v).subtype_injective B
  have hKcomp : K ∈ Chapter1.cComponentsIn (Gv v) := ⟨hKG, hBK.symm ▸ hB⟩
  have hKE : starImage z v K = E := by
    change (K.subgroupOf (Gv v)).map (starMk z v) = E
    rw [hBK, hBE]
  obtain ⟨S, hS⟩ := hSyl
  have hTS : (Tv T v).subgroupOf (Gv v) = (S : Subgroup (Gv v)) := by
    rw [← hS]
    exact comap_map_eq_self_of_injective (Gv v).subtype_injective _
  have hTSstar : (S : Subgroup (Gv v)).map (starMk z v) = starImage z v (Tv T v) := by
    rw [starImage, hTS]
  have hJstar :
      (Stellmacher.elementaryAbelianMaxJ (S : Subgroup (Gv v))).map (starMk z v) =
        starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) := by
    have hi : (Stellmacher.elementaryAbelianMaxJ (S : Subgroup (Gv v))).map
        (Gv v).subtype = Stellmacher.elementaryAbelianMaxJ (Tv T v) := by
      rw [← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Gv v).subtype_injective, hS]
    rw [starImage, ← hi]
    change _ = (((Stellmacher.elementaryAbelianMaxJ (S : Subgroup (Gv v))).map
      (Gv v).subtype).comap (Gv v).subtype).map (starMk z v)
    rw [comap_map_eq_self_of_injective (Gv v).subtype_injective]
  let X := conjugateSpanBy E (starImage z v (Tv T v))
  have hXnormal : X.Normal := by
    have hn := conjugateSpanBy_sylow_normal B S
      ((Chapter1.Section02.proposition_1_2_1_three_index_of_A_3_8 hA38
        (sqtk_twoCore_quotient hlocal) hB).imp_right And.left)
    have hm := hn.map (starMk z v) (starMk_surjective z v)
    rwa [map_conjugateSpanBy, hBE, hTSstar] at hm
  let : X.Normal := hXnormal
  let : IsQuasisimple E := hE.2
  let : Group.IsPerfect X := conjugateSpanBy_isPerfect E _
  have hres : pResidual 2 X = ⊤ := by
    apply (pResidual_eq_top_iff 2 X).mpr
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hperfect : (pResidual 2 X).map X.subtype = X := by
    rw [hres, ← MonoidHom.range_eq_map, range_subtype]
  have hXne : X ≠ ⊥ := fun he => hE.isCComponent.ne_bot
    (bot_unique ((le_conjugateSpanBy E _).trans he.le))
  have hJle : Stellmacher.elementaryAbelianMaxJ (S : Subgroup (Gv v)) ≤
      (S : Subgroup (Gv v)) := sSup_le fun A hA => hA.1
  have hSJ : (S : Subgroup (Gv v)) ≤ normalizer
      (Stellmacher.elementaryAbelianMaxJ (S : Subgroup (Gv v)) : Set (Gv v)) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ (S : Subgroup (Gv v))).map
      (MulAut.conj s).toMonoidHom = _
    rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv]
    have he : (S : Subgroup (Gv v)).map (MulAut.conj s).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup (Gv v)).le_normalizer hs)
    rw [he]
  have hXcomm : ⁅X, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ = X := by
    apply commutator_conjugateSpanBy_eq_self
    · rw [← hJstar, ← hTSstar]
      exact map_mono hJle
    · rw [← hJstar, ← hTSstar]
      exact (map_mono hSJ).trans (le_normalizer_map _)
    · exact hcomm
  have hXF : X ∈ XFamily L T z v :=
    ⟨⟨by rw [normalizer_eq_top]; exact le_top, hperfect, hXne, hXcomm⟩, hXnormal⟩
  have hEcore : pCore 2 E = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hE.1, hstarCore]
    exact E.ker_subtype
  have hEquot : IsQuasisimple (E ⧸ pCore 2 E) :=
    IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hEcore).trans QuotientGroup.quotientBot).symm
  refine ⟨K, hKcomp, hKE, ?_⟩
  refine ⟨⟨hKG, Chapter1.mem_L_of_cComponent hcore ⟨S, hS⟩ hKG hKcomp.2⟩, ?_, ?_⟩
  · exact (congrArg (fun D : Subgroup (Gstar z v) =>
      IsQuasisimple (D ⧸ pCore 2 D)) hKE).mpr hEquot
  · rw [hKE]
    exact XFamily_subset_Xz L T z v hXF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
