module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Pair
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.LocalControl
public import Theory.GroupTheory.AbelianConjugateSpan
/-!
# The original orthogonal central-seed centralizer

In the natural O₄⁺(2) case, the image of the given Sylow subgroup is a
maximal proper subgroup of the actual orthogonal actor. Its containment
in the centralizer of Ω₁Z(T) forces that centralizer to have the same
image: a full image would centralize the entire original conjugate span,
contradicting the noncentral Thompson action. Taking the residual then
gives C_M(Ω₁Z(T)) = C_M(V(M)) T. The binary center identifies the same
central seed for every original characteristic pair.

Source: Aschbacher–Smith 14.1.7 and 14.1.11, printed pp.977–978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterB ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

theorem orthogonal_seed_centralizer_factorization
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (d : NaturalOrthogonalAction M (localModule T M))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    M ⊓ centralizer (centralInvolutions T : Set G) =
      (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) := by
  let Z := centralInvolutions T
  let N := M ⊓ centralizer (Z : Set G)
  have hTN : (T : Subgroup G) ≤ N := by
    refine le_inf hTM ?_
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hsmall : d.image N = d.image (T : Subgroup G) := by
    have hle : d.image (T : Subgroup G) ≤ d.image N := map_mono (comap_mono hTN)
    rcases (d.image_sylow_isCoatom T hTM).le_iff.mp hle with hfull | hs
    · have hord := d.orderingLE_of_image_eq_top T hfull
      have hMCZ : M ≤ centralizer (Z : Set G) := by
        intro m hm
        obtain ⟨a,ha,c,hc,rfl⟩ := hord m hm
        exact (centralizer (Z : Set G)).mul_mem ha.2.2
          (centralizer_le (le_conjugateSpanBy Z M) hc.2)
      have hMCV : M ≤ centralizer (localModule T M : Set G) :=
        le_centralizer_conjugateSpanBy_of_normalizes M Z M M.le_normalizer hMCZ
      have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
        sSup_le fun _ hA => hA.1
      exact (hJ ((hJT.trans hTM).trans hMCV)).elim
    · exact hs
  have hp : IsPGroup 2 (d.image N) := by
    rw [hsmall]
    exact (T.isPGroup'.comap_subtype (K := M)).map d.actor
  have hres := d.residual_le_centralizer_of_image_isTwoGroup (show N ≤ M from inf_le_left) hp
  refine le_antisymm (le_centralizer_of_residual_le_module_centralizer T hTN hres).1 ?_
  exact le_inf (sup_le inf_le_left hTM)
    (le_centralizer_of_residual_le_module_centralizer T hTN hres).2

theorem orthogonal_fixed_pair_centralizer_factorization
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (d : NaturalOrthogonalAction M (localModule T M))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (D : CharacteristicPair (baumann (T : Subgroup G))) :
    M ⊓ centralizer (ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D : Set G) =
      (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) := by
  rw [ChapterC.RankOne.ChiProduct.FixedPair.firstSeed_eq_omega_of_card_two T D
    (d.card_centralInvolutions T hTM)]
  exact orthogonal_seed_centralizer_factorization T hTM d hJ
end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
