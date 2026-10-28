module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.ConjugatorGeometry
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The normalization contradiction for the original component

The prime-to-three residual of the ordinary layer is characteristic in the
plane centralizer. The same l normalizes the plane, hence this embedded
residual. If comparison identifies K with that residual, K centralizes both
U and its l-conjugate and therefore all of V, contradicting its escape.
The residual equality is an explicit, still substantive comparison premise;
this module does not assert the ordinary-component exclusion without it.
Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815.
-/
public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- Normalizing the actual component by a hyperplane-moving l gives the
source contradiction, using the literal conjugate rather than a replacement. -/
theorem Configuration.false_of_component_normalized (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {l : G} (hl : l ∈ L) (hm : l ∉ normalizer (U : Set G))
    (hsq : l ^ 2 ∈ normalizer (U : Set G))
    (hlK : l ∈ normalizer (K : Set G)) : False := by
  have hg := c.conjugate_plane_geometry hl hm hsq
  have heK : K.map (MulAut.conj l).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp hlK
  have hc : K ≤ centralizer (U.map (MulAut.conj l).toMonoidHom : Set G) := by
    have hh := (map_mono (f := (MulAut.conj l).toMonoidHom) hK.1).trans
      (map_centralizer_le_centralizer_image (U : Set G) (MulAut.conj l).toMonoidHom)
    rwa [heK] at hh
  have hKV : K ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hg.1]
    exact sup_le (le_centralizer_iff.mp hK.1) (le_centralizer_iff.mp hc)
  exact c.component_not_le_normalizer hK (hKV.trans (Subgroup.centralizer_le_normalizer _))

/-- The source residual convention is O^{3'}(E(C_G(U₀))), embedded by the
successive subtype maps. Its equality with K forces normalization by l. -/
theorem Configuration.component_normalized_of_plane_residual (c : Configuration T L V U)
    {K : Subgroup G} {l : G} (hl : l ∈ L)
    (hm : l ∉ normalizer (U : Set G)) (hsq : l ^ 2 ∈ normalizer (U : Set G))
    (he : K =
      ((primeToResidual 3 (componentLayer
        (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G)))).map
          (componentLayer (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G))).subtype).map
            (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G)).subtype) :
    l ∈ normalizer (K : Set G) := by
  let U₀ := U ⊓ U.map (MulAut.conj l).toMonoidHom
  let H := centralizer (U₀ : Set G)
  let E := componentLayer H
  let R := (primeToResidual 3 E).map E.subtype
  have hnH : l ∈ normalizer (H : Set G) :=
    normalizer_le_normalizer_centralizer U₀ (c.conjugate_plane_geometry hl hm hsq).2.2.2
  have hnR : l ∈ normalizer (R.map H.subtype : Set G) :=
    normalizer_le_normalizer_characteristic_image H R hnH
  exact he ▸ hnR

/-- Literal consumer of the A.3.12 comparison and odd-index residual equality. -/
theorem Configuration.false_of_component_plane_residual (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {l : G} (hl : l ∈ L) (hm : l ∉ normalizer (U : Set G))
    (hsq : l ^ 2 ∈ normalizer (U : Set G))
    (he : K =
      ((primeToResidual 3 (componentLayer
        (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G)))).map
          (componentLayer (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G))).subtype).map
            (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G)).subtype) : False :=
  c.false_of_component_normalized hK hl hm hsq
    (c.component_normalized_of_plane_residual hl hm hsq he)
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
