module
public import Theory.GroupTheory.CoreCentralNormalizerAction
/-!
# Normalization of literal core-central actor images

If A normalizes R, their images under the normalizer action on the
central core quotient of K retain that normalization. No containment
of either image in the inner automorphism group is assumed.

Source application: Aschbacher–Smith C.4.5, printed p.152.
-/
public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G]

theorem coreCentralActorImage_normalizes (K A R : Subgroup G)
    (hAR : A ≤ normalizer (R : Set G)) :
    coreCentralActorImage K A ≤ normalizer (coreCentralActorImage K R : Set (MulAut (coreCentralQuotient K))) := by
  let N := normalizer (K : Set G)
  have hn : A.subgroupOf N ≤ normalizer (R.subgroupOf N : Set N) := by
    intro a ha r
    exact hAR ha r
  exact (map_mono hn).trans ((R.subgroupOf N).le_normalizer_map (normalizerCoreCentralAction K))
end Subgroup
