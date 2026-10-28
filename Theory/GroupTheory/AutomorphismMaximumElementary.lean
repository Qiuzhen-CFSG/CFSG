module

public import Theory.GroupTheory.SubgroupAutomorphismImages
public import Stellmacher.ElementaryAbelianMaxSylowImages
public import Theory.PGroupCore
/-!
# Maximum elementary subgroups under restricted Sylow automorphisms

An automorphism of a Sylow subgroup transports its maximum elementary
subgroups inside the same ambient Sylow. The proof factors through the
subgroup-of-S equivalence and the public injective-family transport theorem.
This is the exact replacement-family input for Campbell II.5.3 and II.6.3.
-/

public section
open Subgroup Stellmacher
namespace Subgroup
variable {G : Type*} [Group G]

theorem automorphismImage_maxElementary (S : Subgroup G) (a : MulAut S) (A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    automorphismImage S a A ∈ elementaryAbelianMaxSubgroups S := by
  have hm : (A.subgroupOf S).map S.subtype=A := map_subgroupOf_eq_of_le hA.1
  have htop : (⊤ : Subgroup S).map S.subtype=S := by rw [←MonoidHom.range_eq_map,range_subtype]
  have hs : A.subgroupOf S ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by
    apply (maxFamily_map_injective_iff S.subtype S.subtype_injective ⊤ (A.subgroupOf S)).mp
    rwa [htop,hm]
  have ha : (A.subgroupOf S).map a.toMonoidHom ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by
    have hh := (maxFamily_map_injective_iff a.toMonoidHom a.injective ⊤ (A.subgroupOf S)).mpr hs
    rwa [map_top_of_surjective _ a.surjective] at hh
  have hout := (maxFamily_map_injective_iff S.subtype S.subtype_injective ⊤
    ((A.subgroupOf S).map a.toMonoidHom)).mpr ha
  rwa [htop] at hout

variable [Finite G]
theorem maxElementary_conjugate_of_le_core (S : Sylow 2 G) (g : G) (A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)) (hAQ : A ≤ pCore 2 G) :
    A.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups (S : Subgroup G) := by
  apply (maxFamily_sylow_iff S _).mpr
  have hQ : (pCore 2 G).map (MulAut.conj g).toMonoidHom = pCore 2 G :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  refine ⟨(map_mono hAQ).trans (hQ.le.trans (pCore_isPGroup.le_sylow_of_normal S)),?_⟩
  have hh := (maxFamily_map_injective_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective ⊤ A).mpr
    ((maxFamily_sylow_iff S A).mp hA).2
  rwa [map_top_of_surjective _ (MulAut.conj g).surjective] at hh
end Subgroup
