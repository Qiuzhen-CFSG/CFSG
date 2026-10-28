module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.OmegaOneCenterMap

/-!
# Applying solvable Thompson factorization to the radical core

For H = Ξ_q(L)R, the setup proves that R is Sylow, H is solvable, and its
prime divisors are 2 and q. The earlier local characteristic-two hypothesis
places Ξ_q(L)T in He and supplies F*(H) = O₂(H). The full B.2.16 theorem,
retained as an explicit universal input, now factors H: its other alternative
would give an actual L₂(2) section and hence a divisor 3 of |H|.

Injective-map transport identifies J of the Sylow witness and its omega-center
with the subgroups formed intrinsically in R. Mapping the product back to G
then gives the literal normalizer-centralizer factorization used on printed
p.513 in the proof of Aschbacher–Smith Proposition 1.3.8 (1 March 2004
combined manuscript). No factorization or characteristic-two conclusion is
assumed for the particular group H.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem factorization_transport (X R : Subgroup G) (S : Sylow 2 (X ⊔ R : Subgroup G))
    (hS : (S : Subgroup (X ⊔ R : Subgroup G)).map (X ⊔ R).subtype = R)
    (hf : (Set.univ : Set (X ⊔ R : Subgroup G)) =
      (normalizer (elementaryAbelianMaxJ (S : Subgroup (X ⊔ R : Subgroup G)) :
        Set (X ⊔ R : Subgroup G)) : Set (X ⊔ R : Subgroup G)) *
      (centralizer (omegaOneCenterAmbient (S : Subgroup (X ⊔ R : Subgroup G)) :
        Set (X ⊔ R : Subgroup G)) : Set (X ⊔ R : Subgroup G))) :
    ThompsonFactorization X R := by
  let H := X ⊔ R
  have hJ : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      (elementaryThompsonIn R).map R.subtype := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hS]
    rw [elementaryThompsonIn, ChapterB.thompsonJ_zero,
      ← elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective]
    simp only [← MonoidHom.range_eq_map, range_subtype]
  have hZ : (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype =
      (omegaCenterIn R).map R.subtype := by
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective, hS]
    rfl
  apply Set.Subset.antisymm
  · intro g hg
    have hmem : (⟨g, hg⟩ : H) ∈ (Set.univ : Set H) := Set.mem_univ _
    rw [hf] at hmem
    obtain ⟨n, hn, c, hc, he⟩ := hmem
    have hn' : (n : G) ∈ normalizer
        ((elementaryThompsonIn R).map R.subtype : Set G) := by
      rw [← hJ]
      exact (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
        (mem_map_of_mem H.subtype hn)
    have hc' : (c : G) ∈ centralizer ((omegaCenterIn R).map R.subtype : Set G) := by
      rw [← hZ]
      exact map_centralizer_le_centralizer_image _ H.subtype
        (mem_map_of_mem H.subtype hc)
    exact ⟨n, ⟨n.property, hn'⟩, c, ⟨c.property, hc'⟩, congrArg Subtype.val he⟩
  · rintro g ⟨n, hn, c, hc, rfl⟩
    exact H.mul_mem hn.1 hc.1

/-- The exact B.2.16 application in the two-prime case of 1.3.8.
The only earlier theorem inputs are universal solvable Thompson factorization
and the local characteristic-two condition on overgroups of T. -/
theorem thompsonFactorization_of_B216 (hB : ThompsonSource.TheoremB216.{u})
    (p q : ℕ) [Fact q.Prime] (hq : Odd q) (hlarge : 5 ≤ q)
    {L T : Subgroup G} (hL : L ∈ Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hlocal : HOver G (T : Set G) ⊆ He G) :
    ThompsonFactorization (XiP q L) (radicalCore p L T) := by
  have hHe : XiP q L ⊔ T ∈ He G :=
    hlocal ⟨XiP_join_mem_H q hL, fun _ hx => Subgroup.mem_sup_right hx⟩
  obtain ⟨S, hS⟩ := radicalCore_sylow_XiP_join p q hq hL.2.1 hT
  apply factorization_transport (XiP q L) (radicalCore p L T) S hS
  exact ThompsonSource.factorization_of_three_coprime hB
    (XiP_join_radicalCore_solvable p q hq hT)
    (XiP_join_radicalCore_generalizedFitting p q hL.2.1 hT hHe)
    (XiP_join_radicalCore_three_coprime p q hq hlarge hT) S

end CFSG.Quasithin.Chapter1.RadicalNormalizers
