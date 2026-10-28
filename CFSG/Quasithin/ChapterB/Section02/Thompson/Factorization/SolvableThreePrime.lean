module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.InductionStep
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
/-!
# Solvable three-prime Thompson factorization

For a Sylow two-subgroup of rank greater than one in a finite solvable
three-prime group of characteristic two, the group is the ordered product
of the normalizers of J0(P) and Omega1 Z(J1(P)). Induction on group order
uses the local odd-section obstruction; the centralizer bound passes to
every Sylow overgroup. The embedding lemma preserves the literal product
inside an ambient group.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153. The rank restriction
is sufficient for Aschbacher–Smith 13.1.9, whose actual R has rank at least
three. No conclusion of the factorization is taken as an extra premise.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Transport the intrinsic normalizer product to its original subgroup
embedding, keeping the ordered setwise product. -/
theorem thompson_factorization_subgroup_product (X : Subgroup G) (R : Subgroup X)
    (hf : NormalizerProductOn R (normalizer (thompsonJ R 0 : Set X))
      (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set X)) ⊤) :
    (X : Set G) =
      ((X ⊓ normalizer (thompsonJ (R.map X.subtype) 0 : Set G) : Subgroup G) : Set G) *
      ((X ⊓ normalizer (omegaOneCenterAmbient (thompsonJ (R.map X.subtype) 1) : Set G) :
        Subgroup G) : Set G) := by
  have hprod : (Set.univ : Set X) = (normalizer (thompsonJ R 0 : Set X) : Set X) *
      (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set X) : Set X) := by
    simpa only [NormalizerProductOn,top_sup_eq,top_inf_eq,coe_top] using hf
  apply Set.Subset.antisymm
  · intro x hx
    have hh : (⟨x,hx⟩ : X) ∈ (normalizer (thompsonJ R 0 : Set X) : Set X) *
        (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set X) : Set X) := hprod ▸ Set.mem_univ _
    obtain ⟨a,ha,b,hb,he⟩ := hh
    refine ⟨a,⟨a.property,?_⟩,b,⟨b.property,?_⟩,congrArg Subtype.val he⟩
    · have hh := (thompsonJ R 0).le_normalizer_map X.subtype (mem_map_of_mem X.subtype ha)
      rwa [←thompsonJ_map_injective X.subtype X.subtype_injective] at hh
    · have hh := (omegaOneCenterAmbient (thompsonJ R 1)).le_normalizer_map X.subtype
        (mem_map_of_mem X.subtype hb)
      rwa [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
        ←thompsonJ_map_injective X.subtype X.subtype_injective] at hh
  · rintro x ⟨a,ha,b,hb,rfl⟩
    exact X.mul_mem ha.1 hb.1

/-- The p = 2 solvable, three-prime case of GLS G.26.18(a), in the rank
range required by the source 13.1.9 consumer. -/
theorem solvable_threePrime_thompson_factorization [Group.IsSolvable G]
    (P : Sylow 2 G) (hr : 1 < twoRank (P : Subgroup G))
    (h3 : Nat.Coprime 3 (Nat.card G))
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    NormalizerProductOn (P : Subgroup G)
      (normalizer (thompsonJ (P : Subgroup G) 0 : Set G))
      (normalizer (omegaOneCenterAmbient (thompsonJ (P : Subgroup G) 1) : Set G)) ⊤ := by
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    apply thompson_factorization_of_proper P hr h3 hself
    dsimp only
    intro D _ hproper
    let X := D ⊔ (P : Subgroup G)
    let PX : Sylow 2 X := P.subtype le_sup_right
    have hmap : (PX : Subgroup X).map X.subtype = (P : Subgroup G) :=
      map_subgroupOf_eq_of_le le_sup_right
    have hrX : 1 < twoRank (PX : Subgroup X) := by
      rw [←twoRank_map_injective X.subtype X.subtype_injective,hmap]
      exact hr
    have hcX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
      centralizer_pCore_le_of_pCore_le X hself
        ((pCore_isPGroup.le_sylow_of_normal P).trans le_sup_right)
    have hlt : Nat.card X < n := by
      have hidx : 1 < X.index := X.one_lt_index_of_ne_top hproper
      have hc := X.card_mul_index
      have hp : 0 < Nat.card X := Nat.card_pos
      rw [hn] at hc
      nlinarith
    have hf := ih (Nat.card X) hlt (G := X) PX hrX
      (h3.of_dvd_right X.card_subgroup_dvd_card) hcX rfl
    have hh := thompson_factorization_subgroup_product X (PX : Subgroup X) hf
    rw [hmap] at hh
    exact hh
end CFSG.Quasithin.ChapterB
