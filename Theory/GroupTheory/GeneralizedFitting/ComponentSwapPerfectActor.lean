module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormFixedSeed
public import Theory.GroupTheory.ComponentPairRankDescent
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# Perfect pointwise actors on a normal exchanged component pair

The normal pair has exactly two conjugate components. Perfectness forces the actor group into the component stabilizer of index two. Fixing the norm diagonal pointwise then centralizes the first factor, and commutation with the swapping actor centralizes the second.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup
namespace Theory.GroupTheory.NormPair
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {a : G}

/-- A perfect group fixing the norm diagonal pointwise cannot interchange the
normal pair, and therefore centralizes both factors. -/
theorem perfect_actor_centralizes_normal_pair
    (hL : IsComponent G L) (hm : L.map (MulAut.conj a).toMonoidHom ≠ L)
    [(L ⊔ L.map (MulAut.conj a).toMonoidHom).Normal]
    (C : Subgroup G) [Group.IsPerfect C]
    (hCa : C ≤ centralizer ({a} : Set G))
    (hCD : C ≤ centralizer (normRange hL hm : Set G)) :
    C ≤ centralizer ((L ⊔ L.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) := by
  let : (L ⊔ L.conjBy a).Normal := by
    change (L ⊔ L.map (MulAut.conj a).toMonoidHom).Normal
    infer_instance
  have hi : (normalizer (L : Set G)).index = 2 :=
    ComponentPairRankDescent.component_normalizer_index_two_of_normal_pair L hL a hm.symm
  have hCN : C ≤ normalizer (L : Set G) := le_of_isPerfect_of_index_eq_two C _ hi
  intro c hc
  have hca : Commute c a := mem_centralizer_singleton_iff.mp (hCa hc)
  have hLc := centralizes_norm_normalizes_component hL hm hca (hCN hc) (hCD hc)
  have hLac : c ∈ centralizer (L.map (MulAut.conj a).toMonoidHom : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    have hcy : Commute c y := (hLc y hy).symm
    exact ((hca.mul_right hcy).mul_right hca.inv_right).eq.symm
  have hp : L ⊔ L.map (MulAut.conj a).toMonoidHom ≤ centralizer ({c} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hLc x hx))
      (fun x hx => mem_centralizer_singleton_iff.mpr (hLac x hx))
  exact fun x hx => mem_centralizer_singleton_iff.mp (hp hx)
end Theory.GroupTheory.NormPair
