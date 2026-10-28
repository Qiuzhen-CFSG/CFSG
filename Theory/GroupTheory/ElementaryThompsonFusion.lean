module
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# Elementary Thompson fusion and centralizer Sylows

The elementary Thompson subgroup J(T) is weakly closed in a Sylow
2-subgroup T: maximum elementary orders are invariant under conjugacy,
and their generated subgroups have the same order. Every two-subgroup
containing J(T) therefore normalizes it. Burnside's fusion lemma makes
N_G(J(T)) control fusion in C_G(J(T)).

If N_G(J(T)) lies in M, each point centralizer for a point in C_G(J(T))
has a Sylow subgroup in M, giving odd relative centralizer index. This
retains the actual centralizer inclusion and requires no normality of M.

Source: Aschbacher--Smith, A.1.35 and B.2.3, printed pp.30,84--85;
application to the small Thompson branch of 12.6.19, printed p.828.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- A conjugate of J(T) contained in T equals J(T). -/
theorem maxJ_weakly_closed (T : Sylow 2 G) (g : G)
    (h : (elementaryAbelianMaxJ (T : Subgroup G)).map
      (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    g ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have h' : elementaryAbelianMaxJ ((T : Subgroup G).map
      (MulAut.conj g).toMonoidHom) ≤ (T : Subgroup G) := by
    rwa [elementaryAbelianMaxJ_map_equiv]
  have hj := (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ h').2
    (elementaryAbelianMaxOrder_map_equiv (MulAut.conj g) (T : Subgroup G))
  rw [elementaryAbelianMaxJ_map_equiv] at hj
  exact eq_of_le_of_card_ge hj (by rw [card_map_of_injective (MulAut.conj g).injective])

/-- Every ambient Sylow containing J(T) has this same Thompson subgroup. -/
theorem maxJ_eq_of_sylow_overgroup (T P : Sylow 2 G)
    (h : elementaryAbelianMaxJ (T : Subgroup G) ≤ (P : Subgroup G)) :
    elementaryAbelianMaxJ (P : Subgroup G) = elementaryAbelianMaxJ (T : Subgroup G) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G T P
  have hm : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (P : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have he : elementaryAbelianMaxOrder (T : Subgroup G) =
      elementaryAbelianMaxOrder (P : Subgroup G) := by
    rw [←hm,elementaryAbelianMaxOrder_map_equiv]
  have hj := (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ h).2 he
  apply (eq_of_le_of_card_ge hj ?_).symm
  rw [←hm,elementaryAbelianMaxJ_map_equiv,card_map_of_injective (MulAut.conj g).injective]

/-- Every two-subgroup containing J(T) lies in its ambient normalizer. -/
theorem pgroup_le_normalizer_maxJ (T : Sylow 2 G) (S : Subgroup G)
    (hp : IsPGroup 2 S) (h : elementaryAbelianMaxJ (T : Subgroup G) ≤ S) :
    S ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  rw [←maxJ_eq_of_sylow_overgroup T P (h.trans hP)]
  exact hP.trans (P.toSubgroup.le_normalizer.trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ _))

/-- Burnside fusion on the full centralizer of the elementary Thompson subgroup. -/
theorem maxJ_controls_centralizer_fusion (T : Sylow 2 G)
    {x y : G} (hx : x ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hy : y ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hxy : IsConj x y) :
    ∃ n ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G),
      n*x*n⁻¹=y :=
  T.weakly_closed_normalizer_controls_centralizer_fusion _
    (sSup_le fun _ hA => hA.1) (maxJ_weakly_closed T) hx hy hxy
end Stellmacher

namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- A point centralizing J(T) has a centralizer Sylow in N_G(J(T)). -/
theorem exists_centralizer_sylow_le_maxJ_normalizer (T : Sylow 2 G)
    (x : G) (hx : x ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    ∃ S : Sylow 2 (centralizer ({x} : Set G)),
      (S : Subgroup (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let C := centralizer ({x} : Set G)
  have hJC : J ≤ C := fun j hj => mem_centralizer_singleton_iff.mpr (hx j hj)
  have hp : IsPGroup 2 J := T.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
  obtain ⟨S,hS⟩ := (hp.comap_subtype (K := C)).exists_le_sylow
  refine ⟨S,pgroup_le_normalizer_maxJ T _ (S.isPGroup'.map C.subtype) ?_⟩
  intro j hj
  exact ⟨⟨j,hJC hj⟩,hS hj,rfl⟩

/-- Normalizer containment gives odd relative index in the full point centralizer. -/
theorem odd_centralizer_index_of_maxJ_normalizer_le (T : Sylow 2 G)
    (M : Subgroup G)
    (hn : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M)
    (x : G) (hx : x ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    Odd ((M ⊓ centralizer ({x} : Set G)).relIndex (centralizer ({x} : Set G))) := by
  obtain ⟨S,hS⟩ := exists_centralizer_sylow_le_maxJ_normalizer T x hx
  let C := centralizer ({x} : Set G)
  have hs : (S : Subgroup C) ≤ (M ⊓ C).subgroupOf C := fun s hs =>
    ⟨hn (hS (mem_map_of_mem C.subtype hs)),s.property⟩
  have hodd : ¬ 2 ∣ ((M ⊓ C).subgroupOf C).index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hs))
  exact (Nat.even_or_odd _).resolve_left (fun h => hodd h.two_dvd)
end Stellmacher
