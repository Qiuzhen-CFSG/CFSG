module
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.QuotientParabolics
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking

/-!
# Lifting source rank-two residues

A surjection lifts the two specified maximal parabolics, their intersection,
and the exhaustive maximal-overgroup description through its actual kernel.
For a quotient isomorphic to PSL₃(2) with two-group kernel, two proper
non-two-group overgroups of a Sylow subgroup are therefore the full pair
of parabolics whenever their intersection is that Sylow subgroup.

The model step uses the existing binary Bruhat classification, and all
source transport uses the literal quotient map. This is the local lattice
step used in Aschbacher--Smith, I.5 and 13.7.6(1), printed pp.419--420 and940.
-/

@[expose] public section
open Subgroup
namespace Quasithin.I5.RankTwoParabolics
variable {G A : Type*} [Group G] [Group A] {B P R : Subgroup A}
theorem comap_surjective (h : RankTwoParabolics A B P R)
    (f : G →* A) (hf : Function.Surjective f) :
    RankTwoParabolics G (B.comap f) (P.comap f) (R.comap f) := by
  refine ⟨isCoatom_comap_of_surjective hf h.left_maximal,
    isCoatom_comap_of_surjective hf h.right_maximal,
    fun he => h.distinct (comap_injective hf he),
    (comap_inf P R f).symm.trans (congrArg (comap f) h.borel_eq), ?_⟩
  intro U hBU hU
  have hk : f.ker ≤ U := (by intro x hx; change f x ∈ B; rw [hx]; exact B.one_mem :
    f.ker ≤ B.comap f).trans hBU
  have hc : (U.map f).comap f = U := comap_map_eq_self hk
  have hmax : IsCoatom (U.map f) := by
    refine ⟨?_,?_⟩
    · intro he
      exact hU.1 (by rw [←hc,he,comap_top])
    · intro V hv
      have hlt : U < V.comap f := by
        rw [←hc]
        exact (comap_lt_comap_of_surjective hf).mpr hv
      exact comap_injective hf ((hU.2 _ hlt).trans (comap_top f).symm)
  have hb : B ≤ U.map f := by
    rw [←map_comap_eq_self_of_surjective hf B]
    exact map_mono hBU
  rcases h.exhaustive _ hb hmax with he | he
  · exact Or.inl (hc.symm.trans (congrArg (comap f) he))
  · exact Or.inr (hc.symm.trans (congrArg (comap f) he))

theorem symm (h : RankTwoParabolics A B P R) : RankTwoParabolics A B R P :=
  ⟨h.right_maximal,h.left_maximal,Ne.symm h.distinct,
    (inf_comm _ _).trans h.borel_eq,fun U hB hU => (h.exhaustive U hB hU).symm⟩
end Quasithin.I5.RankTwoParabolics

namespace Quasithin.I5.RankTwoParabolics
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem of_psl_model (e : G ≃* Matrix.PSL3Two.PSL) (S : Sylow 2 G)
    (P R : Subgroup G) (hP : P ≠ ⊤) (hR : R ≠ ⊤)
    (hnP : ¬ IsPGroup 2 P) (hnR : ¬ IsPGroup 2 R)
    (hi : P ⊓ R = (S : Subgroup G)) :
    RankTwoParabolics G (S : Subgroup G) P R := by
  have hSP : (S : Subgroup G) ≤ P := hi ▸ inf_le_left
  have hSR : (S : Subgroup G) ≤ R := hi ▸ inf_le_right
  have hPR : P ≠ R := by
    intro he
    have heP : P = (S : Subgroup G) := by simpa only [←he,inf_idem] using hi
    exact hnP (heP ▸ S.isPGroup')
  obtain ⟨hp,em,Q,hs,hpmark,hqmark,hqmax,hqP,hsQ,hPQ,hcases⟩ :=
    Matrix.PSL3Two.exists_compatible_parabolic_marking e S P hSP hP hnP
  have hr := (Matrix.PSL3Two.exists_compatible_parabolic_marking e S R hSR hR hnR).1
  have hRQ : R = Q := ((hcases R hr).mp hSR).resolve_left (Ne.symm hPR)
  refine ⟨hp,hr,hPR,hi,?_⟩
  intro U hSU hU
  rcases (hcases U hU).mp hSU with he | he
  · exact Or.inl he
  · exact Or.inr (he.trans hRQ.symm)

theorem of_psl_two_quotient (N : Subgroup G) [N.Normal] (hn : IsPGroup 2 N)
    (e : (G ⧸ N) ≃* Matrix.PSL3Two.PSL) (S : Sylow 2 G)
    (P R : Subgroup G) (hP : P ≠ ⊤) (hR : R ≠ ⊤)
    (hnP : ¬ IsPGroup 2 P) (hnR : ¬ IsPGroup 2 R)
    (hi : P ⊓ R = (S : Subgroup G)) :
    RankTwoParabolics G (S : Subgroup G) P R := by
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hk : q.ker ≤ (S : Subgroup G) := by
    rw [QuotientGroup.ker_mk']
    exact hn.le_sylow_of_normal S
  have hSP : (S : Subgroup G) ≤ P := hi ▸ inf_le_left
  have hSR : (S : Subgroup G) ≤ R := hi ▸ inf_le_right
  have hc (U : Subgroup G) (hSU : (S : Subgroup G) ≤ U) :
      (U.map q).comap q = U := comap_map_eq_self (hk.trans hSU)
  have hproper (U : Subgroup G) (hSU : (S : Subgroup G) ≤ U) (hu : U ≠ ⊤) :
      U.map q ≠ ⊤ := by
    intro he
    exact hu (by rw [←hc U hSU,he,comap_top])
  have hnotTwo (U : Subgroup G) (hSU : (S : Subgroup G) ≤ U) (hu : ¬ IsPGroup 2 U) :
      ¬ IsPGroup 2 (U.map q) := by
    intro hh
    apply hu
    rw [←hc U hSU]
    exact hh.comap_of_ker_isPGroup q (by rw [QuotientGroup.ker_mk']; exact hn)
  have hmeet : P.map q ⊓ R.map q = ((S : Subgroup G).map q) := by
    apply comap_injective hq
    rw [comap_inf,hc P hSP,hc R hSR,hc _ le_rfl,hi]
  have hm := of_psl_model e (S.mapSurjective hq) (P.map q) (R.map q)
    (hproper P hSP hP) (hproper R hSR hR)
    (hnotTwo P hSP hnP) (hnotTwo R hSR hnR) hmeet
  have hl := hm.comap_surjective q hq
  change RankTwoParabolics G (((S : Subgroup G).map q).comap q)
    ((P.map q).comap q) ((R.map q).comap q) at hl
  rw [hc P hSP,hc R hSR,hc _ le_rfl] at hl
  exact hl
end Quasithin.I5.RankTwoParabolics


