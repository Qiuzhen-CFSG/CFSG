module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.OriginalSelection
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.OriginalSquares
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Involutions
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Exceptional-branch elimination with original source inputs

The original involution nonfusion and center marks supply the fusion rule.
The original Sylow subgroup in C_G(t) gives its exact intersection with T.
Apply the A₈ reduction to obtain the dihedral core; its concrete square
calculation then discharges every square, quotient-index and selection premise
of the exceptional elimination theorem. The matching equalities retain the
literal S, S_C, t and crossing element of the original configuration.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 2.5.26, p.569.
The overcomponent owner supplies the marked exceptional LocalData; no
classification alternative is assumed proved here.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne
open A6Shadow.Frattini
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

/-- The source nonfusion excludes z from the possible conjugates of t in
its central four-group, retaining the original crossing element. -/
theorem original_central_fusion (d : EarlierSetup κ G) (g : G)
    (hg : MulAut.conj g d.t ∈ zpowers d.t ⊔ zpowers d.z) :
    MulAut.conj g d.t = d.t ∨ MulAut.conj g d.t = MulAut.conj d.x d.t := by
  have ht2 : d.t * d.t = 1 := by
    simpa only [d.t_order, pow_two] using pow_orderOf_eq_one d.t
  have hz2 : d.z * d.z = 1 := by
    simpa only [d.z_order, pow_two] using pow_orderOf_eq_one d.z
  have hzZ : d.z ∈ centerIn (d.T : Subgroup G) := by
    rw [d.center_t]
    exact mem_zpowers d.z
  have htz : Commute d.t d.z := hzZ.2 d.t (d.s_le_t (d.sc_le_s d.t_mem))
  have hmem : MulAut.conj g d.t ∈ closure ({d.t, d.z} : Set G) := by
    simpa only [zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union] using hg
  rcases (mem_closure_pair_iff d.t d.z ht2 hz2 htz _).mp hmem with h | h | h | h
  · have ho := (MulAut.conj g).orderOf_eq d.t
    rw [h, orderOf_one, d.t_order] at ho
    omega
  · exact Or.inl h
  · exfalso
    apply d.t_not_conjugate_z g
    rw [← h]
    simp only [MulAut.conj_apply]
    group
  · exact Or.inr (h.trans (d.conj_t_eq_right.trans d.crossing_t).symm)

/-- The original source Sylow mark computes C_T(t) exactly. -/
theorem original_sylow_centralizer (d : EarlierSetup κ G) :
    (d.T : Subgroup G) ⊓ centralizer ({d.t} : Set G) = d.S := by
  obtain ⟨P, hP⟩ := d.sylow_centralizer_t
  have hle : (P : Subgroup (centralizer ({d.t} : Set G))) ≤
      (d.T : Subgroup G).subgroupOf (centralizer ({d.t} : Set G)) := by
    intro s hs
    exact d.s_le_t (hP ▸ mem_map_of_mem _ hs)
  have he := P.is_maximal' d.T.isPGroup'.comap_subtype hle
  have hm := congrArg (Subgroup.map (centralizer ({d.t} : Set G)).subtype) he
  change ((d.T : Subgroup G).subgroupOf (centralizer ({d.t} : Set G))).map _ = _ at hm
  rwa [subgroupOf_map_subtype, hP] at hm

/-- Actual exceptional consumer: the original setup supplies selection,
quotient index, central fusion, Sylow intersection and dihedral squares.
Only the genuine marked A₈ alternative remains with its source producer. -/
theorem original_exceptional_branch_impossible (d : EarlierSetup κ G)
    (l : A8Reduction.LocalData G)
    (hS : l.S = d.S) (hSC : l.SC = d.SC) (ht : l.t = d.t) (hx : l.x = d.x⁻¹) : False := by
  have hz : d.z = d.t * d.zK :=
    (d.involution_identities_of_frattini_ne (hSC ▸ l.frattini_ne)).2
  have hquot : (l.SC.subgroupOf l.S).index = 32 := by
    rw [hSC, hS]
    exact original_core_index d
  obtain ⟨⟨e⟩, _⟩ := A8Reduction.dihedral_and_cyclicFour_of_localData
    l d.simpleQTKE.quasithin hquot
  have e' : d.SC ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hSC.symm).trans e
  apply exceptional_branch_impossible l d.simpleQTKE.quasithin d.T d.M d.z hquot
  · simpa only [ht, hS] using original_sylow_centralizer d
  · rw [hx]
    exact (d.T : Subgroup G).inv_mem d.x_mem
  · simpa only [hx, hS, inv_mem_iff] using d.x_outside
  · intro V v hV hgen hv hvt a ha haV hao
    simpa only [ht] using original_squares_of_dihedral d e' hz V v (hSC ▸ hV) hgen hv
      (ht ▸ hvt) a (hS ▸ ha) haV hao
  · intro g hg
    rcases original_central_fusion d g (ht ▸ hg) with h | h
    · exact Or.inl (by simpa only [ht] using h)
    · apply Or.inr
      rw [ht, hx]
      rw [d.conj_t_eq_right] at h
      simpa only [MulAut.conj_apply, inv_inv] using h
  · exact original_earlierSelection d
  · exact d.even_empty

end CFSG.Quasithin.Chapter2.A6ShadowRankOne
