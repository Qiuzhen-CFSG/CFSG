module

public import BenderSuzuki.SE.Models
public import Theory.GroupAction.AutomorphismFixedTransport
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Unitary

/-!
# Automorphism fixed subgroups for the local Bender argument

The final paragraph of GLS, Volume 4, Chapter 2, Proposition 4.4 uses
Chapter 4, Lemma 3.4(c) and its rank-one consequence. The required model
calculations concern the actual fixed subgroup of an arbitrary automorphism
whose square is one, including the identity automorphism.

The three model calculations are transported through the actual isomorphisms
in `IsSimpleBenderGroup`. If the fixed subgroup contains no elementary four,
the group is PSL₂(4), the automorphism is outer, and its fixed subgroup is
PSL₂(2), containing an involution. If the fixed subgroup has a normal Sylow
2-subgroup, the automorphism is inner. The Suzuki calculation retains the
exponent 2m+1 with m ≥ 1, and the unitary calculation retains both the matrix
field and Hermitian fixed-field cardinalities.

In the local application these results apply to D/O_{2'}(D). Transport from
D to that quotient requires separate odd-kernel centralizer arguments; none
of the equivalences here deletes a kernel.
-/

namespace BenderSuzuki.ZD

open PFAppendixIII PFchapter1section1 _root_.BenderSuzuki.MatrixGroups

/-- The elementary-four obstruction transports through the actual model isomorphism. -/
public theorem fixedSubgroup_twoRank_congr
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (a : MulAut G) :
    TwoRankAtLeastTwo a.fixedSubgroup ↔
      TwoRankAtLeastTwo (MulAut.congr e a).fixedSubgroup := by
  let f := MulAut.fixedSubgroupCongr e a
  exact ⟨fun h => h.map_of_injective f.toMonoidHom f.injective,
    fun h => h.map_of_injective f.symm.toMonoidHom f.symm.injective⟩

/-- Normality is inside the fixed group, and is preserved under model transport. -/
public theorem fixedSubgroup_normalSylow_congr
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (a : MulAut G) :
    (∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) ↔
      ∃ Q : Sylow 2 (MulAut.congr e a).fixedSubgroup,
        (Q : Subgroup (MulAut.congr e a).fixedSubgroup).Normal :=
  (MulAut.fixedSubgroupCongr e a).exists_normal_sylow_iff 2

/-- Even ambient order supplies the fixed involution needed in the rank-one branch. -/
public theorem exists_fixed_involution_of_even
    {G : Type*} [Group G] [Finite G] (a : MulAut G) (ha : a ^ 2 = 1)
    (heven : Even (Nat.card G)) :
    ∃ x : G, x ∈ a.fixedSubgroup ∧ IsInvolution x := by
  obtain ⟨x, hx, ho⟩ := MulAut.exists_fixed_orderOf_eq_two a ha heven
  obtain ⟨hsq, hne⟩ := (orderOf_eq_prime_iff).mp ho
  exact ⟨x, (MulAut.mem_fixedSubgroup a x).mpr hx, hne, hsq⟩

/-- The no-four case in the final paragraph of GLS IV, Chapter 2,
Proposition 4.4. Both identifications are actual group isomorphisms:
the Bender group is PSL₂(4), and its fixed subgroup is PSL₂(2).
The automorphism is outer. -/
public theorem bender_rank_one_fixed_models
    {B : Type*} [Group B] [Finite B] (hB : IsSimpleBenderGroup B)
    (a : MulAut B) (ha : a ^ 2 = 1)
    (hrank : ¬ TwoRankAtLeastTwo a.fixedSubgroup) :
    Nonempty (B ≃* PSL2BinaryMatrixGroup 2) ∧
      (¬ ∃ b : B, a = MulAut.conj b) ∧
      Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup 1) := by
  rcases hB with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩⟩
  · have ha' : (MulAut.congr e a) ^ 2 = 1 := by
      simpa only [map_pow, map_one] using congrArg (MulAut.congr e) ha
    have hrank' : ¬ TwoRankAtLeastTwo (MulAut.congr e a).fixedSubgroup :=
      fun h => hrank ((fixedSubgroup_twoRank_congr e a).mpr h)
    obtain ⟨hn2, houter, _⟩ := Linear.rank_one_obstruction hn _ ha' hrank'
    subst n
    obtain ⟨f⟩ := Linear.outer_fixed_model_two _ ha' houter
    exact ⟨⟨e⟩, fun hi => houter ((MulAut.congr_inner_iff e a).mpr hi),
      ⟨(MulAut.fixedSubgroupCongr e a).trans f⟩⟩
  · have ha' : (MulAut.congr e a) ^ 2 = 1 := by
      simpa only [map_pow, map_one] using congrArg (MulAut.congr e) ha
    obtain ⟨_, _, hfour⟩ := suzuki_involutoryAut_inner_and_twoRank m hm _ ha'
    exact (hrank ((fixedSubgroup_twoRank_congr e a).mpr hfour)).elim
  · let : Field E := hEfield
    let : Finite E := hEfinite
    have ha' : (MulAut.congr e a) ^ 2 = 1 := by
      simpa only [map_pow, map_one] using congrArg (MulAut.congr e) ha
    have hfour := UnitaryAutomorphisms.fixedSubgroup_twoRank J hn hJ hcard hfixed _ ha'
    exact (hrank ((fixedSubgroup_twoRank_congr e a).mpr hfour)).elim

/-- The rank-one obstruction with the fixed involution required by the local
argument. The identity automorphism is allowed in the hypotheses; the no-four
condition forces the automorphism to be outer. -/
public theorem bender_rank_one_obstruction
    {B : Type*} [Group B] [Finite B] (hB : IsSimpleBenderGroup B)
    (a : MulAut B) (ha : a ^ 2 = 1)
    (hrank : ¬ TwoRankAtLeastTwo a.fixedSubgroup) :
    Nonempty (B ≃* PSL2BinaryMatrixGroup 2) ∧
      (¬ ∃ b : B, a = MulAut.conj b) ∧
      ∃ x : B, x ∈ a.fixedSubgroup ∧ IsInvolution x := by
  obtain ⟨⟨e⟩, houter, _⟩ := bender_rank_one_fixed_models hB a ha hrank
  have heven : Even (Nat.card B) := by
    rw [Nat.card_congr e.toEquiv]
    exact Linear.psl2_even_card (BinaryGaloisField 2)
  exact ⟨⟨e⟩, houter, exists_fixed_involution_of_even a ha heven⟩

/-- The 2-closed fixed-group consequence of GLS IV, Chapter 4, Lemma 3.4(c)
used in Chapter 2, Proposition 4.4. Normality is inside the actual fixed
subgroup, and the conclusion supplies an element inducing the automorphism. -/
public theorem bender_inner_of_fixedSubgroup_normalSylow
    {B : Type*} [Group B] [Finite B] (hB : IsSimpleBenderGroup B)
    (a : MulAut B) (ha : a ^ 2 = 1)
    (hP : ∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) :
    ∃ b : B, a = MulAut.conj b := by
  rcases hB with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩⟩
  · have ha' : (MulAut.congr e a) ^ 2 = 1 := by
      simpa only [map_pow, map_one] using congrArg (MulAut.congr e) ha
    exact (MulAut.congr_inner_iff e a).mp
      (Linear.inner_of_normal_sylow hn _ ha'
        ((fixedSubgroup_normalSylow_congr e a).mp hP))
  · have ha' : (MulAut.congr e a) ^ 2 = 1 := by
      simpa only [map_pow, map_one] using congrArg (MulAut.congr e) ha
    obtain ⟨b, hb, _⟩ := suzuki_involutoryAut_inner_and_twoRank m hm _ ha'
    exact (MulAut.congr_inner_iff e a).mp ⟨b, hb⟩
  · let : Field E := hEfield
    let : Finite E := hEfinite
    have ha' : (MulAut.congr e a) ^ 2 = 1 := by
      simpa only [map_pow, map_one] using congrArg (MulAut.congr e) ha
    exact (MulAut.congr_inner_iff e a).mp
      (UnitaryAutomorphisms.inner_of_fixedSubgroup_normalSylow J hn hJ hcard hfixed _ ha'
        ((fixedSubgroup_normalSylow_congr e a).mp hP))

end BenderSuzuki.ZD
