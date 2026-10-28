module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.ActorBounds
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
/-!
# Odd linear-three bounds for a possibly reducible orbit module

For a finite group with trivial two-core and quasisimple generalized Fitting
subgroup of projective type PSL₃(p), p odd, elementary two-subgroups embed in
the automorphism group of that component. The native automorphism rank bound
and three-conjugate generation then bound the degree of any fixed-free binary
module of cubic ratio at most two by eighteen. Irreducibility of the orbit
module is not required.

The original chosen irreducible seed supplies the independent lower-degree
bound in the Section 13.1 consumer. This preserves the source distinction
between the seed and its full T-orbit.
Source: Aschbacher--Smith, 3.2.5, p.580, and 13.1.4, p.867, using the
odd linear-three estimates of Chapter K.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeConjugateBounds
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
variable {G : Type*} [Group G] [Finite G]

private theorem primeRank_two_le_aut_of_twoCore_eq_bot (hcore : pCore 2 G = ⊥) :
    primeRank 2 G ≤ primeRank 2 (MulAut (generalizedFitting G)) := by
  let L := generalizedFitting G
  have hz : center G ≤ L := by
    intro z hz
    apply centralizer_generalizedFitting_le G
    intro l _
    exact mem_center_iff.mp hz l
  have hf : generalizedFitting G = L ⊔ center G := (sup_eq_left.mpr hz).symm
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  let f := (MulAut.conjNormal : G →* MulAut L).comp E.subtype
  have hi : Function.Injective f :=
    QuasisimpleSource.IrreducibleBranch.twoSubgroup_conjugation_injective L E hf hcore
      (hE.isPGroup 2 E)
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).le.trans
    ((primeRank_le_iff_elementary_card_le (MulAut L)).mp le_rfl f.range he)

theorem two_free_two_rank_pslThree (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p) :
    primeRank 2 G ≤ 3 := by
  let := hq
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) := hq.simple
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hAut := automorphism_primeRank_le_quotient_center (E := generalizedFitting G) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hAut
  exact ((primeRank_two_le_aut_of_twoCore_eq_bot hcore).trans hAut).trans
    (Matrix.PSL3.OddPrimeActorRank.automorphism_two_rank
      (Group.IsPerfect.not_isSolvable _) hp ho hF)

theorem two_free_three_conjugates_pslThree (hcore : pCore 2 G = ⊥)
    (hq : IsQuasisimple (generalizedFitting G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p)
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g : Fin 3 → G, generalizedFitting G ≤
      closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let L := generalizedFitting G
  let := hq
  let : IsSimpleGroup (L ⧸ center L) := hq.simple
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let f := MulAut.centralQuotientConjugation L e
  have hft : f t ≠ 1 := by
    intro he
    apply ht
    have hc : t ∈ centralizer (L : Set G) := by
      rw [← MulAut.centralQuotientConjugation_ker L e]
      exact he
    exact Subgroup.disjoint_def.mp
      (QuasisimpleSections.disjoint_centralizer_fitting hcore (zpowers t)
        ((IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) ht2).isPGroup 2 _))
      (mem_zpowers t) hc
  obtain ⟨s, hs⟩ := three_bound_of_inner_graph inner_three_bound graph_three_bound
    (Group.IsPerfect.not_isSolvable _) hp ho hF (f t) hft
      (by rw [← map_pow, ht2, map_one])
  exact MulAut.lift_conjugate_generation L e
    (centralizer_generalizedFitting_le G) t s hs

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem two_free_degree_le_eighteen_pslThree (ρ : Representation (ZMod 2) G W)
    (hcore : pCore 2 G = ⊥) (hq : IsQuasisimple (generalizedFitting G))
    (hc : fixedSpace ρ (generalizedFitting G) = ⊥)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 p)
    (hratio : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) W ≤ 18 := by
  exact finrank_le_of_cubicRatio_and_conjugates ρ (generalizedFitting G) hc
    (two_free_two_rank_pslThree hcore hq hp ho hm)
    (two_free_three_conjugates_pslThree hcore hq hp ho hm) hratio
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
