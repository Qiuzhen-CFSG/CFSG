module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.LinearSylow
public import Theory.SpecificGroups.SL3.QuinticBorel

/-!
# Completing the component comparisons in original 14.6.15

The last surviving row is SL₃ over a binary field of degree two modulo
four. Its actual radical intersection is Sylow. The literal order-five
first-factor action therefore preserves a five-free Borel and cannot be
inner. Its outer image has order five, forcing the actor group's inner
intersection to be a two-group. Borel rigidity then excludes the actor.

Together with the earlier full B.5.1 row reductions this excludes every
second-normalizer geometry. The extraction uses SourceEscapingComponent
and retains all six B.5.1 clauses; it does not use the disputed ordinary
centralizer identity. Constructing the exchanged module geometry and
discharging the original index obligation remain with the final owner,
qt-e-14615-quintic-exclusion. Earlier 14.6.12--14 inputs retain their discharge
with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The final linear-three component row contradicts its literal Borel
normalizer and first-factor action. -/
theorem source_no_linear_star (F : BinaryField)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* SL(3,F.Carrier)) : False := by
  have hd := source_component_linear_degree s d j F e
  have hm := source_component_linear_degree_mod_four s d j F e
  have hl : 1 < F.degree := by omega
  let R := Mc.pCoreIn 2
  let C := starImage j.J R j.J
  let Q := (starImage j.J R R).subgroupOf C
  let f := (starComponentAction j.J R).comp
    (inclusion (source_first_le_common_normalizer s d j))
  have hi := source_component_input s d j
  obtain ⟨S,hS⟩ := source_component_linear_radical_sylow s d j F e
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    have h4 : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hl
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left h4 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left h4 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4^3*(4^3-1)*(4^2-1)) hh
  obtain ⟨_,hN⟩ := star_intersection_placement_from_source_of_large_order hi hlarge
  have hNf : (normalizer (S : Set C)).map MulAut.conj ≤ normalizer (f.range : Set _) := by
    have he : f.range = (d.K1.subgroupOf
        (normalizer (j.J : Set G) ⊓ normalizer (R : Set G))).map
          (starComponentAction j.J R) := by rw [MonoidHom.range_comp,inclusion_range]
    change (normalizer ((S : Subgroup C) : Set C)).map MulAut.conj ≤ _
    rw [hS,he]
    exact (map_mono hN).trans (source_borel_normalizes_first_actor s d j hi.normalizes)
  obtain ⟨k,hk,_,ha⟩ := source_component_star_quintic s d j hi.normalizes
  have hfix : (S : Subgroup C).map (starComponentAction j.J R k).toMonoidHom = S := by
    rw [hS]
    exact source_component_radical_intersection_fixed s d j k
  have hout := Matrix.SL3.QuinticBorel.sylow_quintic_not_inner F.Carrier F.degree_pos F.card_eq
    hd e S _ ha hfix
  have horder := MulAut.outer_order_eq_prime_of_prime_order_not_inner _ ha hout
  let y : d.K1 := ⟨k,hk⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup C)
  let o := q.comp f
  have h5 : 5 ∣ Nat.card o.range := by
    have hh := orderOf_dvd_natCard (o.rangeRestrict y)
    rw [Subgroup.orderOf_mk] at hh
    exact horder ▸ hh
  obtain ⟨_,_,⟨em⟩,_⟩ := source_normalizer_geometry_residual_models s d
  have hc : Nat.card (d.K1 ⧸ pCore 2 d.K1) = 5 := by
    rw [Nat.card_congr em.toEquiv]
    simp
  have ht : IsPGroup 2 (f.range ⊓ MulAut.innerSubgroup C : Subgroup _) :=
    MulAut.inner_intersection_isPGroup_of_outer_range f (by decide) hc h5
  exact Matrix.SL3.QuinticBorel.no_sylow_actor_of_equiv F.Carrier hl F.card_eq hd e S
    f.range ht hNf _ ⟨y,rfl⟩ ha hfix

include s d in
/-- Every actual normalizer geometry is excluded. This completes the terminal
component comparison, without the disputed ordinary-centralizer identity. -/
theorem source_normalizer_geometry_false : False := by
  let j := Classical.choice (exists_source_escaping_component s d)
  obtain ⟨hCJ,_,F,_,⟨e⟩⟩ := source_component_linear_moved_rows s d j
  exact source_no_linear_star s d j F ((subgroupOfEquivOfLe hCJ).symm.trans e)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
