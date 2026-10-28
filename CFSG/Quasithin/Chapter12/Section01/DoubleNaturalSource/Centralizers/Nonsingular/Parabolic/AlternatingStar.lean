module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingStarSixExclusion
public import Theory.SpecificGroups.Alternating.EightSectionExtension
public import Theory.GroupAction.OddTransitiveTwoCore
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeDegree

/-!
# Alternating star-component exclusions at a nonsingular point

The original radical has a nontrivial image in the C.2.7 star extension.
The perfect point residual normalizes that image and retains its simple
two-core quotient through the solvable star kernel. For A7 the faithful
seven-letter action forces every two-local normalizer to be seven-free.
For A8 a factor five forces the radical image to be a transposition;
its centralizer is seven-free. These exclude A7 in both doubled-natural
degrees and A8 in degree five, without an ambient Sylow assertion.

`AlternatingStarSource` applies the exclusions to the literal residual,
radical and centralizer/closure consumer. The possible odd central star
kernel is retained. Source: Aschbacher--Smith 12.1.1, pp.788--789, and
C.2.7, pp.145--147. Imported prime-degree and alternating-group results
retain their original attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
open ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

private theorem seven_not_dvd_two_normalizer
    (Q : Subgroup (Equiv.Perm (Fin 7))) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ¬ 7 ∣ Nat.card (normalizer (Q : Set (Equiv.Perm (Fin 7)))) := by
  intro hd
  let N := normalizer (Q : Set (Equiv.Perm (Fin 7)))
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 N := Classical.choice inferInstance
  have hp : Nat.card P = 7 := P.card_eq_prime_of_dvd_of_not_sq_dvd hd (by
    intro hh
    have hh := hh.trans N.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh)
  let : MulAction.IsPretransitive P (Fin 7) :=
    Atlas.GroupTheory.prime_subgroup_pretransitive (G := N) 7 (by simp) P hp
  have hc : pCore 2 N = ⊥ := N.subtype.twoCore_eq_bot_of_transitive_odd
    N.subtype_injective (by simp) (by
      intro x y
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P x y
      exact ⟨g.val,hg⟩)
  have hle : Q.subgroupOf N ≤ pCore 2 N := le_sSup ⟨inferInstance,hQ.comap_subtype⟩
  have hb : Q.subgroupOf N = ⊥ := bot_unique (hc ▸ hle)
  have hh := congrArg (map N.subtype) hb
  rw [map_subgroupOf_eq_of_le Q.le_normalizer,Subgroup.map_bot] at hh
  exact hne hh

private theorem eight_no_two_normalizer_five_seven
    (Q N : Subgroup (Equiv.Perm (Fin 8))) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hN : N ≤ alternatingGroup (Fin 8)) (hn : N ≤ normalizer (Q : Set _))
    (h5 : 5 ∣ Nat.card N) (h7 : 7 ∣ Nat.card N) : False := by
  obtain ⟨t,ht,_,hC⟩ :=
    Theory.SpecificGroups.Alternating.EightSectionExtension.normalized_two_is_transposition
      Q N hQ hne hN hn h5
  have hd := h7.trans (card_dvd_of_le (hn.trans hC))
  rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp ht] at hd
  norm_num [Nat.factorial] at hd

private theorem section_card_dvd {B A : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    [IsSimpleGroup (B ⧸ pCore 2 B)] [Group A] [Finite A]
    (f : B →* A) [Group.IsSolvable f.ker] : Nat.card (B ⧸ pCore 2 B) ∣ Nat.card f.range := by
  have hk := PerfectCoreTwoExtension.solvable_ker_le_core f
  let q : (B ⧸ f.ker) →* (B ⧸ pCore 2 B) :=
    QuotientGroup.lift f.ker (QuotientGroup.mk' (pCore 2 B)) (by
      simpa only [QuotientGroup.ker_mk'] using hk)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
    exact ⟨QuotientGroup.mk' f.ker b,rfl⟩
  have hd := card_dvd_of_surjective q hq
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd

/-- A seven-divisible simple residual section excludes A7 as a star component.
A factor five in the same section also excludes A8. The radical is the original C.2.7 radical. -/
theorem no_alternating_star_of_section
    {G : Type*} [Group G] [Finite G] {H K R M A : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hA : A ≤ M ⊓ K) [Group.IsPerfect A] [IsSimpleGroup (A ⧸ pCore 2 A)]
    (hAR : A ≤ normalizer (R : Set G))
    (hseven : 7 ∣ Nat.card (A ⧸ pCore 2 A))
    {d : ℕ} (hd : d = 7 ∨ d = 8)
    (hfive : d = 8 → 5 ∣ Nat.card (A ⧸ pCore 2 A))
    (e : starImage K R K ≃* alternatingGroup (Fin d)) : False := by
  obtain ⟨f,hf,hfe⟩ := alternating_star_embedding h (by omega) (by omega) e
  let C := starImage K R K
  let Q := (starImage K R R).map f
  let a := (toStarImage K R).comp (inclusion (hA.trans inf_le_right))
  let g := f.comp (C.subtype.comp a)
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hQ : IsPGroup 2 Q := (hR.comap_subtype.map (QuotientGroup.mk' (starKernel K R))).map f
  have hQne : Q ≠ ⊥ := by
    intro hh
    let : (K.subgroupOf (K ⊔ R)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
    exact star_radical_ne_bot (source_join_input h)
      (((starImage K R R).map_eq_bot_iff_of_injective hf).mp hh)
  have hn : g.range ≤ normalizer (Q : Set _) := by
    rintro _ ⟨x,rfl⟩
    apply (starImage K R R).le_normalizer_map f
    apply mem_map_of_mem f
    apply (R.subgroupOf (K ⊔ R)).le_normalizer_map (QuotientGroup.mk' (starKernel K R))
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq (show R ≤ K ⊔ R from le_sup_right)]
    exact hAR x.property
  let : Group.IsSolvable g.ker := by
    dsimp only [g]
    rw [MonoidHom.ker_comp_of_injective _ _ hf,
      MonoidHom.ker_comp_of_injective _ _ C.subtype_injective]
    exact six_star_map_ker_solvable h _
  have h7 : 7 ∣ Nat.card g.range := hseven.trans (section_card_dvd g)
  rcases hd with rfl | rfl
  · exact seven_not_dvd_two_normalizer Q hQ hQne (h7.trans (card_dvd_of_le hn))
  · apply eight_no_two_normalizer_five_seven Q g.range hQ hQne _ hn
      ((hfive rfl).trans (section_card_dvd g)) h7
    rintro _ ⟨x,rfl⟩
    change f (a x) ∈ _
    rw [hfe]
    exact (e (a x)).property
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
