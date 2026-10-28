module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairImage
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.SylowOuterRadicalFreeSections
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Inner action of the original pair from a small Sylow Frattini quotient

A nontrivial outer image of the original fixed residual retains its whole
A₅ × A₅ quotient: the actual pair-image kernel is a two-group. Descend the
outer action of the normal quasisimple K faithfully to K/Z(K), and lift
through the Sylow stabilizer. The unconditional simple-group pointwise
Sylow fixer is solvable, so the whole radical-free pair survives restriction
to the Sylow subgroup. Its order contains twenty-five, impossible when the
Sylow Frattini quotient has at most128 elements.

The consumer retains the literal original F and N_G(B), and concludes
F ≤ K C_N(K). Its sole additional model premise is the specified Sylow
Frattini size bound; no full outer-solvability classification is required.
Source: Aschbacher–Smith 4.4.10, printed p.621, in the original nonnormal
A₅ setup of10.2, using the two-Schreier input I.3.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
  {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem a5Pair_radical_eq_bot :
    solvableRadical (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have h := solvableRadical_eq_bot_of_simple_not_solvable
    (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)))
  exact solvableRadical_prod_eq_bot h h

include D in
/-- The original pair has trivial image in the outer group of a simple group
whose Sylow two-subgroup has at most seven Frattini generators. -/
theorem source_a5_oddActorResidual_outer_hom_eq_one_of_smallFrattini
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (P : Sylow 2 S) (hP : Nat.card (P ⧸ frattini P) ≤ 128) :
    let F := ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype)
    let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
    ∀ f : I →* MulAut.Outer S, f.comp (inclusion (show F ≤ I from le_sup_left)) = 1 := by
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))
  change ∀ f : I →* MulAut.Outer S,
    f.comp (inclusion (show F ≤ I from le_sup_left)) = 1
  intro f
  let g := f.comp (inclusion (show F ≤ I from le_sup_left))
  by_contra hg
  have hk : IsPGroup 2 g.ker := source_a5_oddActorResidual_hom_kernel D e hn hp B hB hBC hperm f hg
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  obtain ⟨q,hq,hqker⟩ := source_a5_oddActorResidual_product_quotient D e hn B hBC hodd
  have hker : g.ker ≤ q.ker := by
    rw [hqker]
    exact le_sSup ⟨inferInstance,hk⟩
  let a : g.range →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    g.rangeRestrict.liftOfSurjective g.rangeRestrict_surjective ⟨q,by
      simpa only [MonoidHom.ker_rangeRestrict] using hker⟩
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨g.rangeRestrict y,by simp [a]⟩
  let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  have hdiv := MulAut.radicalFree_outer_section_card_dvd_sylow_aut P
    a5Pair_radical_eq_bot g.range a ha
  have h25 : 25 ∣ Nat.card (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
    rw [Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]
  exact P.isPGroup'.not_twentyfive_dvd_card_mulAut_of_frattini_card_le_128 hP (h25.trans hdiv)

include D in
/-- A small actual Sylow Frattini quotient of K/Z(K) forces the unchanged
fixed residual to act innerly on the normal quasisimple K. -/
theorem source_a5_oddNormalizer_inner_of_smallFrattini
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card (P ⧸ frattini P) ≤ 128) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hIN : I ≤ N := sup_le hFN inf_le_right
  let α : N →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp MulAut.conjNormal
  let j := MulAut.centralQuotientOuter (MulEquiv.refl (K ⧸ center K))
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hz := source_a5_oddActorResidual_outer_hom_eq_one_of_smallFrattini
    D e hn hp B hB hBC hperm P hP ((j.comp α).comp (inclusion hIN))
  have hker : α.ker = K ⊔ centralizer (K : Set N) := by
    rw [show α = (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (MulAut.conjNormal : N →* MulAut K) from rfl,
      ← MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup]
  intro x hx
  rw [← hker]
  change α x = 1
  apply MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K))
  exact (DFunLike.congr_fun hz (⟨x,hx⟩ : F)).trans j.map_one.symm
end CFSG.Quasithin.Chapter10
