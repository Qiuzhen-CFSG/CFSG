module
public import CFSG.Quasithin.Chapter14.Section06.SourceClassifiedFactors
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.PrimitiveTransitivity
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorCount

/-!
# Transitivity of the original solvable plane factors

The original outside-minimal subgroup has an elementary minimal normal
odd residual. Triviality of the quotient two-core makes that residual
self-centralizing. Each orbit product of the classified ratio factors
therefore contains the residual, and independence leaves only one orbit.
The final consumer constructs this transitive factor action from the actual
odd-core counterexample, retaining the original quotient and module.

This establishes the primitive permutation step in 14.6.12(2). It does not
infer two factors from primitivity alone: the single elementary-nine
indecomposable requires its separate original source exclusion.

Source: Aschbacher--Smith 14.6.11--12, printed pp.1030--1031.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab

/-- The actual primitive residual forces transitivity of the literal
factor permutation, without a new recognition or action premise. -/
theorem source_ratio_factor_transitive
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor) :
    ∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j := by
  obtain ⟨p,hprime,hE,_,_,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  exact f.transitive_of_minimal_normal_selfCentralizing d
    (pResidual 2 (J ⧸ pCore 2 J)) hmin
    (centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)) π hp

/-- There are at most two original factors; in the nonsingleton case,
their intersections with the actual odd residual are cyclic. -/
theorem source_ratio_factor_count
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor) :
    Nat.card d.Index ≤ 2 ∧
      (1 < Nat.card d.Index → ∀ i,
        IsCyclic ((f.ambientFactor d i).actor ⊓ pResidual 2 (J ⧸ pCore 2 J) : Subgroup _)) := by
  classical
  let P := pResidual 2 (J ⧸ pCore 2 J)
  let K := ChapterD.Jhat a.representation
  let R : d.Index → Subgroup (J ⧸ pCore 2 J) := fun i => (f.ambientFactor d i).actor ⊓ P
  obtain ⟨p,hprime,hE,hrank,_,_⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let : Fact p.Prime := ⟨by rcases hprime with rfl | rfl <;> decide⟩
  let : IsElementaryAbelian p P := hE
  have hodd : Odd p := by rcases hprime with rfl | rfl <;> decide
  have hPK : P ≤ K := source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hself : centralizer (P : Set (J ⧸ pCore 2 J)) ≤ P :=
    centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)
  have hR : ∀ i, IsPGroup p (R i) := fun i => (IsElementaryAbelian.isPGroup p P).to_le inf_le_right
  have hne : ∀ i, R i ≠ ⊥ := fun i =>
    f.actor_inf_ne_bot_of_selfCentralizing d P hPK hself i
  let i : d.Index := Classical.choice inferInstance
  have hq : cubicRatio (d.factor i).action ≤ 2 := by
    rw [(d.factor i).embedding.ratio,f.ratio]
    exact (cubicRatio_le_quadraticRatio _).trans
      (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff (d.factor i).action).mpr hq
  obtain ⟨x,hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.2.1.1
  have hx : (x : (d.factor i).Carrier) ∈ A := x.property
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hx2 : orderOf (x : (d.factor i).Carrier) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (x : (d.factor i).Carrier) hx)
    (fun he => hxne (Subtype.ext he))
  let t := (f.ambientFactor d i).embedding.groupMap (x : (d.factor i).Carrier)
  have ht2 : orderOf t = 2 :=
    (orderOf_injective _ (f.ambientFactor d i).embedding.group_injective (x : (d.factor i).Carrier)).trans hx2
  have hm : t ∉ centralizer (P : Set (J ⧸ pCore 2 J)) := by
    intro ht
    have hd : 2 ∣ p := ht2 ▸ orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian t (hself ht))
    rcases hprime with rfl | rfl <;> norm_num at hd
  have ht : ∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j :=
    source_ratio_factor_transitive hG T hempty hM hu hmany hcard e hab J hJ hs a f d π hp
  have hconj : ∀ i j, ∃ g : J ⧸ pCore 2 J, (R i).map (MulAut.conj g).toMonoidHom = R j := by
    intro i j
    obtain ⟨g,hg⟩ := ht i j
    refine ⟨g,?_⟩
    change ((f.ambientFactor d i).actor ⊓ P).map _ = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,hp,hg]
    have he : P.map (MulAut.conj g).toMonoidHom = P := Subgroup.Normal.map_conj_eq P g
    rw [he]
  refine ⟨(f.factor_family_bound d hodd (MonoidHom.id _) Function.surjective_id hrank
    P (IsElementaryAbelian.isPGroup p P) id Function.injective_id R (fun _ => inf_le_left)
    hR hne i t ⟨(x : (d.factor i).Carrier),rfl⟩ ht2 hm).1,?_⟩
  intro hmore
  exact (f.factor_orbit_bound d hodd (MonoidHom.id _) Function.surjective_id hrank
    P (IsElementaryAbelian.isPGroup p P) id Function.injective_id R (fun _ => inf_le_left)
    hR hne hconj i t ⟨(x : (d.factor i).Carrier),rfl⟩ ht2 hm hmore).2

/-- An original odd-core counterexample supplies its decomposition and a
transitive permutation of its actual embedded actors and support spaces. -/
theorem source_oddCore_counterexample_transitive_factors
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G) (_hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      J ≤ H ∧ Group.IsSolvable J ∧
      ∃ _hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J),
      ∃ a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T),
      ∃ f : ChapterD.RatioDecomposition.FactorData a.representation
          (ChapterD.Jhat a.representation)
          (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))),
      ∃ d : ChapterD.RatioDecomposition.Decomposition f.representation,
        d.FittingFull ∧ ∃ π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index,
          (⋃ i, f.ambientBlock d i) = ChapterD.QhatStar a.representation ∧
          pResidual 2 (J ⧸ pCore 2 J) ≤ π.ker ∧
          (∀ g i,
            Subgroup.map (MulAut.conj g).toMonoidHom '' f.ambientBlock d i =
              f.ambientBlock d (π g i) ∧
            (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
              (f.ambientFactor d (π g i)).actor ∧
            (f.ambientFactor d i).space.map (a.representation g) =
              (f.ambientFactor d (π g i)).space) ∧
          (∀ i j, ∃ g : J ⧸ pCore 2 J, π g i = j) ∧
          Nat.card d.Index ≤ 2 ∧
          (1 < Nat.card d.Index → ∀ i,
            IsCyclic ((f.ambientFactor d i).actor ⊓ pResidual 2 (J ⧸ pCore 2 J) : Subgroup _)) := by
  obtain ⟨J,hJ,hJH,hs,hU,a,f,d,hd,π,hblocks,hker,hperm⟩ :=
    source_oddCore_counterexample_classified_factors
      hG T hempty hM hu hmany hcard e hab H hH hne
  let := hU
  exact ⟨J,hJ,hJH,hs,hU,a,f,d,hd,π,hblocks,hker,hperm,
    source_ratio_factor_transitive hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π (fun g i => (hperm g i).2.1),
    source_ratio_factor_count hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π (fun g i => (hperm g i).2.1)⟩

end CFSG.Quasithin.Chapter14.Section06
