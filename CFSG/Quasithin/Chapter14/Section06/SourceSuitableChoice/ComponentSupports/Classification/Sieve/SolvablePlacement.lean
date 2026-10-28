module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Preparation
public import Theory.GroupTheory.NormalSylowQuotientAction.InvariantLift
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# Solvable quotient subgroups in the terminal model sieve

A Sylow-invariant solvable subgroup of a marked K/O₂(K) lifts to a solvable
overgroup of the original T, inside H. Original 14.6.18 places that lift in
M. Mapping back gives containment in the literal image of M ∩ K. The cubic
specialization proves solvability using the coset action of degree three.

These are the Borel and parabolic placement steps of Aschbacher--Smith
14.6.20, printed p.1037. The actual model applications are in `Exceptional`.
The sole earlier-source premise is 14.6.18, owned by qt-e-14625-source;
qt-e-suitable-component-supports retains the remaining model sieve.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
variable {G B : Type*} [Group G] [Finite G] [Group B] [Finite B]

omit [Finite B] in
/-- Original 14.6.18 places a Sylow-invariant solvable subgroup of the actual
component quotient in the image of M. The ambient overgroup need only belong
to H(T); no exclusion of a final classification model is assumed. -/
theorem source_invariant_solvable_le_image
    (T : Sylow 2 G) (M : Subgroup G)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* B)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J : Subgroup B) [Group.IsSolvable J]
    (hinv : ∀ b : MulAut B,
      ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map b.toMonoidHom =
        (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) →
      J.map b.toMonoidHom = J) :
    J ≤ (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Jpre := J.comap q
  let Y := Jpre.map K.subtype ⊔ (T : Subgroup G)
  have hYover : Y ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right
      (sup_le ((map_subtype_le Jpre).trans hKH) hH.2) hH
  have hs : Group.IsSolvable Y :=
    NormalSylowQuotientAction.solvable_lift_sup_of_sylow_invariant T K hn eK P hP J hinv
  have hYM := hsolv Y hYover hs
  have hpre : Jpre ≤ M.subgroupOf K :=
    (map_le_iff_le_comap).mp (le_sup_left.trans hYM)
  have hm := map_mono (f := q) hpre
  rwa [map_comap_eq_self_of_surjective
    (eK.surjective.comp (QuotientGroup.mk'_surjective _))] at hm

/-- In particular the invariant cubic subgroups used for A₇ and M₂₂ lie in
the literal image of M, using their solvability rather than 14.3's exclusions. -/
theorem source_invariant_cubic_le_image
    (T : Sylow 2 G) (M : Subgroup G)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* B)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J : Subgroup B)
    (hi : ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).relIndex J = 3)
    (hinv : ∀ b : MulAut B,
      ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map b.toMonoidHom =
        (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) →
      J.map b.toMonoidHom = J) :
    J ≤ (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  let : Group.IsNilpotent (Pq : Subgroup B) := Pq.isPGroup'.isNilpotent
  let : Group.IsSolvable J := (Pq : Subgroup B).isSolvable_of_relIndex_le_four J (by
    change ((P : Subgroup K).map q).relIndex J ≤ 4
    rw [hi]; decide)
  exact source_invariant_solvable_le_image T M hsolv H hH K hKH hn eK P hP J hinv
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
