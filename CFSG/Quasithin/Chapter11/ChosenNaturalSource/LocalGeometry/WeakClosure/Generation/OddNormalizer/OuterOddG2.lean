module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterOddFour
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.G2Frattini

/-!
# Excluding the last outer component action

The faithful quaternion-summand action bounds the Sylow Frattini quotient
of odd-prime G₂ by 32. Its automorphisms therefore cannot have the original
PSL₃(4) quotient section. Combined with the preceding model exclusions,
this places the original odd-actor residual in the inner automorphisms of
every actual Theorem B component of N(A).

Source: Aschbacher–Smith, 4.4.10–11, printed pp.621–623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

/-- Transport the actual octonion bound over every prime field realization. -/
theorem odd_g2_frattini_le_thirtytwo
    {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassificationModels.IsG2At Q p) (P : Sylow 2 Q) :
    Nat.card (P ⧸ frattini P) ≤ 32 := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := by
    have := hp.two_le
    have hn : p ≠ 2 := by intro he; subst p; norm_num at ho
    omega
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let a : ZMod p ≃+* F := ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let b : Q ≃* Atlas.G2.Model (ZMod p) := e.trans (Atlas.G2.fieldEquiv a.symm)
  let R := P.mapSurjective (f := b.toMonoidHom) b.surjective
  rw [SylowFrattiniBounds.card_congr (P.equivMapOfInjective b.toMonoidHom b.injective)]
  exact G2Frattini.prime_frattini_card_le hp2 R

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- Odd-prime G₂ cannot carry the original PSL₃(4) outer section.
The component's full central cover is retained. -/
theorem moved_outer_not_odd_g2 {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hm : ClassificationModels.IsG2At (K ⧸ center K) p) : False := by
  let P : Sylow 2 (K ⧸ center K) := default
  exact moved_outer_not_of_frattini_le_thirtytwo D S K hK ho
    (.odd (.g2 p hp hodd hm)) P (odd_g2_frattini_le_thirtytwo hp hodd hm P)

/-- The full Theorem B catalogue excludes every actual outer section.
This proves only the source's needed section exclusion and keeps the
original central quotient and full component cover. -/
theorem no_moved_outer_section {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    ¬ ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f := by
  intro ho
  obtain ⟨p,hp,hodd,hg⟩ := moved_outer_g2_model D S K hK hm ho
  exact moved_outer_not_odd_g2 D S K hK ho hp hodd hg

open Chapter4 Chapter4.Section04
/-- Every actual component is acted on by the original residual through
inner automorphisms. No ambient two-core or C.2.8 hypothesis is used. -/
theorem moved_component_inner_action {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) := by
  exact (moved_component_inner_or_outer_section D S hA hodd K hK).resolve_right
    (no_moved_outer_section D S K hK hm)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
