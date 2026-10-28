module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.PointCentralizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Intersections
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.FullCentralizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Generation
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.CoreIntersections

/-!
# AS91 involution centralizers, fusion and ambient generation

The original marked Todd embedding selects a second involution. Its orbit
and the original marker orbit partition E minus its identity, and Thompson
fusion control separates them in G. The restriction of the same Todd map
identifies C_M(t)/E with Aut(M₂₂). Conditional on the exact earlier (6.2)(3),
intersections E ∩ Eᵍ for g in C_G(t) outside M consist of second-orbit
elements and have order at most four.

Both standard fixed-coset arguments now hold on the original normalizers
and centralizers. The first confines every pure pair-plane normalizer to M;
the second proves C_G(t)≤M. Thus E is the unique conjugate radical containing
t. The actual quotients E/U and E/<t>, together with their cardinality
obstructions to transitivity, discharge both final normalizer steps.
The exact earlier intersection premise is supplied by the incidence producer
on the same LocalData. Four explicit Todd lifts cover involutions outside E
and fuse into the original plane core Q with conjugators in M. A pair
displacement and the original returning marker identify the two noncentral
H-classes in Q. Thus every involution in C_G(z) joined with M is conjugate
to z or t inside that join. Their full ambient centralizers lie in the join,
so every ambient involution transporter also lies there. Strong embedding
would contradict the two distinct classes; hence the join is G. This proves
exactly the unchanged SourceCycleBase.Input.generate clause without assuming
the join simple. The existence of LocalData and unconditional recognition
remain with their earlier-source assembly owners.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.2)–(6.5), pp.601–602.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- The established centralizer and fusion calculations, retaining the same
Todd representative, ambient conjugators, quotient and radical intersections. -/
theorem todd_fusion_consequences (a : LocalData h) (hi : MarkerIntersection a) :
    second a ∈ a.P.E ∧ orderOf (second a) = 2 ∧ ¬ IsConj z (second a) ∧
    (∀ u ∈ a.P.E, u ≠ 1 →
      (∃ m ∈ a.P.M, MulAut.conj m z = u) ∨
      ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) ∧
    Nonempty ((secondCentralizer a ⧸ a.P.E.subgroupOf (secondCentralizer a)) ≃*
      MulAut M22) ∧
    primeRank 2 (secondCentralizer a ⧸ a.P.E.subgroupOf (secondCentralizer a)) ≤ 5 ∧
    (∀ g : G, g ∈ centralizer (second a) → g ∉ a.P.M →
      Nat.card (a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 4 ∧
      ∀ u ∈ a.P.E ⊓ a.P.E.map (MulAut.conj g).toMonoidHom, u ≠ 1 →
        ∃ m ∈ a.P.M, MulAut.conj m (second a) = u) :=
  ⟨second_mem a,second_order a,not_isConj_second a,E_orbits a,
    secondCentralizer_quotient a,secondCentralizer_quotient_rank_le a,
    fun g hgc hgm => ⟨centralizer_intersection_card_le_four a hi g hgc hgm,
      centralizer_intersection_second a hi g hgc hgm⟩⟩


/-- The full centralizer and unique-radical clauses of AS91 (6.3)(3), on the
same earlier data and with exactly the earlier intersection premise. -/
theorem second_centralizer_consequences (a : LocalData h) (hi : MarkerIntersection a) :
    centralizer (second a) ≤ a.P.M ∧
    centralizer (second a) = secondCentralizer a ∧
    (∀ g : G, second a ∈ a.P.E.map (MulAut.conj g).toMonoidHom →
      a.P.E.map (MulAut.conj g).toMonoidHom = a.P.E) :=
  ⟨second_centralizer_le a hi,second_centralizer_eq a hi,second_radical_unique a hi⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
