module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Requirements

/-!
# Restricting a marked span quotient to an actual core factor

A marked quotient of the full orbit span has kernel Z_alpha. To restrict it
to a subgroup of the core, two separate statements are needed: the subgroup
must generate the span together with Z_alpha and meet Z_alpha in U_alpha.
The first gives surjectivity of the restriction, and the second gives its
exact relative kernel. Ambient equivariance restricts to the actual core
conjugation action with the original marking unchanged.

`SpanQuotient` and `CoreLift` keep those separate mathematical obligations
explicit. Neither is constructed from the source hypotheses in this module;
in particular a quotient by Z_alpha does not by itself give a factor by U_alpha.
This is the quotient conversion needed after MS93 (1993), (4.6.12)(5),
printed pp.911--912. It does not assume or assert a core-center equality.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne

private theorem restriction_surjective {G H : Type*} [Group G] [Group H]
    (S Z A : Subgroup G) (hZ : Z ≤ S) (hA : A ≤ S) (hgen : S = Z ⊔ A)
    (q : S →* H) (hq : Function.Surjective q) (hk : q.ker = Z.subgroupOf S) :
    Function.Surjective (q.comp (inclusion hA)) := by
  let f := q.comp (inclusion hA)
  let K := f.range.comap q
  have hZK : Z ≤ K.map S.subtype := by
    intro z hz
    refine ⟨⟨z, hZ hz⟩, ?_, rfl⟩
    have hqz : q ⟨z, hZ hz⟩ = 1 := by
      change (⟨z, hZ hz⟩ : S) ∈ q.ker
      rw [hk]
      exact hz
    change q ⟨z, hZ hz⟩ ∈ f.range
    rw [hqz]
    exact f.range.one_mem
  have hAK : A ≤ K.map S.subtype := by
    intro a ha
    refine ⟨⟨a, hA ha⟩, ?_, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hSK : S ≤ K.map S.subtype := hgen.trans_le (sup_le hZK hAK)
  intro y
  obtain ⟨x, rfl⟩ := hq y
  obtain ⟨x', hx', he⟩ := hSK x.property
  have he' : x' = x := Subtype.ext he
  subst x'
  exact hx'

variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- The actual full-span quotient by Z_alpha, dual to the given natural marking. -/
structure SpanQuotient (c : Vertex R) where
  quotient : orbitSpan c →* Multiplicative Linear.W
  onto : Function.Surjective quotient
  kernel : quotient.ker = (Z R (alpha R)).subgroupOf (orbitSpan c)
  action : ∀ (m : M) (x y : orbitSpan c),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (quotient y).toAdd =
      Linear.dual (common.natural.marking (source.projection m)) (quotient x).toAdd

/-- An invariant core subgroup generating the span modulo Z, with intersection exactly U.
It may be smaller than the full intersection of the span with the core. -/
structure CoreLift (c : Vertex R) where
  factor : Subgroup (core R (alpha R))
  normalized : ∀ m (x : core R (alpha R)), x ∈ factor → coreAction (R := R) m x ∈ factor
  intersect : factor.map (core R (alpha R)).subtype ⊓ Z R (alpha R) = U R (alpha R)
  decomposition : orbitSpan c = Z R (alpha R) ⊔ factor.map (core R (alpha R)).subtype

variable {source common}

namespace SpanQuotient
variable {c : Vertex R} (q : SpanQuotient source common c)

include q in
/-- The exact kernel and onto map identify the full-span quotient order as eight. -/
theorem quotient_index : (Z R (alpha R)).relIndex (orbitSpan c) = 8 := by
  change ((Z R (alpha R)).subgroupOf (orbitSpan c)).index = 8
  rw [← q.kernel]
  change Nat.card (orbitSpan c ⧸ q.quotient.ker) = 8
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q.quotient q.onto).toEquiv,
    Nat.card_eq_fintype_card]
  decide

end SpanQuotient

namespace CoreLift
variable {c : Vertex R} (d : CoreLift c)

/-- The decomposition places the selected core subgroup inside the actual orbit span. -/
theorem factor_le : d.factor ≤ coreOrbit c := by
  intro x hx
  change (x : FreeAmalgam R) ∈ orbitSpan c
  rw [d.decomposition]
  exact mem_sup_right ⟨x, hx, rfl⟩

/-- The intersection identity includes the entire U-layer in the selected factor. -/
theorem contains : (U R (alpha R)).subgroupOf (core R (alpha R)) ≤ d.factor := by
  intro x hx
  have h : (x : FreeAmalgam R) ∈ d.factor.map (core R (alpha R)).subtype ⊓ Z R (alpha R) :=
    d.intersect.symm ▸ hx
  obtain ⟨y, hy, he⟩ := h.1
  exact (Subtype.ext he : y = x) ▸ hy

/-- The literal composite subgroup inclusion from the selected core factor to its span. -/
noncomputable def toSpan : d.factor →* orbitSpan c :=
  ((core R (alpha R)).subtype.comp d.factor.subtype).codRestrict _
    (fun x => d.factor_le x.property)

/-- Generation modulo Z makes the restricted quotient surjective. -/
theorem restrict_onto (q : SpanQuotient source common c) :
    Function.Surjective (q.quotient.comp d.toSpan) := by
  let A := d.factor.map (core R (alpha R)).subtype
  have hA : A ≤ orbitSpan c := by
    rw [d.decomposition]
    exact le_sup_right
  have hZ : Z R (alpha R) ≤ orbitSpan c := by rw [d.decomposition]; exact le_sup_left
  have hs := restriction_surjective (orbitSpan c) (Z R (alpha R)) A hZ hA
    d.decomposition q.quotient q.onto q.kernel
  intro w
  obtain ⟨a, ha⟩ := hs w
  obtain ⟨x, hx, he⟩ := a.property
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (congrArg q.quotient (Subtype.ext he)).trans ha

/-- Intersecting the original kernel with the factor gives exactly the relative U-layer. -/
theorem restrict_kernel (q : SpanQuotient source common c) :
    (q.quotient.comp d.toSpan).ker =
      ((U R (alpha R)).subgroupOf (core R (alpha R))).subgroupOf d.factor := by
  ext x
  change q.quotient (d.toSpan x) = 1 ↔ ((x : core R (alpha R)) : FreeAmalgam R) ∈ U R (alpha R)
  change d.toSpan x ∈ q.quotient.ker ↔ _
  rw [q.kernel]
  change ((x : core R (alpha R)) : FreeAmalgam R) ∈ Z R (alpha R) ↔ _
  constructor
  · intro hx
    rw [← d.intersect]
    exact ⟨⟨x, x.property, rfl⟩, hx⟩
  · intro hx
    have h := d.intersect.symm ▸ hx
    exact h.2

/-- Restrict the marked quotient, proving all fields of the actual dual factor. -/
noncomputable def dualFactor (q : SpanQuotient source common c) : DualFactor source common d.factor where
  contains := d.contains
  normalized := d.normalized
  quotient := q.quotient.comp d.toSpan
  onto := d.restrict_onto q
  kernel := d.restrict_kernel q
  action m x y hy := q.action m (d.toSpan x) (d.toSpan y)
    (congrArg (fun z : core R (alpha R) => (z : FreeAmalgam R)) hy)

end CoreLift
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
