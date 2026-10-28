module

public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.Classification.Endpoints
public import Theory.AlgebraicGroup.BNPair.StandardParabolic

/-! The following interface describes geometry to be constructed. No standard
parabolic comparison, classification, or rigidity is stored as a field. -/
@[expose] public noncomputable section

namespace Theory.AlgebraicGroup.InvariantLeviGeometry.Classification

open BorelIntersectionGeometry.RankOneGeometry
universe u
variable {k : Type u} [Field k]
  {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)

/-- The actual simple roots are the fundamental roots of the supplied positive
system when its positivity agrees with the realized height function. -/
public theorem simple_eq_fundamental (hpositive : S.positiveRoots = S.D.positive) :
    S.D.simple = FundamentalRootsFor S.D S.positiveRoots := by
  rw [hpositive]
  ext a
  have hs := S.standardParabolic.1.2.1
  rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, hs, _⟩
  rw [hs]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun b hb c hc hbc => h b c hbc ⟨hb, hc⟩⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun b c hbc ⟨hb, hc⟩ => h b hb c hc hbc⟩

/-- The simple-root label used by the calibrated SL₂ markings. -/
def fundamentalIndex
    (hpositive : S.positiveRoots = S.D.positive) (i : S.D.simple) :
    {a // a ∈ FundamentalRootsFor S.D S.positiveRoots} :=
  ⟨i.val, simple_eq_fundamental S hpositive ▸ i.property⟩

/-- The same label in the supplied integral root pairing, without changing
its root datum. -/
def baseIndex (i : S.D.simple) : S.integralBase.support :=
  ⟨S.rootEquiv i.val, (S.actualRootDatum.1.2.2.2 i.val).mp i.property⟩

/-- Required bridge from actual rank-one geometry to a Tits system. The Borel,
normalizer, simple matrix representatives, and integral Weyl group all retain
the supplied datum. Existence is a separate theorem to be proved. -/
public structure AlignedTitsSystem
    (hpositive : S.positiveRoots = S.D.positive)
    (M : SimpleRootMarkings S.D S.positiveRoots) where
  system : TitsSystem (X := Variety.Point K)
  borel_eq : system.B = S.B.toSubgroup
  normalizer_eq : system.N = S.T.normalizer.toSubgroup
  intersection_eq : system.B ⊓ system.N = S.T.toSubgroup
  simple : S.D.simple ≃ system.S
  simple_lift : ∀ i : S.D.simple, ∃ n : system.N,
    n.val = (M.marking (fundamentalIndex S hpositive i)).hom
      BruhatGeneration.SL2.reflection ∧
    QuotientGroup.mk' ((system.B ⊓ system.N).subgroupOf system.N) n =
      (simple i).val
  weylEquiv : (system.N ⧸ (system.B ⊓ system.N).subgroupOf system.N) ≃*
    S.integralPairing.weylGroup
  weyl_simple : ∀ i : S.D.simple,
    weylEquiv (simple i).val = S.integralBase.simpleReflection (baseIndex S i)

namespace AlignedTitsSystem

variable {S} {hpositive : S.positiveRoots = S.D.positive}
  {M : SimpleRootMarkings S.D S.positiveRoots}
  (A : AlignedTitsSystem S hpositive M)

/-- Quotient simple generators attached to the actual subset `J`. -/
def simpleIndices (J : Set S.D.Root) :
    Set (A.system.N ⧸ (A.system.B ⊓ A.system.N).subgroupOf A.system.N) :=
  (fun i : S.D.simple => (A.simple i).val) '' {i | i.val ∈ J}

public theorem simpleIndices_subset (J : Set S.D.Root) :
    A.simpleIndices J ⊆ A.system.S := by
  rintro _ ⟨i, hi, rfl⟩
  exact (A.simple i).property

/-- The abstract standard parabolic. Its coincidence with `rootParabolic`
is an obligation, rather than an assumption in the aligned Tits system. -/
def standard (J : Set S.D.Root) : Subgroup (Variety.Point K) :=
  A.system.standardParabolic (A.simpleIndices J)

public theorem simpleIndices_mono {J J' : Set S.D.Root} (h : J ⊆ J') :
    A.simpleIndices J ⊆ A.simpleIndices J' := by
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, h hi, rfl⟩

public theorem simpleIndices_le_iff {J J' : Set S.D.Root}
    (hJ : J ⊆ S.D.simple) (_hJ' : J' ⊆ S.D.simple) :
    A.simpleIndices J ⊆ A.simpleIndices J' ↔ J ⊆ J' := by
  constructor
  · intro h i hi
    obtain ⟨j, hj, heq⟩ := h (show (A.simple ⟨i, hJ hi⟩).val ∈
      A.simpleIndices J from ⟨⟨i, hJ hi⟩, hi, rfl⟩)
    have heq' : j = ⟨i, hJ hi⟩ := A.simple.injective (Subtype.ext heq)
    change j.val ∈ J' at hj
    have hjval : j.val = i := congrArg Subtype.val heq'
    simpa only [hjval] using hj
  · exact A.simpleIndices_mono

/-- The abstract family has the required order, once it is compared with the
literal root-generated family. -/
public theorem standard_le_iff {J J' : Set S.D.Root}
    (hJ : J ⊆ S.D.simple) (hJ' : J' ⊆ S.D.simple) :
    A.standard J ≤ A.standard J' ↔ J ⊆ J' := by
  rw [standard, standard, A.system.standardParabolic_le_iff
    (A.simpleIndices_subset J) (A.simpleIndices_subset J')]
  exact A.simpleIndices_le_iff hJ hJ'

variable [IsAlgClosed k]

/-- The concrete consumer of the root-group comparison prerequisite. Its
extra premise must be discharged before claiming algebraic classification. -/
public theorem rootParabolic_le_iff_of_comparison
    (hcompare : ∀ J, J ⊆ S.D.simple →
      (rootParabolic S J).toSubgroup = A.standard J)
    {J J' : Set S.D.Root} (hJ : J ⊆ S.D.simple) (hJ' : J' ⊆ S.D.simple) :
    rootParabolic S J ≤ rootParabolic S J' ↔ J ⊆ J' := by
  change (rootParabolic S J).toSubgroup ≤ (rootParabolic S J').toSubgroup ↔ _
  rw [hcompare J hJ, hcompare J' hJ']
  exact A.standard_le_iff hJ hJ'

end AlignedTitsSystem
end Theory.AlgebraicGroup.InvariantLeviGeometry.Classification

end
