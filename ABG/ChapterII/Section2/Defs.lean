module

public import ABG.ChapterII.Section1.FusionPatterns

/-!
# Q-groups, D-groups and QD-groups

ABG Chapter II §2 Definitions 1–4 (article pp14–15) first name the three
non-complement fusion patterns and then enlarge Q and D. The full-Sylow
predicates retain all clauses of the corresponding Section 1 proposition.
Their simpler structural characterizations require proofs of those propositions.

The enlarged Q witness embeds the actual Sylow subgroup R of G into an actual
quasi-dihedral or wreathed group S. It records the unique generalized quaternion
subgroup Y of largest order in S and a normal subgroup K of two-power index
with no normal subgroup of index two. The image of R intersected with K is
exactly Y; thus the quaternion and normal-subgroup witnesses cannot be chosen
independently. Every subgroup of the center of R is weakly closed in R.
For finite G, normality ensures R intersected with K is a Sylow subgroup of K.

The Q predicate retains the original class and adjoins this overgroup class.
Their agreement for full quasi-dihedral/wreathed Sylow subgroups remains a
proof obligation, rather than an assumed fusion equivalence. The D predicate
adjoins precisely the groups with dihedral Sylow two-subgroups and no normal
two-complement. These exposed source definitions supply the local classes for
the later characteristic-power construction and induction on simple sections.
-/

noncomputable section

namespace ABG

universe u

/-- Chapter II Definition 1: the entire first fusion alternative. -/
@[expose] public def IsQDGroup (G : Type u) [Group G] : Prop :=
  (∃ (S : Sylow 2 G) (T Q : Subgroup G),
    QuasiDihedralFusionFrame S T Q ∧ QuasiDihedralQDPattern T Q) ∨
  (∃ (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G),
    WreathedFusionFrame S n U V ∧ WreathedQDPattern U V)

/-- The original Q-group definition, before the enlargement in Definition 3. -/
@[expose] public def IsFullSylowQGroup (G : Type u) [Group G] : Prop :=
  (∃ (S : Sylow 2 G) (T Q : Subgroup G),
    QuasiDihedralFusionFrame S T Q ∧ QuasiDihedralQPattern S T Q) ∨
  (∃ (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G),
    WreathedFusionFrame S n U V ∧ WreathedQPattern S n U V)

/-- The original D-group definition, before adjoining dihedral Sylow groups. -/
@[expose] public def IsFullSylowDGroup (G : Type u) [Group G] : Prop :=
  (∃ (S : Sylow 2 G) (T Q : Subgroup G),
    QuasiDihedralFusionFrame S T Q ∧ QuasiDihedralDPattern T Q) ∨
  (∃ (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G),
    WreathedFusionFrame S n U V ∧ WreathedDPattern U V)

/-- The unique generalized quaternion subgroup of largest order, as used in
Definition 3. The order maximality is among quaternion subgroups only. -/
@[expose] public def IsLargestQuaternionSubgroup
    {S : Type u} [Group S] (Y : Subgroup S) : Prop :=
  IsGeneralizedQuaternionGroup Y ∧
    ∀ Z : Subgroup S, IsGeneralizedQuaternionGroup Z →
      Nat.card Z ≤ Nat.card Y ∧ (Nat.card Z = Nat.card Y → Z = Y)

/-- Chapter II Definition 3, with the actual Sylow subgroup embedded in an
actual quasi-dihedral or wreathed overgroup. The image of `R ∩ K` is precisely
`Y`, so the quaternion subgroup and the normal subgroup are linked. -/
@[expose] public def IsQuaternionOvergroupQGroup (G : Type u) [Group G] : Prop :=
  ∃ (S : Type u) (inst : Group S), letI := inst;
    (Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) ∧
      ∃ (R : Sylow 2 G) (f : R →* S) (Y : Subgroup S) (K : Subgroup G),
        Function.Injective f ∧ IsLargestQuaternionSubgroup Y ∧
          K.Normal ∧ (∃ m : ℕ, K.index = 2 ^ m) ∧
            HasNoNormalIndexTwoSubgroup K ∧ HasWeaklyClosedCenterSubgroups (R : Subgroup G) ∧
              (K.comap (R : Subgroup G).subtype).map f = Y

/-- The enlarged Q-group class retains Definition 1 and adds Definition 3.
Their agreement on full quasi-dihedral/wreathed Sylow groups is a theorem,
not a definitional assumption about fusion. -/
@[expose] public def IsQGroup (G : Type u) [Group G] : Prop :=
  IsFullSylowQGroup G ∨ IsQuaternionOvergroupQGroup G

/-- Chapter II Definition 4: add the dihedral groups without a normal
2-complement to the original D-group class. -/
@[expose] public def IsDGroup (G : Type u) [Group G] : Prop :=
  IsFullSylowDGroup G ∨
    (HasDihedralSylowTwo G ∧ ¬ HasNormalPComplement 2 G)

end ABG
