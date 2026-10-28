module

public import Theory.AlgebraicGroup.ClosedSubgroup.Product
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Dimension.Product
public import Theory.AlgebraicGroup.Foundations
public import Theory.AlgebraicGroup.Jordan.ClosedSubgroup
public import Theory.AlgebraicGroup.Unipotent.Basic
public import Theory.AlgebraicGroup.Morphism.Connected

set_option linter.style.haveILetI false

/-!
# Semisimple commutators in connected unipotent groups

This module proves the parts of A. Borel, *Linear Algebraic Groups*, Chapter 3,
Proposition 9.3 needed for solvable-group induction.  If `U` is a connected
unipotent closed subgroup and a semisimple point `s` normalizes `U`, then the
closed fixed subgroup `C_U(s)` is connected (part (2)).  Bor1's map
`c_s(u) = u * s * u⁻¹ * s⁻¹` also carries its point image `M = c_s(U)` onto
itself, so its restriction to `M` is a bijection (part (3)).  The latter is the
input used in Bor1 10.6(3) to force `M` into every term of a descending central
series.

The proof establishes a unique point decomposition `U = M * C_U(s)` by
induction on the dimension of `U`.  In the commutative case the commutator map
is constructed as a regular homomorphism; closed image and kernel results,
connectedness, and the dimension formula show that multiplication gives the
decomposition.  In the general case the identity component of the algebraic
center supplies a positive-dimensional connected, central, `s`-normalized
subgroup.  Passing through the actual normalizer quotient lowers dimension,
and the quotient and central decompositions are combined.  The same induction
proves fixed-subgroup connectedness: in the commutative case the product map
remains surjective after restricting the kernel to its identity component; in
the general case the fixed-subgroup morphism has connected quotient and
connected kernel.  Uniqueness follows from the Jordan decomposition: a point
both in the commutator image and fixed by `s` must be trivial.

The exported conclusions include the closed fixed subgroup and its connectedness
(Bor1 9.3(2)), together with the point-level factorization needed in Bor1
10.6(4).  We do not assert that `M` is a closed subvariety or that the
restriction is a variety isomorphism; those stronger statements use the
separate closed-orbit result Bor1 9.2.
-/

universe u

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Bor1's map `c_s(u) = u s u^-1 s^-1`, expressed using the repository's
commutator convention. -/
@[expose]
public def semisimpleCommutator {G : Variety k} [AlgebraicGroup G]
    (s u : Variety.Point G) : Variety.Point G :=
  u * s * u⁻¹ * s⁻¹

omit [IsAlgClosed k] in
public lemma semisimpleCommutator_eq_commutator
    {G : Variety k} [AlgebraicGroup G] (s u : Variety.Point G) :
    semisimpleCommutator s u = ⁅u, s⁆ := by
  rfl

omit [IsAlgClosed k] in
public lemma semisimpleCommutator_mul
    {G : Variety k} [AlgebraicGroup G] (s u v : Variety.Point G) :
    semisimpleCommutator s (u * v) =
      u * semisimpleCommutator s v * u⁻¹ * semisimpleCommutator s u := by
  simp only [semisimpleCommutator]
  group

omit [IsAlgClosed k] in
public lemma semisimpleCommutator_mem_of_mem_normalizer
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    {s u : Variety.Point G}
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (hu : u ∈ U.toSubgroup) :
    semisimpleCommutator s u ∈ U.toSubgroup := by
  have hconj : s * u⁻¹ * s⁻¹ ∈ U.toSubgroup :=
    (Subgroup.mem_normalizer_iff.mp hs u⁻¹).mp (U.toSubgroup.inv_mem hu)
  simpa [semisimpleCommutator, mul_assoc] using
    U.toSubgroup.mul_mem hu hconj

/-- The commutator map on the points of a normalized closed subgroup. -/
@[expose]
public def semisimpleCommutatorOn
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Variety.Point U.carrierVariety → Variety.Point U.carrierVariety :=
  fun u ↦ U.pointEquiv.symm
    ⟨semisimpleCommutator s (U.inclusion.onPoints u),
      semisimpleCommutator_mem_of_mem_normalizer U hs
        (U.pointEquiv u).property⟩

omit [IsAlgClosed k] in
public lemma semisimpleCommutatorOn_inclusion
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (u : Variety.Point U.carrierVariety) :
    U.inclusion.onPoints (semisimpleCommutatorOn U s hs u) =
      semisimpleCommutator s (U.inclusion.onPoints u) := by
  change (U.pointEquiv (U.pointEquiv.symm _)).val = _
  rw [U.pointEquiv.apply_symm_apply]

/-- The point image `M = c_s(U)` from Bor1 9.3. -/
@[expose]
public def semisimpleCommutatorImage
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Set (Variety.Point U.carrierVariety) :=
  Set.range (semisimpleCommutatorOn U s hs)

/-- The fixed points of conjugation by `s`, equivalently the kernel of
`c_s`. -/
@[expose]
public def semisimpleCommutatorFixedPoints
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Set (Variety.Point U.carrierVariety) :=
  {u | semisimpleCommutatorOn U s hs u = 1}

/-- The centralizer of a single point, represented as the closed equalizer of
left and right multiplication by that point. -/
@[expose]
public noncomputable def semisimpleCommutatorPointCentralizer
    {G : Variety k} [AlgebraicGroup G] (s : Variety.Point G) :
    ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup
    (Subgroup.centralizer ({s} : Set (Variety.Point G))) (by
      have hclosed : IsZariskiClosed G
          {g : Variety.Point G |
            (Theory.AlgebraicGroup.leftMulMorphism G s).toFun g =
              (Theory.AlgebraicGroup.rightMulMorphism G s).toFun g} :=
        Variety.Morphism.isZariskiClosed_equalizer
          (Theory.AlgebraicGroup.leftMulMorphism G s)
          (Theory.AlgebraicGroup.rightMulMorphism G s)
      have heq : (Subgroup.centralizer ({s} : Set (Variety.Point G)) :
          Set (Variety.Point G)) =
          {g : Variety.Point G |
            (Theory.AlgebraicGroup.leftMulMorphism G s).toFun g =
              (Theory.AlgebraicGroup.rightMulMorphism G s).toFun g} := by
        ext g
        change g ∈ Subgroup.centralizer ({s} : Set (Variety.Point G)) ↔ _
        rw [Subgroup.mem_centralizer_iff]
        constructor
        · intro h
          have hs := h s (by simp)
          change s * g = g * s
          simpa only [Theory.AlgebraicGroup.leftMulMorphism_apply,
            Theory.AlgebraicGroup.rightMulMorphism_apply] using hs
        · intro h t ht
          change s * g = g * s at h
          simpa [Set.mem_singleton_iff.mp ht] using h
      rw [heq]
      exact hclosed)

omit [IsAlgClosed k] in
public lemma semisimpleCommutator_eq_one_iff_commute
    {G : Variety k} [AlgebraicGroup G] (s u : Variety.Point G) :
    semisimpleCommutator s u = 1 ↔ u * s = s * u := by
  simp only [semisimpleCommutator]
  constructor
  · intro h
    calc
      u * s = (u * s * u⁻¹ * s⁻¹) * (s * u) := by group
      _ = s * u := by rw [h, one_mul]
  · intro h
    rw [h]
    group

/-- The closed subgroup of `U` fixed by conjugation by `s`.  Its definition is
independent of the normalizing proof term used by `semisimpleCommutatorOn`. -/
@[expose]
public noncomputable def semisimpleCommutatorFixedSubgroup
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G) : ClosedSubgroup U.carrierVariety :=
  U.inclusion.closedSubgroupPreimage (semisimpleCommutatorPointCentralizer s)

omit [IsAlgClosed k] in
public lemma semisimpleCommutatorFixedSubgroup_mem_iff
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G) (u : Variety.Point U.carrierVariety) :
    u ∈ semisimpleCommutatorFixedSubgroup U s ↔
      U.inclusion.onPoints u * s = s * U.inclusion.onPoints u := by
  change U.inclusion.onPoints u ∈
      semisimpleCommutatorPointCentralizer s ↔ _
  change U.inclusion.onPoints u ∈
      Subgroup.centralizer ({s} : Set (Variety.Point G)) ↔ _
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h s (by simp)).symm
  · intro h y hy
    simpa [Set.mem_singleton_iff.mp hy] using h.symm

omit [IsAlgClosed k] in
public lemma semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (u : Variety.Point U.carrierVariety) :
    u ∈ semisimpleCommutatorFixedPoints U s hs ↔
      u ∈ semisimpleCommutatorFixedSubgroup U s := by
  change semisimpleCommutatorOn U s hs u = 1 ↔ _
  rw [← U.inclusion_injective.eq_iff]
  rw [semisimpleCommutatorOn_inclusion, U.inclusion.onPoints.map_one]
  rw [semisimpleCommutator_eq_one_iff_commute]
  exact (semisimpleCommutatorFixedSubgroup_mem_iff U s u).symm

private def HasSemisimpleCommutatorDecomposition
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Prop :=
  (∀ u, ∃ m, m ∈ semisimpleCommutatorImage U s hs ∧
      ∃ z, z ∈ semisimpleCommutatorFixedPoints U s hs ∧ u = m * z) ∧
    ∀ {m₁ m₂ z₁ z₂},
      m₁ ∈ semisimpleCommutatorImage U s hs →
      m₂ ∈ semisimpleCommutatorImage U s hs →
      z₁ ∈ semisimpleCommutatorFixedPoints U s hs →
      z₂ ∈ semisimpleCommutatorFixedPoints U s hs →
      m₁ * z₁ = m₂ * z₂ → m₁ = m₂ ∧ z₁ = z₂

private def HasSemisimpleCommutatorPackage
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Prop :=
  HasSemisimpleCommutatorDecomposition U s hs ∧
    Variety.IsConnected
      (semisimpleCommutatorFixedSubgroup U s).carrierVariety

private def semisimpleCommutatorAmbientImage
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G) : Set (Variety.Point G) :=
  semisimpleCommutator s '' (U : Set (Variety.Point G))

private def semisimpleCommutatorAmbientFixedPoints
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G) : Set (Variety.Point G) :=
  {u | u ∈ U ∧ semisimpleCommutator s u = 1}

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorAmbientFixedPoints_one
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G) :
    (1 : Variety.Point G) ∈ semisimpleCommutatorAmbientFixedPoints U s := by
  exact ⟨U.toSubgroup.one_mem, by simp [semisimpleCommutator]⟩

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorAmbientFixedPoints_mul
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G) {u v : Variety.Point G}
    (hu : u ∈ semisimpleCommutatorAmbientFixedPoints U s)
    (hv : v ∈ semisimpleCommutatorAmbientFixedPoints U s) :
    u * v ∈ semisimpleCommutatorAmbientFixedPoints U s := by
  refine ⟨U.toSubgroup.mul_mem hu.1 hv.1, ?_⟩
  rw [semisimpleCommutator_eq_one_iff_commute]
  have hu' := (semisimpleCommutator_eq_one_iff_commute s u).mp hu.2
  have hv' := (semisimpleCommutator_eq_one_iff_commute s v).mp hv.2
  calc
    u * v * s = u * (v * s) := by group
    _ = u * (s * v) := by rw [hv']
    _ = (u * s) * v := by group
    _ = (s * u) * v := by rw [hu']
    _ = s * (u * v) := by group

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorAmbientFixedPoints_inv
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G) {u : Variety.Point G}
    (hu : u ∈ semisimpleCommutatorAmbientFixedPoints U s) :
    u⁻¹ ∈ semisimpleCommutatorAmbientFixedPoints U s := by
  refine ⟨U.toSubgroup.inv_mem hu.1, ?_⟩
  rw [semisimpleCommutator_eq_one_iff_commute]
  have hu' := (semisimpleCommutator_eq_one_iff_commute s u).mp hu.2
  have h := congrArg (fun x ↦ u⁻¹ * x * u⁻¹) hu'
  simpa [mul_assoc] using h.symm

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorOn_mul
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (u v : Variety.Point U.carrierVariety) :
    semisimpleCommutatorOn U s hs (u * v) =
      u * semisimpleCommutatorOn U s hs v * u⁻¹ *
        semisimpleCommutatorOn U s hs u := by
  apply U.inclusion_injective
  simp only [map_mul, map_inv, semisimpleCommutatorOn_inclusion]
  exact semisimpleCommutator_mul s _ _

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorFixedPoints_one
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    (1 : Variety.Point U.carrierVariety) ∈
      semisimpleCommutatorFixedPoints U s hs := by
  change semisimpleCommutatorOn U s hs 1 = 1
  apply U.inclusion_injective
  rw [semisimpleCommutatorOn_inclusion, U.inclusion.onPoints.map_one]
  simp [semisimpleCommutator]

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorFixedPoints_mul
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    {u v : Variety.Point U.carrierVariety}
    (hu : u ∈ semisimpleCommutatorFixedPoints U s hs)
    (hv : v ∈ semisimpleCommutatorFixedPoints U s hs) :
    u * v ∈ semisimpleCommutatorFixedPoints U s hs := by
  have hu' : U.inclusion.onPoints u ∈
      semisimpleCommutatorAmbientFixedPoints U s := by
    refine ⟨(U.pointEquiv u).property, ?_⟩
    have h := congrArg U.inclusion.onPoints hu
    rwa [semisimpleCommutatorOn_inclusion,
      U.inclusion.onPoints.map_one] at h
  have hv' : U.inclusion.onPoints v ∈
      semisimpleCommutatorAmbientFixedPoints U s := by
    refine ⟨(U.pointEquiv v).property, ?_⟩
    have h := congrArg U.inclusion.onPoints hv
    rwa [semisimpleCommutatorOn_inclusion,
      U.inclusion.onPoints.map_one] at h
  have huv' := semisimpleCommutatorAmbientFixedPoints_mul U s hu' hv'
  change semisimpleCommutatorOn U s hs (u * v) = 1
  apply U.inclusion_injective
  rw [semisimpleCommutatorOn_inclusion, map_mul,
    U.inclusion.onPoints.map_one]
  exact huv'.2

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorFixedPoints_inv
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    {u : Variety.Point U.carrierVariety}
    (hu : u ∈ semisimpleCommutatorFixedPoints U s hs) :
    u⁻¹ ∈ semisimpleCommutatorFixedPoints U s hs := by
  have hu' : U.inclusion.onPoints u ∈
      semisimpleCommutatorAmbientFixedPoints U s := by
    refine ⟨(U.pointEquiv u).property, ?_⟩
    have h := congrArg U.inclusion.onPoints hu
    rwa [semisimpleCommutatorOn_inclusion,
      U.inclusion.onPoints.map_one] at h
  have huInv' := semisimpleCommutatorAmbientFixedPoints_inv U s hu'
  change semisimpleCommutatorOn U s hs u⁻¹ = 1
  apply U.inclusion_injective
  rw [semisimpleCommutatorOn_inclusion, map_inv,
    U.inclusion.onPoints.map_one]
  exact huInv'.2

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorOn_eq_iff
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (u v : Variety.Point U.carrierVariety) :
    semisimpleCommutatorOn U s hs u = semisimpleCommutatorOn U s hs v ↔
      semisimpleCommutatorOn U s hs (v⁻¹ * u) = 1 := by
  constructor
  · intro h
    apply U.inclusion_injective
    rw [semisimpleCommutatorOn_inclusion, U.inclusion.onPoints.map_one]
    rw [U.inclusion.onPoints.map_mul, U.inclusion.onPoints.map_inv]
    have hamb := congrArg U.inclusion.onPoints h
    rw [semisimpleCommutatorOn_inclusion,
      semisimpleCommutatorOn_inclusion] at hamb
    simp only [semisimpleCommutator] at hamb ⊢
    have hamb' :
        U.inclusion.onPoints u * s * (U.inclusion.onPoints u)⁻¹ =
          U.inclusion.onPoints v * s * (U.inclusion.onPoints v)⁻¹ := by
      calc
        U.inclusion.onPoints u * s * (U.inclusion.onPoints u)⁻¹ =
            (U.inclusion.onPoints u * s * (U.inclusion.onPoints u)⁻¹ * s⁻¹) * s := by
              group
        _ = (U.inclusion.onPoints v * s * (U.inclusion.onPoints v)⁻¹ * s⁻¹) * s :=
          congrArg (fun x ↦ x * s) hamb
        _ = U.inclusion.onPoints v * s * (U.inclusion.onPoints v)⁻¹ := by
          group
    calc
      (U.inclusion.onPoints v)⁻¹ * U.inclusion.onPoints u * s *
          ((U.inclusion.onPoints v)⁻¹ * U.inclusion.onPoints u)⁻¹ * s⁻¹ =
          (U.inclusion.onPoints v)⁻¹ *
            (U.inclusion.onPoints u * s * (U.inclusion.onPoints u)⁻¹) *
              U.inclusion.onPoints v * s⁻¹ := by group
      _ = (U.inclusion.onPoints v)⁻¹ *
            (U.inclusion.onPoints v * s * (U.inclusion.onPoints v)⁻¹) *
              U.inclusion.onPoints v * s⁻¹ := by rw [hamb']
      _ = 1 := by group
  · intro h
    apply U.inclusion_injective
    rw [semisimpleCommutatorOn_inclusion,
      semisimpleCommutatorOn_inclusion]
    have hamb := congrArg U.inclusion.onPoints h
    rw [semisimpleCommutatorOn_inclusion, U.inclusion.onPoints.map_one] at hamb
    rw [U.inclusion.onPoints.map_mul, U.inclusion.onPoints.map_inv] at hamb
    simp only [semisimpleCommutator] at hamb ⊢
    have hamb' :
        (U.inclusion.onPoints v)⁻¹ * U.inclusion.onPoints u * s *
            (U.inclusion.onPoints u)⁻¹ * U.inclusion.onPoints v = s := by
      calc
        (U.inclusion.onPoints v)⁻¹ * U.inclusion.onPoints u * s *
            (U.inclusion.onPoints u)⁻¹ * U.inclusion.onPoints v =
            ((U.inclusion.onPoints v)⁻¹ * U.inclusion.onPoints u * s *
              ((U.inclusion.onPoints v)⁻¹ * U.inclusion.onPoints u)⁻¹ * s⁻¹) * s := by
                group
        _ = s := by rw [hamb]; simp
    have h' := congrArg
      (fun x ↦ U.inclusion.onPoints v * x * (U.inclusion.onPoints v)⁻¹) hamb'
    have huv : U.inclusion.onPoints u * s * (U.inclusion.onPoints u)⁻¹ =
        U.inclusion.onPoints v * s * (U.inclusion.onPoints v)⁻¹ := by
      simpa [mul_assoc] using h'
    exact congrArg (fun x ↦ x * s⁻¹) huv

private lemma unipotent_fixed_commutator_eq_one
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    {u : Variety.Point U.carrierVariety}
    (huImage : u ∈ semisimpleCommutatorImage U s hs)
    (huFixed : u ∈ semisimpleCommutatorFixedPoints U s hs) :
    u = 1 := by
  obtain ⟨v, rfl⟩ := huImage
  let z := semisimpleCommutatorOn U s hs v
  have hzFixed : semisimpleCommutatorOn U s hs z = 1 := huFixed
  have hzAmbientFixed :
      semisimpleCommutator s (U.inclusion.onPoints z) = 1 := by
    rw [← semisimpleCommutatorOn_inclusion U s hs]
    exact congrArg U.inclusion.onPoints hzFixed |>.trans U.inclusion.onPoints.map_one
  have hzs : U.inclusion.onPoints z * s = s * U.inclusion.onPoints z := by
    calc
      U.inclusion.onPoints z * s =
          semisimpleCommutator s (U.inclusion.onPoints z) *
            (s * U.inclusion.onPoints z) := by
              simp only [semisimpleCommutator]
              group
      _ = s * U.inclusion.onPoints z := by rw [hzAmbientFixed, one_mul]
  have hzUni : IsUnipotentElement G (U.inclusion.onPoints z) :=
    morphism_preserves_unipotentElement U.inclusion z (hU z)
  have hconjSemi : IsSemisimpleElement G
      (U.inclusion.onPoints v * s * (U.inclusion.onPoints v)⁻¹) := by
    let c : AlgebraicGroup.Morphism G G :=
      { toVariety := AlgebraicGroup.conjugationByMorphism G (U.inclusion.onPoints v)
        map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
        map_mul := by
          intro x y
          simp only [AlgebraicGroup.conjugationByMorphism_apply]
          group }
    have hc := morphism_preserves_semisimpleElement c s hsSemi
    change IsSemisimpleElement G
      ((AlgebraicGroup.conjugationByMorphism G
        (U.inclusion.onPoints v)).toFun s) at hc
    rw [AlgebraicGroup.conjugationByMorphism_apply] at hc
    exact hc
  have hzsmul : U.inclusion.onPoints z * s =
      U.inclusion.onPoints v * s * (U.inclusion.onPoints v)⁻¹ := by
    rw [semisimpleCommutatorOn_inclusion]
    simp only [semisimpleCommutator]
    group
  have hprodSemi : IsSemisimpleElement G (s * U.inclusion.onPoints z) := by
    rw [← hzs, hzsmul]
    exact hconjSemi
  let d : JordanDecomposition (s * U.inclusion.onPoints z) :=
    { semisimplePart := s
      unipotentPart := U.inclusion.onPoints z
      eq_mul := rfl
      commute := hzs.symm
      semisimple := hsSemi
      unipotent := hzUni }
  let trivial : JordanDecomposition (s * U.inclusion.onPoints z) :=
    { semisimplePart := s * U.inclusion.onPoints z
      unipotentPart := 1
      eq_mul := by simp
      commute := Commute.one_right _
      semisimple := hprodSemi
      unipotent := one_isUnipotentElement G }
  have h := d.unique trivial
  have hzOne : U.inclusion.onPoints z = 1 :=
    congrArg JordanDecomposition.unipotentPart h
  exact U.inclusion_injective (hzOne.trans U.inclusion.onPoints.map_one.symm)

private lemma unipotent_ambient_image_fixed_eq_one
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    {u : Variety.Point G}
    (huImage : u ∈ semisimpleCommutatorAmbientImage U s)
    (huFixed : u ∈ semisimpleCommutatorAmbientFixedPoints U s) :
    u = 1 := by
  let uU : Variety.Point U.carrierVariety :=
    U.pointEquiv.symm ⟨u, huFixed.1⟩
  have huUImage : uU ∈ semisimpleCommutatorImage U s hs := by
    obtain ⟨v, hvU, hv⟩ := huImage
    let vU : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨v, hvU⟩
    refine ⟨vU, U.inclusion_injective ?_⟩
    rw [semisimpleCommutatorOn_inclusion]
    change semisimpleCommutator s v = u
    exact hv
  have huUFixed : uU ∈ semisimpleCommutatorFixedPoints U s hs := by
    change semisimpleCommutatorOn U s hs uU = 1
    apply U.inclusion_injective
    rw [semisimpleCommutatorOn_inclusion, U.inclusion.onPoints.map_one]
    change semisimpleCommutator s u = 1
    exact huFixed.2
  have huUOne := unipotent_fixed_commutator_eq_one
    U hU s hsSemi hs huUImage huUFixed
  have hIncl : U.inclusion.onPoints uU = 1 := by
    simpa only [U.inclusion.onPoints.map_one] using
      congrArg U.inclusion.onPoints huUOne
  have huIncl : U.inclusion.onPoints uU = u := by
    change (U.pointEquiv uU).val = u
    simp [uU]
  exact huIncl ▸ hIncl

private theorem identityComponentAmbient_mem_normalizer
    {G : Variety k} [AlgebraicGroup G] (C : ClosedSubgroup G)
    (g : Variety.Point G) (hg : g ∈ C.normalizer.toSubgroup) :
    g ∈ C.identityComponentAmbient.normalizer.toSubgroup := by
  let N := C.identityComponentAmbient
  let D := N.conjugate g
  have hDset : (D : Set (Variety.Point G)) =
      (fun x ↦ g * x * g⁻¹) '' (N : Set (Variety.Point G)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      exact (N.mem_conjugate_iff g x).mp hx
    · rintro ⟨y, hy, rfl⟩
      apply (N.mem_conjugate_iff g _).mpr
      change g⁻¹ * (g * y * g⁻¹) * g ∈ N.toSubgroup
      change y ∈ N.toSubgroup at hy
      simpa [mul_assoc] using hy
  have hNconn : _root_.IsConnected (N : Set (Variety.Point G)) :=
    C.identityComponentAmbient_isConnected
  have hDconn : _root_.IsConnected (D : Set (Variety.Point G)) := by
    rw [hDset]
    exact hNconn.image
      (fun x ↦ g * x * g⁻¹)
      (AlgebraicGroup.conjugationByMorphism G g).continuous.continuousOn
  have hDC : D ≤ C := by
    intro x hx
    have hx' := (N.mem_conjugate_iff g x).mp hx
    have hxC : g⁻¹ * x * g ∈ C :=
      C.identityComponentAmbient_le hx'
    have hnorm := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)
    have hxC' := hnorm.mp hxC
    change x ∈ C.toSubgroup
    simpa [mul_assoc] using hxC'
  have hDN : D ≤ N :=
    connected_closedSubgroup_le_identityComponentAmbient D C hDconn hDC
  have hdim : Variety.dimension N.carrierVariety =
      Variety.dimension D.carrierVariety := N.conjugate_dimension_eq g
  have hDN_eq : D = N := by
    by_contra hne
    have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne
      D N hDN hne hDconn hNconn
    exact (ne_of_lt hlt) hdim.symm
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  change x ∈ N.toSubgroup ↔ g * x * g⁻¹ ∈ N.toSubgroup
  constructor
  · intro hx
    rw [← hDN_eq]
    change g * x * g⁻¹ ∈ (D : Set (Variety.Point G))
    rw [hDset]
    exact ⟨x, hx, rfl⟩
  · intro hx
    have hxD : g * x * g⁻¹ ∈ D.toSubgroup := by
      rw [hDN_eq]
      exact hx
    change g * x * g⁻¹ ∈ (D : Set (Variety.Point G)) at hxD
    rw [hDset] at hxD
    obtain ⟨y, hy, hxy⟩ := hxD
    have hxy' : x = y := by
      have := congrArg (fun z ↦ g⁻¹ * z * g) hxy
      simpa [mul_assoc] using this.symm
    rw [hxy']
    exact hy

omit [IsAlgClosed k] in
private lemma closedSubgroup_carrier_isConnected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private lemma closedSubgroup_isConnected_of_carrier
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : Variety.IsConnected H.carrierVariety) :
    _root_.IsConnected (H : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    connectedSpace_iff_univ.mpr hH
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    e.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

private theorem source_connected_of_surjective_morphism_of_connected_kernel
    {A B : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    (f : AlgebraicGroup.Morphism A B)
    (hf : Function.Surjective f.onPoints)
    (hB : Variety.IsConnected B)
    (hker : Variety.IsConnected f.kernelClosedSubgroup.carrierVariety) :
    Variety.IsConnected A := by
  let R : ClosedSubgroup B := ClosedSubgroup.top
  let P : ClosedSubgroup A := f.closedSubgroupPreimage R
  let I : ClosedSubgroup A := P.identityComponentAmbient
  have hRset : _root_.IsConnected (R : Set (Variety.Point B)) := by
    change _root_.IsConnected (Set.univ : Set (Variety.Point B))
    exact hB
  have himage : (f.comp I.inclusion).imageClosedSubgroup = R :=
    f.closedSubgroupPreimage_identityComponent_image_eq hf R hRset
  have hIconn : _root_.IsConnected (I : Set (Variety.Point A)) := by
    simpa [I] using P.identityComponentAmbient_isConnected
  have hI0 : I.toSubgroup ≤ AlgebraicGroup.identityComponentSubgroup A := by
    intro x hx
    exact connected_closedSubgroup_subset_identityComponent A hIconn hx
  have hker0 : f.kernelClosedSubgroup.toSubgroup ≤
      AlgebraicGroup.identityComponentSubgroup A := by
    intro x hx
    exact connected_closedSubgroup_subset_identityComponent A
      (closedSubgroup_isConnected_of_carrier f.kernelClosedSubgroup hker) hx
  apply (identityComponent_eq_univ_iff_isConnected A).mp
  apply Set.eq_univ_of_univ_subset
  intro x _
  have hfx : f.onPoints x ∈ R := by trivial
  rw [← himage] at hfx
  change f.onPoints x ∈ (f.comp I.inclusion).image at hfx
  obtain ⟨y, hy⟩ := hfx
  let z := I.inclusion.onPoints y
  have hzI : z ∈ I := (I.pointEquiv y).property
  have hz0 : z ∈ AlgebraicGroup.identityComponentSubgroup A := hI0 hzI
  have hdiffKer : z⁻¹ * x ∈ f.kernelClosedSubgroup := by
    change f.onPoints (z⁻¹ * x) = 1
    rw [map_mul, map_inv]
    have hy' : f.onPoints z = f.onPoints x := by
      change f.onPoints (I.inclusion.onPoints y) = f.onPoints x
      exact hy
    rw [hy']
    group
  have hdiff0 : z⁻¹ * x ∈ AlgebraicGroup.identityComponentSubgroup A :=
    hker0 hdiffKer
  have := (AlgebraicGroup.identityComponentSubgroup A).mul_mem hz0 hdiff0
  rw [← AlgebraicGroup.identityComponentSubgroup_carrier]
  simpa [mul_assoc] using this

omit [IsAlgClosed k] in
private lemma map_semisimpleCommutator
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (s u : Variety.Point G) :
    f.onPoints (semisimpleCommutator s u) =
      semisimpleCommutator (f.onPoints s) (f.onPoints u) := by
  simp [semisimpleCommutator, map_mul, map_inv]

private theorem exists_normalized_connected_central_subgroup
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (hnotcomm : ¬ ∀ x ∈ U.toSubgroup, ∀ y ∈ U.toSubgroup, x * y = y * x) :
    ∃ N : ClosedSubgroup G,
      Variety.IsConnected N.carrierVariety ∧
      IsUnipotentAlgebraicGroup N.carrierVariety ∧
      N ≤ U ∧
      (∀ n ∈ N.toSubgroup, ∀ u ∈ U.toSubgroup, n * u = u * n) ∧
      s ∈ Subgroup.normalizer (N.toSubgroup : Set (Variety.Point G)) ∧
      0 < Variety.dimension N.carrierVariety := by
  have hUpos : 0 < Variety.dimension U.carrierVariety := by
    by_contra hpos
    have hdim0 : Variety.dimension U.carrierVariety = 0 :=
      le_antisymm (not_lt.mp hpos) (by simp)
    letI : Finite (Variety.Point U.carrierVariety) :=
      (dimension_zero_iff_finite_points U.carrierVariety).mp hdim0
    let : T1Space (Variety.Point U.carrierVariety) :=
      ⟨fun x ↦ Variety.isClosed_iff_isZariskiClosed.mpr
        (isZariskiClosed_singleton U.carrierVariety x)⟩
    let : ConnectedSpace (Variety.Point U.carrierVariety) :=
      connectedSpace_iff_univ.mpr hUconn
    let : DiscreteTopology (Variety.Point U.carrierVariety) :=
      Finite.instDiscreteTopology
    let : Subsingleton (Variety.Point U.carrierVariety) :=
      PreconnectedSpace.trivial_of_discrete
    apply hnotcomm
    intro x hx y hy
    let xU := U.pointEquiv.symm ⟨x, hx⟩
    let yU := U.pointEquiv.symm ⟨y, hy⟩
    have hxy : xU * yU = yU * xU := Subsingleton.elim _ _
    have hxy' := congrArg U.inclusion.onPoints hxy
    have hxIncl : U.inclusion.onPoints xU = x := by
      change (U.pointEquiv xU).val = x
      simp [xU]
    have hyIncl : U.inclusion.onPoints yU = y := by
      change (U.pointEquiv yU).val = y
      simp [yU]
    simpa only [map_mul, hxIncl, hyIncl] using hxy'
  let Z : ClosedSubgroup U.carrierVariety :=
    (ClosedSubgroup.top (G := U.carrierVariety)).centralizer
  letI : AlgebraicGroup Z.carrierVariety := Z.carrierAlgebraicGroup
  let j : AlgebraicGroup.Morphism Z.carrierVariety G :=
    U.inclusion.comp Z.inclusion
  let C : ClosedSubgroup G := j.imageClosedSubgroup
  have hj_apply (z : Variety.Point Z.carrierVariety) :
      j.onPoints z = U.inclusion.onPoints (Z.inclusion.onPoints z) := rfl
  have hCmem (x : Variety.Point G) : x ∈ C.toSubgroup ↔
      x ∈ U.toSubgroup ∧
        ∀ y ∈ U.toSubgroup, x * y = y * x := by
    constructor
    · intro hx
      change x ∈ j.image at hx
      obtain ⟨z, hz⟩ := hx
      have hzZ : Z.inclusion.onPoints z ∈ Z.toSubgroup :=
        (Z.pointEquiv z).property
      have hxU : x ∈ U.toSubgroup := by
        rw [← hz, hj_apply]
        exact (U.pointEquiv (Z.inclusion.onPoints z)).property
      refine ⟨hxU, ?_⟩
      intro y hy
      let yU := U.pointEquiv.symm ⟨y, hy⟩
      have hzy : yU * Z.inclusion.onPoints z = Z.inclusion.onPoints z * yU := by
        exact (Subgroup.mem_centralizer_iff.mp hzZ) yU (by trivial)
      have hzy' := congrArg U.inclusion.onPoints hzy
      rw [map_mul, map_mul] at hzy'
      have hyU : U.inclusion.onPoints yU = y := by
        change (U.pointEquiv yU).val = y
        simp [yU]
      rw [hyU, ← hj_apply, hz] at hzy'
      exact hzy'.symm
    · rintro ⟨hxU, hxcentral⟩
      let xU := U.pointEquiv.symm ⟨x, hxU⟩
      have hxIncl : U.inclusion.onPoints xU = x := by
        change (U.pointEquiv xU).val = x
        simp [xU]
      have hxZ : xU ∈ Z.toSubgroup := by
        change xU ∈ Subgroup.centralizer
          (Set.univ : Set (Variety.Point U.carrierVariety))
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        apply U.inclusion_injective
        rw [map_mul, map_mul, hxIncl]
        exact (hxcentral _ (U.pointEquiv y).property).symm
      let z := Z.pointEquiv.symm ⟨xU, hxZ⟩
      change x ∈ j.image
      refine ⟨z, ?_⟩
      rw [hj_apply]
      change U.inclusion.onPoints (Z.pointEquiv z).val = x
      simp [z, hxIncl]
  have hjinj : Function.Injective j.onPoints :=
    U.inclusion_injective.comp Z.inclusion_injective
  letI : Subsingleton j.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hjinj
    have hx : j.onPoints x.val = 1 := x.property
    have hy : j.onPoints y.val = 1 := y.property
    rw [hx, hy]
  letI : Subsingleton (Variety.Point j.kernelClosedSubgroup.carrierVariety) :=
    j.kernelClosedSubgroup.pointEquiv.subsingleton
  letI : Finite (Variety.Point j.kernelClosedSubgroup.carrierVariety) :=
    Finite.of_subsingleton
  have hjkerDim : Variety.dimension j.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points j.kernelClosedSubgroup.carrierVariety).2
      inferInstance
  have hjdim := morphism_dimension_eq_kernel_add_image j
  rw [hjkerDim, zero_add] at hjdim
  have hZpos : 0 < Variety.dimension Z.carrierVariety := by
    simpa only [Z] using unipotent_positiveCenter_dimension hU hUpos
  have hCpos : 0 < Variety.dimension C.carrierVariety := by
    change 0 < Variety.dimension j.imageClosedSubgroup.carrierVariety
    rw [← hjdim]
    exact hZpos
  have hsC : s ∈ C.normalizer.toSubgroup := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    have hsU := Subgroup.mem_normalizer_iff.mp hs
    constructor
    · intro hx
      obtain ⟨hxU, hxcentral⟩ := (hCmem x).mp hx
      apply (hCmem _).mpr
      refine ⟨(hsU x).mp hxU, ?_⟩
      intro y hy
      have hyback : s⁻¹ * y * s ∈ U.toSubgroup := by
        apply (hsU (s⁻¹ * y * s)).mpr
        simpa [mul_assoc] using hy
      have hc := hxcentral _ hyback
      have hc' := congrArg (fun z ↦ s * z * s⁻¹) hc
      simpa [mul_assoc] using hc'
    · intro hx
      obtain ⟨hxsU, hxscentral⟩ := (hCmem _).mp hx
      apply (hCmem x).mpr
      refine ⟨(hsU x).mpr hxsU, ?_⟩
      intro y hy
      have hyconj : s * y * s⁻¹ ∈ U.toSubgroup := (hsU y).mp hy
      have hc := hxscentral _ hyconj
      have hc' := congrArg (fun z ↦ s⁻¹ * z * s) hc
      simpa [mul_assoc] using hc'
  let N : ClosedSubgroup G := C.identityComponentAmbient
  have hNconnSet : _root_.IsConnected (N : Set (Variety.Point G)) :=
    C.identityComponentAmbient_isConnected
  have hNconn : Variety.IsConnected N.carrierVariety :=
    closedSubgroup_carrier_isConnected N hNconnSet
  have hNC : N ≤ C := C.identityComponentAmbient_le
  have hNU : N ≤ U := by
    intro n hn
    exact (hCmem n).mp (hNC hn) |>.1
  have hNcentral : ∀ n ∈ N.toSubgroup, ∀ u ∈ U.toSubgroup, n * u = u * n := by
    intro n hn
    exact (hCmem n).mp (hNC hn) |>.2
  have hN : IsUnipotentAlgebraicGroup N.carrierVariety := by
    intro n
    let g := N.inclusion.onPoints n
    have hgN : g ∈ N.toSubgroup := (N.pointEquiv n).property
    have hgU : g ∈ U.toSubgroup := hNU hgN
    let u := U.pointEquiv.symm ⟨g, hgU⟩
    have huAmb : IsUnipotentElement G g := by
      have hu := morphism_preserves_unipotentElement U.inclusion u (hU u)
      have huIncl : U.inclusion.onPoints u = g := by
        change (U.pointEquiv u).val = g
        simp [u]
      rwa [huIncl] at hu
    have hn := closedSubgroup_unipotent_of_ambient N hgN huAmb
    have heq : N.pointEquiv.symm ⟨g, hgN⟩ = n := by
      apply N.pointEquiv.injective
      apply Subtype.ext
      rfl
    rwa [heq] at hn
  have hsN : s ∈ N.normalizer.toSubgroup :=
    identityComponentAmbient_mem_normalizer C s hsC
  have hNpos : 0 < Variety.dimension N.carrierVariety := by
    rw [ClosedSubgroup.dimension_identityComponentAmbient]
    exact hCpos
  exact ⟨N, hNconn, hN, hNU, hNcentral, hsN, hNpos⟩

private def semisimpleCommutatorAbelianMorphism
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (hcomm : ∀ x ∈ U.toSubgroup, ∀ y ∈ U.toSubgroup, x * y = y * x) :
    AlgebraicGroup.Morphism U.carrierVariety U.carrierVariety := by
  let f : Variety.Morphism U.carrierVariety G :=
    (AlgebraicGroup.rightMulMorphism G s⁻¹).comp
      ((AlgebraicGroup.conjugateMorphism G s).comp U.inclusion.toVariety)
  have hf_apply (u : Variety.Point U.carrierVariety) :
      f.toFun u = semisimpleCommutator s (U.inclusion.onPoints u) := by
    simp only [f, Variety.Morphism.comp, AlgebraicGroup.rightMulMorphism_apply,
      AlgebraicGroup.conjugateMorphism_apply, semisimpleCommutator]
    rfl
  let fG : AlgebraicGroup.Morphism U.carrierVariety G :=
    { toVariety := f
      map_one := by
        rw [hf_apply, U.inclusion.onPoints.map_one]
        simp [semisimpleCommutator]
      map_mul := by
        intro u v
        rw [hf_apply, hf_apply, hf_apply, U.inclusion.onPoints.map_mul]
        rw [semisimpleCommutator_mul]
        have hu : U.inclusion.onPoints u ∈ U.toSubgroup := (U.pointEquiv u).property
        have hcv : semisimpleCommutator s (U.inclusion.onPoints v) ∈ U.toSubgroup :=
          semisimpleCommutator_mem_of_mem_normalizer U hs
            (U.pointEquiv v).property
        calc
          U.inclusion.onPoints u *
              semisimpleCommutator s (U.inclusion.onPoints v) *
                (U.inclusion.onPoints u)⁻¹ *
                  semisimpleCommutator s (U.inclusion.onPoints u) =
              semisimpleCommutator s (U.inclusion.onPoints v) *
                semisimpleCommutator s (U.inclusion.onPoints u) := by
                  rw [hcomm _ hu _ hcv]
                  group
          _ = semisimpleCommutator s (U.inclusion.onPoints u) *
                semisimpleCommutator s (U.inclusion.onPoints v) :=
              hcomm _
                (semisimpleCommutator_mem_of_mem_normalizer U hs
                  (U.pointEquiv v).property) _
                (semisimpleCommutator_mem_of_mem_normalizer U hs
                  (U.pointEquiv u).property) }
  exact fG.codRestrictClosedSubgroup U fun u ↦ by
    change f.toFun u ∈ U.toSubgroup
    rw [hf_apply]
    exact semisimpleCommutator_mem_of_mem_normalizer U hs
      (U.pointEquiv u).property

omit [IsAlgClosed k] in
private lemma semisimpleCommutatorAbelianMorphism_apply
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (hcomm : ∀ x ∈ U.toSubgroup, ∀ y ∈ U.toSubgroup, x * y = y * x)
    (u : Variety.Point U.carrierVariety) :
    (semisimpleCommutatorAbelianMorphism U s hs hcomm).onPoints u =
      semisimpleCommutatorOn U s hs u := by
  apply U.inclusion_injective
  unfold semisimpleCommutatorAbelianMorphism
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply,
    semisimpleCommutatorOn_inclusion]
  rfl

private theorem semisimpleCommutator_decomposition_of_commute
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (hcomm : ∀ x ∈ U.toSubgroup, ∀ y ∈ U.toSubgroup, x * y = y * x) :
    HasSemisimpleCommutatorPackage U s hs := by
  let c := semisimpleCommutatorAbelianMorphism U s hs hcomm
  let I := c.imageClosedSubgroup
  let K := c.kernelClosedSubgroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  letI : AlgebraicGroup (Variety.prod I.carrierVariety K.carrierVariety) :=
    AlgebraicGroup.prod I.carrierVariety K.carrierVariety
  letI : AlgebraicGroup
      (Variety.prod U.carrierVariety U.carrierVariety) :=
    AlgebraicGroup.prod U.carrierVariety U.carrierVariety
  let left := I.inclusion.comp
    (AlgebraicGroup.Morphism.fst I.carrierVariety K.carrierVariety)
  let right := K.inclusion.comp
    (AlgebraicGroup.Morphism.snd I.carrierVariety K.carrierVariety)
  let pair := AlgebraicGroup.Morphism.prod left right
  have hcommU (x y : Variety.Point U.carrierVariety) : x * y = y * x := by
    apply U.inclusion_injective
    change (U.pointEquiv x).val * (U.pointEquiv y).val =
      (U.pointEquiv y).val * (U.pointEquiv x).val
    exact hcomm _ (U.pointEquiv x).property _ (U.pointEquiv y).property
  let α : AlgebraicGroup.Morphism
      (Variety.prod I.carrierVariety K.carrierVariety) U.carrierVariety :=
    { toVariety := (AlgebraicGroup.mulMorphism U.carrierVariety).comp pair.toVariety
      map_one := by
        change I.inclusion.onPoints
            ((AlgebraicGroup.Morphism.fst I.carrierVariety K.carrierVariety).onPoints 1) *
          K.inclusion.onPoints
            ((AlgebraicGroup.Morphism.snd I.carrierVariety K.carrierVariety).onPoints 1) = 1
        simp
      map_mul := by
        intro x y
        let xi := I.inclusion.onPoints
          ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).1)
        let xk := K.inclusion.onPoints
          ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).2)
        let yi := I.inclusion.onPoints
          ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety y).1)
        let yk := K.inclusion.onPoints
          ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety y).2)
        change (xi * yi) * (xk * yk) = (xi * xk) * (yi * yk)
        calc
          (xi * yi) * (xk * yk) = xi * (yi * xk) * yk := by group
          _ = xi * (xk * yi) * yk := by rw [hcommU yi xk]
          _ = (xi * xk) * (yi * yk) := by group }
  have hα_apply (x : Variety.Point
      (Variety.prod I.carrierVariety K.carrierVariety)) :
      α.onPoints x =
        I.inclusion.onPoints
            ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).1) *
          K.inclusion.onPoints
            ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).2) := by
    simp [α, pair, left, right, AlgebraicGroup.Morphism.onPoints,
      AlgebraicGroup.Morphism.comp, AlgebraicGroup.Morphism.prod,
      AlgebraicGroup.Morphism.fst, AlgebraicGroup.Morphism.snd,
      AlgebraicGroup.mulMorphism, Variety.Morphism.comp, Variety.prodPointEquiv]
  have hαinj : Function.Injective α.onPoints := by
    intro x y hxy
    let xi := I.inclusion.onPoints
      ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).1)
    let xk := K.inclusion.onPoints
      ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).2)
    let yi := I.inclusion.onPoints
      ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety y).1)
    let yk := K.inclusion.onPoints
      ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety y).2)
    have hprod : xi * xk = yi * yk := by simpa [hα_apply] using hxy
    have hcross : yi⁻¹ * xi = yk * xk⁻¹ := by
      calc
        yi⁻¹ * xi = yi⁻¹ * (yi * yk * xk⁻¹) := by rw [← hprod]; group
        _ = yk * xk⁻¹ := by group
    have hcrossImage : yi⁻¹ * xi ∈ semisimpleCommutatorImage U s hs := by
      have hmem : yi⁻¹ * xi ∈ I.toSubgroup :=
        I.toSubgroup.mul_mem
          (I.toSubgroup.inv_mem (I.pointEquiv _).property)
          (I.pointEquiv _).property
      change yi⁻¹ * xi ∈ c.image at hmem
      obtain ⟨w, hw⟩ := hmem
      refine ⟨w, ?_⟩
      rw [← semisimpleCommutatorAbelianMorphism_apply U s hs hcomm]
      exact hw
    have hcrossFixed : yi⁻¹ * xi ∈ semisimpleCommutatorFixedPoints U s hs := by
      change semisimpleCommutatorOn U s hs (yi⁻¹ * xi) = 1
      rw [← semisimpleCommutatorAbelianMorphism_apply U s hs hcomm]
      change c.onPoints (yi⁻¹ * xi) = 1
      rw [hcross, c.onPoints.map_mul, c.onPoints.map_inv]
      have hyker : c.onPoints yk = 1 := (K.pointEquiv _).property
      have hxker : c.onPoints xk = 1 := (K.pointEquiv _).property
      rw [hyker, hxker]
      simp
    have hcrossOne := unipotent_fixed_commutator_eq_one
      U hU s hsSemi hs hcrossImage hcrossFixed
    have hi : xi = yi := by
      have := congrArg (fun z ↦ yi * z) hcrossOne
      simpa [mul_assoc] using this
    have hk : xk = yk := by
      rw [hi] at hprod
      exact mul_left_cancel hprod
    apply (Variety.prodPointEquiv I.carrierVariety K.carrierVariety).injective
    apply Prod.ext
    · exact I.inclusion_injective hi
    · exact K.inclusion_injective hk
  letI : Subsingleton α.kernelClosedSubgroup.toSubgroup := by
    constructor
    intro x y
    apply Subtype.ext
    apply hαinj
    have hx : α.onPoints x.val = 1 := x.property
    have hy : α.onPoints y.val = 1 := y.property
    rw [hx, hy]
  letI : Subsingleton (Variety.Point α.kernelClosedSubgroup.carrierVariety) :=
    α.kernelClosedSubgroup.pointEquiv.subsingleton
  letI : Finite (Variety.Point α.kernelClosedSubgroup.carrierVariety) :=
    Finite.of_subsingleton
  have hαkerDim : Variety.dimension α.kernelClosedSubgroup.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points α.kernelClosedSubgroup.carrierVariety).2
      inferInstance
  have hαdim := morphism_dimension_eq_kernel_add_image α
  rw [hαkerDim, zero_add] at hαdim
  have hcdim := morphism_dimension_eq_kernel_add_image c
  have hαimageDim : Variety.dimension α.imageClosedSubgroup.carrierVariety =
      Variety.dimension U.carrierVariety := by
    rw [← hαdim, dimension_product_additive]
    rw [add_comm]
    exact hcdim.symm
  have hαcontains :=
    (closedSubgroup_dimension_eq_iff_contains_identityComponent
      U.carrierVariety α.imageClosedSubgroup).mp hαimageDim
  have hUidentity : AlgebraicGroup.identityComponent U.carrierVariety = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected U.carrierVariety).mpr hUconn
  have hαsurj : Function.Surjective α.onPoints := by
    intro u
    have hu : u ∈ α.imageClosedSubgroup.toSubgroup := by
      apply hαcontains
      rw [hUidentity]
      trivial
    change u ∈ α.image at hu
    exact hu
  have hdecomp : HasSemisimpleCommutatorDecomposition U s hs := by
    constructor
    · intro u
      obtain ⟨x, hx⟩ := hαsurj u
      let m := I.inclusion.onPoints
        ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).1)
      let z := K.inclusion.onPoints
        ((Variety.prodPointEquiv I.carrierVariety K.carrierVariety x).2)
      refine ⟨m, ?_, z, ?_, ?_⟩
      · have hm : m ∈ I.toSubgroup := (I.pointEquiv _).property
        change m ∈ c.image at hm
        obtain ⟨v, hv⟩ := hm
        exact ⟨v, (semisimpleCommutatorAbelianMorphism_apply
          U s hs hcomm v).symm.trans hv⟩
      · change semisimpleCommutatorOn U s hs z = 1
        rw [← semisimpleCommutatorAbelianMorphism_apply U s hs hcomm]
        exact (K.pointEquiv _).property
      · simpa [m, z, hα_apply] using hx.symm
    · intro m₁ m₂ z₁ z₂ hm₁ hm₂ hz₁ hz₂ heq
      have hcross : m₂⁻¹ * m₁ = z₂ * z₁⁻¹ := by
        calc
          m₂⁻¹ * m₁ = m₂⁻¹ * (m₂ * z₂ * z₁⁻¹) := by rw [← heq]; group
          _ = z₂ * z₁⁻¹ := by group
      have hcrossImage : m₂⁻¹ * m₁ ∈ semisimpleCommutatorImage U s hs := by
        obtain ⟨v₁, rfl⟩ := hm₁
        obtain ⟨v₂, rfl⟩ := hm₂
        rw [← semisimpleCommutatorAbelianMorphism_apply U s hs hcomm,
          ← semisimpleCommutatorAbelianMorphism_apply U s hs hcomm]
        refine ⟨v₂⁻¹ * v₁, ?_⟩
        exact (c.onPoints.map_mul v₂⁻¹ v₁).trans
          (congrArg (fun z ↦ z * c.onPoints v₁) (c.onPoints.map_inv v₂))
      have hcrossFixed : m₂⁻¹ * m₁ ∈ semisimpleCommutatorFixedPoints U s hs := by
        change semisimpleCommutatorOn U s hs (m₂⁻¹ * m₁) = 1
        rw [hcross, ← semisimpleCommutatorAbelianMorphism_apply U s hs hcomm,
          c.onPoints.map_mul, c.onPoints.map_inv]
        change semisimpleCommutatorOn U s hs z₂ = 1 at hz₂
        change semisimpleCommutatorOn U s hs z₁ = 1 at hz₁
        rw [semisimpleCommutatorAbelianMorphism_apply U s hs hcomm,
          semisimpleCommutatorAbelianMorphism_apply U s hs hcomm, hz₁, hz₂]
        simp
      have hone := unipotent_fixed_commutator_eq_one
        U hU s hsSemi hs hcrossImage hcrossFixed
      have hm : m₁ = m₂ := by
        have := congrArg (fun z ↦ m₂ * z) hone
        simpa [mul_assoc] using this
      rw [hm] at heq
      exact ⟨hm, mul_left_cancel heq⟩
  refine ⟨hdecomp, ?_⟩
  · let K0 : ClosedSubgroup K.carrierVariety :=
      AlgebraicGroup.identityComponentClosedSubgroup K.carrierVariety
    letI : AlgebraicGroup K0.carrierVariety := K0.carrierAlgebraicGroup
    letI : AlgebraicGroup
        (Variety.prod I.carrierVariety K0.carrierVariety) :=
      AlgebraicGroup.prod I.carrierVariety K0.carrierVariety
    let β : AlgebraicGroup.Morphism
        (Variety.prod I.carrierVariety K0.carrierVariety)
          (Variety.prod I.carrierVariety K.carrierVariety) :=
      AlgebraicGroup.Morphism.prod
        (AlgebraicGroup.Morphism.fst I.carrierVariety K0.carrierVariety)
        (K0.inclusion.comp
          (AlgebraicGroup.Morphism.snd I.carrierVariety K0.carrierVariety))
    let α0 := α.comp β
    have hβinj : Function.Injective β.onPoints := by
      intro x y hxy
      apply (Variety.prodPointEquiv I.carrierVariety K0.carrierVariety).injective
      apply Prod.ext
      · apply Variety.Point.ext
        have h := congrArg (fun z ↦
          (Variety.prodPointEquiv I.carrierVariety K.carrierVariety z).1) hxy
        simpa [β, AlgebraicGroup.Morphism.prod,
          AlgebraicGroup.Morphism.onPoints, AlgebraicGroup.Morphism.comp,
          AlgebraicGroup.Morphism.fst, AlgebraicGroup.Morphism.snd,
          Variety.Morphism.comp, Variety.prodPointEquiv] using h
      · apply K0.inclusion_injective
        apply Variety.Point.ext
        have h := congrArg (fun z ↦
          (Variety.prodPointEquiv I.carrierVariety K.carrierVariety z).2) hxy
        simpa [β, AlgebraicGroup.Morphism.prod,
          AlgebraicGroup.Morphism.onPoints, AlgebraicGroup.Morphism.comp,
          AlgebraicGroup.Morphism.fst, AlgebraicGroup.Morphism.snd,
          Variety.Morphism.comp, Variety.prodPointEquiv] using h
    have hα0inj : Function.Injective α0.onPoints := by
      intro x y hxy
      apply hβinj
      apply hαinj
      exact hxy
    letI : Subsingleton α0.kernelClosedSubgroup.toSubgroup := by
      constructor
      intro x y
      apply Subtype.ext
      apply hα0inj
      have hx : α0.onPoints x.val = 1 := x.property
      have hy : α0.onPoints y.val = 1 := y.property
      rw [hx, hy]
    letI : Subsingleton (Variety.Point α0.kernelClosedSubgroup.carrierVariety) :=
      α0.kernelClosedSubgroup.pointEquiv.subsingleton
    letI : Finite (Variety.Point α0.kernelClosedSubgroup.carrierVariety) :=
      Finite.of_subsingleton
    have hα0kerDim : Variety.dimension α0.kernelClosedSubgroup.carrierVariety = 0 :=
      (dimension_zero_iff_finite_points α0.kernelClosedSubgroup.carrierVariety).2
        inferInstance
    have hα0dim := morphism_dimension_eq_kernel_add_image α0
    rw [hα0kerDim, zero_add] at hα0dim
    have hα0imageDim : Variety.dimension α0.imageClosedSubgroup.carrierVariety =
        Variety.dimension U.carrierVariety := by
      rw [← hα0dim, dimension_product_additive]
      rw [dimension_identityComponentClosedSubgroup, add_comm]
      exact hcdim.symm
    have hα0contains :=
      (closedSubgroup_dimension_eq_iff_contains_identityComponent
        U.carrierVariety α0.imageClosedSubgroup).mp hα0imageDim
    have hα0surj : Function.Surjective α0.onPoints := by
      intro u
      have hu : u ∈ α0.imageClosedSubgroup.toSubgroup := by
        apply hα0contains
        rw [hUidentity]
        trivial
      change u ∈ α0.image at hu
      exact hu
    have hK0all : ∀ z : Variety.Point K.carrierVariety,
        z ∈ K0.toSubgroup := by
      intro z
      let x : Variety.Point (Variety.prod I.carrierVariety K.carrierVariety) :=
        (Variety.prodPointEquiv I.carrierVariety K.carrierVariety).symm
          (1, z)
      obtain ⟨y, hy⟩ := hα0surj (α.onPoints x)
      have hβ : β.onPoints y = x := by
        apply hαinj
        exact hy
      have hsecond := congrArg (fun w ↦
          (Variety.prodPointEquiv I.carrierVariety K.carrierVariety w).2) hβ
      have hsecond' : K0.inclusion.onPoints
          ((Variety.prodPointEquiv I.carrierVariety K0.carrierVariety y).2) = z := by
        apply Variety.Point.ext
        simpa [β, x, AlgebraicGroup.Morphism.prod,
          AlgebraicGroup.Morphism.onPoints, AlgebraicGroup.Morphism.comp,
          AlgebraicGroup.Morphism.fst, AlgebraicGroup.Morphism.snd,
          Variety.Morphism.comp, Variety.prodPointEquiv] using hsecond
      have hK0mem :
          K0.inclusion.onPoints
              ((Variety.prodPointEquiv I.carrierVariety K0.carrierVariety y).2) ∈
            K0.toSubgroup :=
        (K0.pointEquiv _).property
      rwa [hsecond'] at hK0mem
    have hKconn : Variety.IsConnected K.carrierVariety := by
      apply (identityComponent_eq_univ_iff_isConnected K.carrierVariety).mp
      apply Set.eq_univ_of_univ_subset
      intro z _
      change z ∈ (AlgebraicGroup.identityComponentClosedSubgroup
        K.carrierVariety).toSubgroup
      rw [AlgebraicGroup.identityComponentClosedSubgroup_carrier]
      exact hK0all z
    have hKeq : K = semisimpleCommutatorFixedSubgroup U s := by
      apply SetLike.coe_injective
      ext z
      change c.onPoints z = 1 ↔
        z ∈ semisimpleCommutatorFixedSubgroup U s
      rw [semisimpleCommutatorAbelianMorphism_apply U s hs hcomm,
        ← semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup]
      rfl
    rw [← hKeq]
    exact hKconn

private lemma unipotent_central_fixed_factor_eq_one
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    {a u v : Variety.Point U.carrierVariety}
    (haFixed : a ∈ semisimpleCommutatorFixedPoints U s hs)
    (haCentral : ∀ w : Variety.Point U.carrierVariety, a * w = w * a)
    (heq : semisimpleCommutatorOn U s hs u * a =
      semisimpleCommutatorOn U s hs v) :
    a = 1 := by
  let aG := U.inclusion.onPoints a
  let uG := U.inclusion.onPoints u
  let vG := U.inclusion.onPoints v
  have haUni : IsUnipotentElement G aG :=
    morphism_preserves_unipotentElement U.inclusion a (hU a)
  have has : aG * s = s * aG := by
    apply (semisimpleCommutator_eq_one_iff_commute s aG).mp
    have h := congrArg U.inclusion.onPoints haFixed
    rw [semisimpleCommutatorOn_inclusion, U.inclusion.onPoints.map_one] at h
    exact h
  have hau : aG * uG = uG * aG := by
    have h := congrArg U.inclusion.onPoints (haCentral u)
    simpa only [map_mul] using h
  have hausemi : IsSemisimpleElement G (uG * s * uG⁻¹) := by
    let c : AlgebraicGroup.Morphism G G :=
      { toVariety := AlgebraicGroup.conjugationByMorphism G uG
        map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
        map_mul := by
          intro x y
          simp only [AlgebraicGroup.conjugationByMorphism_apply]
          group }
    have hc := morphism_preserves_semisimpleElement c s hsSemi
    change IsSemisimpleElement G
      ((AlgebraicGroup.conjugationByMorphism G uG).toFun s) at hc
    simpa [AlgebraicGroup.conjugationByMorphism_apply] using hc
  have hvsemi : IsSemisimpleElement G (vG * s * vG⁻¹) := by
    let c : AlgebraicGroup.Morphism G G :=
      { toVariety := AlgebraicGroup.conjugationByMorphism G vG
        map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
        map_mul := by
          intro x y
          simp only [AlgebraicGroup.conjugationByMorphism_apply]
          group }
    have hc := morphism_preserves_semisimpleElement c s hsSemi
    change IsSemisimpleElement G
      ((AlgebraicGroup.conjugationByMorphism G vG).toFun s) at hc
    simpa [AlgebraicGroup.conjugationByMorphism_apply] using hc
  have haCommutesConj : aG * (uG * s * uG⁻¹) =
      (uG * s * uG⁻¹) * aG := by
    have hauInv : aG * uG⁻¹ = uG⁻¹ * aG := by
      have h := congrArg (fun x ↦ uG⁻¹ * x * uG⁻¹) hau
      simpa [mul_assoc] using h.symm
    calc
      aG * (uG * s * uG⁻¹) = (aG * uG) * s * uG⁻¹ := by group
      _ = (uG * aG) * s * uG⁻¹ := by rw [hau]
      _ = uG * (aG * s) * uG⁻¹ := by group
      _ = uG * (s * aG) * uG⁻¹ := by rw [has]
      _ = uG * s * (aG * uG⁻¹) := by group
      _ = uG * s * (uG⁻¹ * aG) := by rw [hauInv]
      _ = (uG * s * uG⁻¹) * aG := by group
  have hprod : (uG * s * uG⁻¹) * aG = vG * s * vG⁻¹ := by
    have heq' := congrArg U.inclusion.onPoints heq
    rw [map_mul, semisimpleCommutatorOn_inclusion,
      semisimpleCommutatorOn_inclusion] at heq'
    change semisimpleCommutator s uG * aG =
      semisimpleCommutator s vG at heq'
    have heq'' := congrArg (fun x ↦ x * s) heq'
    simpa [semisimpleCommutator, has, mul_assoc] using heq''
  let d : JordanDecomposition (vG * s * vG⁻¹) :=
    { semisimplePart := uG * s * uG⁻¹
      unipotentPart := aG
      eq_mul := hprod.symm
      commute := haCommutesConj.symm
      semisimple := hausemi
      unipotent := haUni }
  let trivial : JordanDecomposition (vG * s * vG⁻¹) :=
    { semisimplePart := vG * s * vG⁻¹
      unipotentPart := 1
      eq_mul := by simp
      commute := Commute.one_right _
      semisimple := hvsemi
      unipotent := one_isUnipotentElement G }
  have h := d.unique trivial
  have haOne : aG = 1 := congrArg JordanDecomposition.unipotentPart h
  apply U.inclusion_injective
  exact haOne.trans U.inclusion.onPoints.map_one.symm

private theorem semisimpleCommutator_decomposition
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    HasSemisimpleCommutatorPackage U s hs := by
  induction hdim : Cardinal.toNat (Variety.dimension U.carrierVariety)
      using Nat.strong_induction_on generalizing G U s with
  | h d ih =>
      by_cases hcomm : ∀ x ∈ U.toSubgroup, ∀ y ∈ U.toSubgroup, x * y = y * x
      · exact semisimpleCommutator_decomposition_of_commute
          U hUconn hU s hsSemi hs hcomm
      obtain ⟨N, hNconn, hN, hNU, hNcentral, hsN, hNpos⟩ :=
        exists_normalized_connected_central_subgroup U hUconn hU s hs hcomm
      have hNneq : N ≠ U := by
        intro hEq
        apply hcomm
        intro x hx y hy
        exact hNcentral x (by simpa [hEq] using hx) y hy
      have hNconnSet : _root_.IsConnected (N : Set (Variety.Point G)) :=
        closedSubgroup_isConnected_of_carrier N hNconn
      have hUconnSet : _root_.IsConnected (U : Set (Variety.Point G)) :=
        closedSubgroup_isConnected_of_carrier U hUconn
      have hNdimlt : Variety.dimension N.carrierVariety <
          Variety.dimension U.carrierVariety :=
        connected_closedSubgroup_dimension_lt_of_le_of_ne
          N U hNU hNneq hNconnSet hUconnSet
      have hNnatlt : Cardinal.toNat (Variety.dimension N.carrierVariety) < d := by
        rw [← hdim]
        exact Cardinal.toNat_lt_toNat hNdimlt
          (variety_dimension_lt_aleph0 U.carrierVariety)
      let K : ClosedSubgroup G := N.normalizer
      letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
      have hUK (u : Variety.Point U.carrierVariety) :
          U.inclusion.onPoints u ∈ K.toSubgroup := by
        apply Subgroup.centralizer_le_normalizer (N.toSubgroup : Set (Variety.Point G))
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact hNcentral n hn _ (U.pointEquiv u).property
      let iU : AlgebraicGroup.Morphism U.carrierVariety K.carrierVariety :=
        U.inclusion.codRestrictClosedSubgroup K hUK
      have hiU_apply (u : Variety.Point U.carrierVariety) :
          K.inclusion.onPoints (iU.onPoints u) = U.inclusion.onPoints u := by
        exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
          U.inclusion K hUK u
      let NK : ClosedSubgroup K.carrierVariety :=
        K.inclusion.closedSubgroupPreimage N
      have hNKnormal : NK.toSubgroup.Normal := by
        refine ⟨?_⟩
        intro n hn g
        have hn' : K.inclusion.onPoints n ∈ N.toSubgroup := hn
        have hg' : K.inclusion.onPoints g ∈ N.normalizer.toSubgroup :=
          (K.pointEquiv g).property
        have hconj := (Subgroup.mem_normalizer_iff.mp hg'
          (K.inclusion.onPoints n)).mp hn'
        change K.inclusion.onPoints (g * n * g⁻¹) ∈ N.toSubgroup
        simpa only [map_mul, map_inv] using hconj
      obtain ⟨Q, hQ, q, hqsurj, hqker, _⟩ := theorem_1_1_2_b NK hNKnormal
      letI : AlgebraicGroup Q := hQ
      let sK : Variety.Point K.carrierVariety := K.pointEquiv.symm ⟨s, hsN⟩
      have hsK_apply : K.inclusion.onPoints sK = s := by
        change (K.pointEquiv sK).val = s
        simp [sK]
      have hsKSemi : IsSemisimpleElement K.carrierVariety sK := by
        have := (closedSubgroup_semisimpleElement_iff K hsN).mp hsSemi
        simpa [sK] using this
      let sQ : Variety.Point Q := q.onPoints sK
      have hsQSemi : IsSemisimpleElement Q sQ :=
        morphism_preserves_semisimpleElement q sK hsKSemi
      let fU : AlgebraicGroup.Morphism U.carrierVariety Q := q.comp iU
      let UQ : ClosedSubgroup Q := fU.imageClosedSubgroup
      letI : AlgebraicGroup UQ.carrierVariety := UQ.carrierAlgebraicGroup
      have hfU_mem (u : Variety.Point U.carrierVariety) :
          fU.onPoints u ∈ UQ.toSubgroup := ⟨u, rfl⟩
      let p : AlgebraicGroup.Morphism U.carrierVariety UQ.carrierVariety :=
        fU.codRestrictClosedSubgroup UQ hfU_mem
      have hp_surj : Function.Surjective p.onPoints :=
        fU.codRestrictImageClosedSubgroup_surjective hfU_mem
      have hp_apply (u : Variety.Point U.carrierVariety) :
          UQ.inclusion.onPoints (p.onPoints u) = fU.onPoints u := by
        exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
          fU UQ hfU_mem u
      have hUQconn : Variety.IsConnected UQ.carrierVariety :=
        closedSubgroup_carrier_isConnected UQ
          (fU.imageClosedSubgroup_isConnected hUconn)
      have hUQ : IsUnipotentAlgebraicGroup UQ.carrierVariety :=
        hU.of_surjective p hp_surj
      have hsQ : sQ ∈
          Subgroup.normalizer (UQ.toSubgroup : Set (Variety.Point Q)) := by
        apply Subgroup.mem_normalizer_iff.mpr
        intro x
        constructor
        · intro hx
          change x ∈ fU.image at hx
          obtain ⟨u, rfl⟩ := hx
          have huconj : s * U.inclusion.onPoints u * s⁻¹ ∈ U.toSubgroup :=
            (Subgroup.mem_normalizer_iff.mp hs _).mp (U.pointEquiv u).property
          let u' := U.pointEquiv.symm
            ⟨s * U.inclusion.onPoints u * s⁻¹, huconj⟩
          refine ⟨u', ?_⟩
          change q.onPoints (iU.onPoints u') =
            q.onPoints sK * q.onPoints (iU.onPoints u) * (q.onPoints sK)⁻¹
          rw [← map_mul, ← map_inv, ← map_mul]
          apply congrArg q.onPoints
          apply K.inclusion_injective
          simp only [map_mul, map_inv, hiU_apply, hsK_apply]
          change s * U.inclusion.onPoints u * s⁻¹ = _
          simp
        · intro hx
          change sQ * x * sQ⁻¹ ∈ fU.image at hx
          obtain ⟨u, hu⟩ := hx
          have hu' : fU.onPoints u = sQ * x * sQ⁻¹ := hu
          have hxEq : x = sQ⁻¹ * fU.onPoints u * sQ := by
            rw [hu']
            group
          have huBack : s⁻¹ * U.inclusion.onPoints u * s ∈ U.toSubgroup := by
            apply (Subgroup.mem_normalizer_iff.mp hs _).mpr
            have huMem : U.inclusion.onPoints u ∈ U.toSubgroup :=
              (U.pointEquiv u).property
            convert huMem using 1
            group
          let u' := U.pointEquiv.symm
            ⟨s⁻¹ * U.inclusion.onPoints u * s, huBack⟩
          change x ∈ fU.image
          refine ⟨u', ?_⟩
          rw [hxEq]
          change q.onPoints (iU.onPoints u') =
            (q.onPoints sK)⁻¹ * q.onPoints (iU.onPoints u) * q.onPoints sK
          rw [← map_inv, ← map_mul, ← map_mul]
          apply congrArg q.onPoints
          apply K.inclusion_injective
          simp only [map_mul, map_inv, hiU_apply, hsK_apply]
          change s⁻¹ * U.inclusion.onPoints u * s = _
          simp
      have hfU_one_iff (u : Variety.Point U.carrierVariety) :
          fU.onPoints u = 1 ↔ U.inclusion.onPoints u ∈ N.toSubgroup := by
        change q.onPoints (iU.onPoints u) = 1 ↔ _
        rw [← MonoidHom.mem_ker]
        change iU.onPoints u ∈ q.kernel ↔ _
        rw [hqker]
        change K.inclusion.onPoints (iU.onPoints u) ∈ N.toSubgroup ↔ _
        rw [hiU_apply]
      let nU : AlgebraicGroup.Morphism N.carrierVariety U.carrierVariety :=
        N.inclusion.codRestrictClosedSubgroup U fun n ↦
          hNU (N.pointEquiv n).property
      have hnU_apply (n : Variety.Point N.carrierVariety) :
          U.inclusion.onPoints (nU.onPoints n) = N.inclusion.onPoints n := by
        exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
          N.inclusion U (fun n ↦ hNU (N.pointEquiv n).property) n
      have hnUinj : Function.Injective nU.onPoints := by
        intro x y hxy
        apply N.inclusion_injective
        rw [← hnU_apply, ← hnU_apply, hxy]
      let I : ClosedSubgroup U.carrierVariety := nU.imageClosedSubgroup
      have hIconn : Variety.IsConnected I.carrierVariety :=
        closedSubgroup_carrier_isConnected I
          (nU.imageClosedSubgroup_isConnected hNconn)
      have hIdim : Variety.dimension I.carrierVariety =
          Variety.dimension N.carrierVariety := by
        letI : Subsingleton nU.kernelClosedSubgroup.toSubgroup := by
          constructor
          intro x y
          apply Subtype.ext
          apply hnUinj
          rw [x.property, y.property]
        letI : Subsingleton
            (Variety.Point nU.kernelClosedSubgroup.carrierVariety) :=
          nU.kernelClosedSubgroup.pointEquiv.subsingleton
        letI : Finite (Variety.Point nU.kernelClosedSubgroup.carrierVariety) :=
          Finite.of_subsingleton
        have hker0 : Variety.dimension nU.kernelClosedSubgroup.carrierVariety = 0 :=
          (dimension_zero_iff_finite_points
            nU.kernelClosedSubgroup.carrierVariety).2 inferInstance
        have hdim' := morphism_dimension_eq_kernel_add_image nU
        rw [hker0, zero_add] at hdim'
        exact hdim'.symm
      have hIle : I ≤ fU.kernelClosedSubgroup := by
        intro x hx
        change x ∈ nU.image at hx
        obtain ⟨n, rfl⟩ := hx
        change fU.onPoints (nU.onPoints n) = 1
        rw [hfU_one_iff, hnU_apply]
        exact (N.pointEquiv n).property
      have hkerPos : 0 <
          Variety.dimension fU.kernelClosedSubgroup.carrierVariety := by
        have hIconnSet : _root_.IsConnected
            (I : Set (Variety.Point U.carrierVariety)) :=
          closedSubgroup_isConnected_of_carrier I hIconn
        have hle := connected_closedSubgroup_dimension_le_of_le
          I fU.kernelClosedSubgroup hIconnSet hIle
        rw [hIdim] at hle
        exact hNpos.trans_le hle
      have hUQdimlt : Variety.dimension UQ.carrierVariety <
          Variety.dimension U.carrierVariety := by
        have hformula := morphism_dimension_eq_kernel_add_image fU
        have hnat := congrArg Cardinal.toNat hformula
        rw [Cardinal.toNat_add
          (variety_dimension_lt_aleph0 fU.kernelClosedSubgroup.carrierVariety)
          (variety_dimension_lt_aleph0 fU.imageClosedSubgroup.carrierVariety)] at hnat
        have hkerNatPos : 0 < Cardinal.toNat
            (Variety.dimension fU.kernelClosedSubgroup.carrierVariety) :=
          Cardinal.toNat_pos.mpr ⟨hkerPos.ne',
            variety_dimension_lt_aleph0 fU.kernelClosedSubgroup.carrierVariety⟩
        apply (Cardinal.toNat_lt_iff_lt_of_lt_aleph0
          (variety_dimension_lt_aleph0 UQ.carrierVariety)
          (variety_dimension_lt_aleph0 U.carrierVariety)).mp
        change Cardinal.toNat
            (Variety.dimension fU.imageClosedSubgroup.carrierVariety) < _
        omega
      have hUQnatlt : Cardinal.toNat (Variety.dimension UQ.carrierVariety) < d := by
        rw [← hdim]
        exact Cardinal.toNat_lt_toNat hUQdimlt
          (variety_dimension_lt_aleph0 U.carrierVariety)
      have hNpackage := ih _ hNnatlt N hNconn hN s hsSemi hsN rfl
      have hUQpackage := ih _ hUQnatlt UQ hUQconn hUQ sQ hsQSemi hsQ rfl
      have hNdecomp := hNpackage.1
      have hUQdecomp := hUQpackage.1
      have hp_c (u : Variety.Point U.carrierVariety) :
          p.onPoints (semisimpleCommutatorOn U s hs u) =
            semisimpleCommutatorOn UQ sQ hsQ (p.onPoints u) := by
        apply UQ.inclusion_injective
        rw [hp_apply, semisimpleCommutatorOn_inclusion, hp_apply]
        change q.onPoints (iU.onPoints
            (semisimpleCommutatorOn U s hs u)) =
          semisimpleCommutator (q.onPoints sK)
            (q.onPoints (iU.onPoints u))
        rw [← map_semisimpleCommutator q sK (iU.onPoints u)]
        apply congrArg q.onPoints
        apply K.inclusion_injective
        rw [hiU_apply, semisimpleCommutatorOn_inclusion]
        simp only [semisimpleCommutator, map_mul, map_inv,
          hsK_apply, hiU_apply]
      have hp_image {m : Variety.Point U.carrierVariety}
          (hm : m ∈ semisimpleCommutatorImage U s hs) :
          p.onPoints m ∈ semisimpleCommutatorImage UQ sQ hsQ := by
        obtain ⟨u, rfl⟩ := hm
        exact ⟨p.onPoints u, (hp_c u).symm⟩
      have hp_image_surj {m : Variety.Point UQ.carrierVariety}
          (hm : m ∈ semisimpleCommutatorImage UQ sQ hsQ) :
          ∃ m', m' ∈ semisimpleCommutatorImage U s hs ∧ p.onPoints m' = m := by
        obtain ⟨x, rfl⟩ := hm
        obtain ⟨u, rfl⟩ := hp_surj x
        exact ⟨semisimpleCommutatorOn U s hs u, ⟨u, rfl⟩, hp_c u⟩
      have hp_fixed {z : Variety.Point U.carrierVariety}
          (hz : z ∈ semisimpleCommutatorFixedPoints U s hs) :
          p.onPoints z ∈ semisimpleCommutatorFixedPoints UQ sQ hsQ := by
        change semisimpleCommutatorOn UQ sQ hsQ (p.onPoints z) = 1
        rw [← hp_c, hz, p.onPoints.map_one]
      have hkerCentral {x : Variety.Point U.carrierVariety}
          (hx : p.onPoints x = 1) :
          ∀ y : Variety.Point U.carrierVariety, x * y = y * x := by
        have hfx : fU.onPoints x = 1 := by
          rw [← hp_apply, hx, UQ.inclusion.onPoints.map_one]
        have hxN := (hfU_one_iff x).mp hfx
        intro y
        apply U.inclusion_injective
        rw [map_mul, map_mul]
        exact hNcentral _ hxN _ (U.pointEquiv y).property
      have hnU_c (n : Variety.Point N.carrierVariety) :
          nU.onPoints (semisimpleCommutatorOn N s hsN n) =
            semisimpleCommutatorOn U s hs (nU.onPoints n) := by
        apply U.inclusion_injective
        rw [hnU_apply, semisimpleCommutatorOn_inclusion,
          semisimpleCommutatorOn_inclusion, hnU_apply]
      have hnU_image {m : Variety.Point N.carrierVariety}
          (hm : m ∈ semisimpleCommutatorImage N s hsN) :
          nU.onPoints m ∈ semisimpleCommutatorImage U s hs := by
        obtain ⟨n, rfl⟩ := hm
        exact ⟨nU.onPoints n, hnU_c n⟩
      have hnU_fixed {z : Variety.Point N.carrierVariety}
          (hz : z ∈ semisimpleCommutatorFixedPoints N s hsN) :
          nU.onPoints z ∈ semisimpleCommutatorFixedPoints U s hs := by
        change semisimpleCommutatorOn U s hs (nU.onPoints z) = 1
        rw [← hnU_c, hz, nU.onPoints.map_one]
      have hAlphaInj : ∀ {m₁ m₂ z₁ z₂ : Variety.Point U.carrierVariety},
          m₁ ∈ semisimpleCommutatorImage U s hs →
          m₂ ∈ semisimpleCommutatorImage U s hs →
          z₁ ∈ semisimpleCommutatorFixedPoints U s hs →
          z₂ ∈ semisimpleCommutatorFixedPoints U s hs →
          m₁ * z₁ = m₂ * z₂ → m₁ = m₂ ∧ z₁ = z₂ := by
        intro m₁ m₂ z₁ z₂ hm₁ hm₂ hz₁ hz₂ heq
        have heqQ : p.onPoints m₁ * p.onPoints z₁ =
            p.onPoints m₂ * p.onPoints z₂ := by
          simpa only [map_mul] using congrArg p.onPoints heq
        have hparts := hUQdecomp.2
          (hp_image hm₁) (hp_image hm₂) (hp_fixed hz₁) (hp_fixed hz₂) heqQ
        let a := z₁ * z₂⁻¹
        have haKer : p.onPoints a = 1 := by
          simp only [a, map_mul, map_inv, hparts.2]
          simp
        have haCentral : ∀ w : Variety.Point U.carrierVariety, a * w = w * a :=
          hkerCentral haKer
        have haFixed : a ∈ semisimpleCommutatorFixedPoints U s hs :=
          semisimpleCommutatorFixedPoints_mul U s hs hz₁
            (semisimpleCommutatorFixedPoints_inv U s hs hz₂)
        obtain ⟨u, rfl⟩ := hm₁
        obtain ⟨v, rfl⟩ := hm₂
        have hfactor : semisimpleCommutatorOn U s hs u * a =
            semisimpleCommutatorOn U s hs v := by
          calc
            semisimpleCommutatorOn U s hs u * a =
                (semisimpleCommutatorOn U s hs u * z₁) * z₂⁻¹ := by
              simp [a, mul_assoc]
            _ = (semisimpleCommutatorOn U s hs v * z₂) * z₂⁻¹ := by
              rw [heq]
            _ = semisimpleCommutatorOn U s hs v := by group
        have haOne := unipotent_central_fixed_factor_eq_one
          U hU s hsSemi hs haFixed haCentral hfactor
        have hz : z₁ = z₂ := by
          have := congrArg (fun x ↦ x * z₂) haOne
          simpa [a, mul_assoc] using this
        rw [hz] at heq
        exact ⟨mul_right_cancel heq, hz⟩
      have hp_nU (n : Variety.Point N.carrierVariety) :
          p.onPoints (nU.onPoints n) = 1 := by
        apply UQ.inclusion_injective
        rw [hp_apply, UQ.inclusion.onPoints.map_one, hfU_one_iff, hnU_apply]
        exact (N.pointEquiv n).property
      have hker_lift {x : Variety.Point U.carrierVariety}
          (hxKer : p.onPoints x = 1) :
          ∃ n : Variety.Point N.carrierVariety, nU.onPoints n = x := by
        have hfx : fU.onPoints x = 1 := by
          rw [← hp_apply, hxKer, UQ.inclusion.onPoints.map_one]
        have hxN := (hfU_one_iff x).mp hfx
        let n := N.pointEquiv.symm ⟨U.inclusion.onPoints x, hxN⟩
        refine ⟨n, ?_⟩
        apply U.inclusion_injective
        rw [hnU_apply]
        change (N.pointEquiv n).val = U.inclusion.onPoints x
        simp [n]
      have hImageKer {x : Variety.Point U.carrierVariety}
          (hxImage : x ∈ semisimpleCommutatorImage U s hs)
          (hxKer : p.onPoints x = 1) :
          ∃ n, n ∈ semisimpleCommutatorImage N s hsN ∧
            nU.onPoints n = x := by
        have hfx : fU.onPoints x = 1 := by
          rw [← hp_apply, hxKer, UQ.inclusion.onPoints.map_one]
        have hxN := (hfU_one_iff x).mp hfx
        let n := N.pointEquiv.symm ⟨U.inclusion.onPoints x, hxN⟩
        have hnUeq : nU.onPoints n = x := by
          apply U.inclusion_injective
          rw [hnU_apply]
          change (N.pointEquiv n).val = U.inclusion.onPoints x
          simp [n]
        obtain ⟨m, hm, z, hz, hn⟩ := hNdecomp.1 n
        have hdecomp : x * 1 = nU.onPoints m * nU.onPoints z := by
          rw [mul_one, ← hnUeq, hn, map_mul]
        have hparts := hAlphaInj hxImage (hnU_image hm)
          (semisimpleCommutatorFixedPoints_one U s hs) (hnU_fixed hz) hdecomp
        exact ⟨m, hm, hparts.1.symm⟩
      have hc_central_mul (n x : Variety.Point U.carrierVariety)
          (hnCentral : ∀ w : Variety.Point U.carrierVariety, n * w = w * n) :
          semisimpleCommutatorOn U s hs (n * x) =
            semisimpleCommutatorOn U s hs x *
              semisimpleCommutatorOn U s hs n := by
        rw [semisimpleCommutatorOn_mul]
        rw [hnCentral (semisimpleCommutatorOn U s hs x)]
        group
      have hc_central_inv (n : Variety.Point U.carrierVariety)
          (hnCentral : ∀ w : Variety.Point U.carrierVariety, n * w = w * n) :
          semisimpleCommutatorOn U s hs n⁻¹ =
            (semisimpleCommutatorOn U s hs n)⁻¹ := by
        have hnInvCentral : ∀ w : Variety.Point U.carrierVariety,
            n⁻¹ * w = w * n⁻¹ := by
          intro w
          have h := hnCentral w
          have h' := congrArg (fun x ↦ n⁻¹ * x * n⁻¹) h
          simpa [mul_assoc] using h'.symm
        have h := hc_central_mul n⁻¹ n hnInvCentral
        simp only [inv_mul_cancel] at h
        have hone := semisimpleCommutatorFixedPoints_one U s hs
        change semisimpleCommutatorOn U s hs 1 = 1 at hone
        rw [hone] at h
        have h' := congrArg
          (fun x ↦ (semisimpleCommutatorOn U s hs n)⁻¹ * x) h
        simpa [mul_assoc] using h'.symm
      have hp_fixed_surj {z' : Variety.Point UQ.carrierVariety}
          (hz' : z' ∈ semisimpleCommutatorFixedPoints UQ sQ hsQ) :
          ∃ z, z ∈ semisimpleCommutatorFixedPoints U s hs ∧
            p.onPoints z = z' := by
        obtain ⟨x, rfl⟩ := hp_surj z'
        have hcxKer : p.onPoints (semisimpleCommutatorOn U s hs x) = 1 := by
          rw [hp_c]
          exact hz'
        obtain ⟨m, hm, hmEq⟩ := hImageKer ⟨x, rfl⟩ hcxKer
        obtain ⟨n, hn⟩ := hm
        let a := nU.onPoints n
        have haKer : p.onPoints a = 1 := hp_nU n
        have haCentral : ∀ w : Variety.Point U.carrierVariety, a * w = w * a :=
          hkerCentral haKer
        have hca : semisimpleCommutatorOn U s hs a =
            semisimpleCommutatorOn U s hs x := by
          rw [← hnU_c, hn, hmEq]
        let z := a⁻¹ * x
        refine ⟨z, ?_, ?_⟩
        · change semisimpleCommutatorOn U s hs z = 1
          rw [show z = a⁻¹ * x by rfl,
            hc_central_mul a⁻¹ x]
          · rw [hc_central_inv a haCentral, hca]
            group
          · intro w
            have h := haCentral w
            have h' := congrArg (fun y ↦ a⁻¹ * y * a⁻¹) h
            simpa [mul_assoc] using h'.symm
        · change p.onPoints (a⁻¹ * x) = p.onPoints x
          rw [map_mul, map_inv, haKer]
          simp
      have hdecomp : HasSemisimpleCommutatorDecomposition U s hs := by
        constructor
        · intro u
          obtain ⟨m', hm', z', hz', huQ⟩ := hUQdecomp.1 (p.onPoints u)
          obtain ⟨m, hm, hmMap⟩ := hp_image_surj hm'
          obtain ⟨z, hz, hzMap⟩ := hp_fixed_surj hz'
          let r := (m * z)⁻¹ * u
          have hrKer : p.onPoints r = 1 := by
            change p.onPoints ((m * z)⁻¹ * u) = 1
            rw [map_mul, map_inv, map_mul, hmMap, hzMap, ← huQ]
            group
          obtain ⟨n, hnMap⟩ := hker_lift hrKer
          obtain ⟨mn, hmn, zn, hzn, hn⟩ := hNdecomp.1 n
          have hrDecomp : r = nU.onPoints mn * nU.onPoints zn := by
            rw [← hnMap, hn, map_mul]
          have hmnCentral : ∀ w : Variety.Point U.carrierVariety,
              nU.onPoints mn * w = w * nU.onPoints mn :=
            hkerCentral (hp_nU mn)
          have hznCentral : ∀ w : Variety.Point U.carrierVariety,
              nU.onPoints zn * w = w * nU.onPoints zn :=
            hkerCentral (hp_nU zn)
          have hcombinedImage : m * nU.onPoints mn ∈
              semisimpleCommutatorImage U s hs := by
            obtain ⟨v, rfl⟩ := hm
            obtain ⟨n₀, rfl⟩ := hmn
            refine ⟨nU.onPoints n₀ * v, ?_⟩
            rw [hc_central_mul (nU.onPoints n₀) v
              (hkerCentral (hp_nU n₀))]
            rw [hnU_c]
          have hcombinedFixed : nU.onPoints zn * z ∈
              semisimpleCommutatorFixedPoints U s hs :=
            semisimpleCommutatorFixedPoints_mul U s hs (hnU_fixed hzn) hz
          refine ⟨m * nU.onPoints mn, hcombinedImage,
            nU.onPoints zn * z, hcombinedFixed, ?_⟩
          have huFromR : u = (m * z) * r := by
            change u = (m * z) * ((m * z)⁻¹ * u)
            group
          rw [huFromR, hrDecomp]
          calc
            m * z * (nU.onPoints mn * nU.onPoints zn) =
                m * (z * nU.onPoints mn) * nU.onPoints zn := by group
            _ = m * (nU.onPoints mn * z) * nU.onPoints zn := by
              rw [← hmnCentral z]
            _ = m * nU.onPoints mn * (z * nU.onPoints zn) := by group
            _ = m * nU.onPoints mn * (nU.onPoints zn * z) := by
              rw [← hznCentral z]
        · exact hAlphaInj
      refine ⟨hdecomp, ?_⟩
      let ZU := semisimpleCommutatorFixedSubgroup U s
      let ZQ := semisimpleCommutatorFixedSubgroup UQ sQ
      let ZN := semisimpleCommutatorFixedSubgroup N s
      letI : AlgebraicGroup ZU.carrierVariety := ZU.carrierAlgebraicGroup
      letI : AlgebraicGroup ZQ.carrierVariety := ZQ.carrierAlgebraicGroup
      letI : AlgebraicGroup ZN.carrierVariety := ZN.carrierAlgebraicGroup
      let p0 := p.comp ZU.inclusion
      have hp0_mem (z : Variety.Point ZU.carrierVariety) :
          p0.onPoints z ∈ ZQ.toSubgroup := by
        apply (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
          UQ sQ hsQ _).mp
        apply hp_fixed
        apply (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
          U s hs _).mpr
        exact (ZU.pointEquiv z).property
      let pZ : AlgebraicGroup.Morphism ZU.carrierVariety ZQ.carrierVariety :=
        p0.codRestrictClosedSubgroup ZQ hp0_mem
      have hpZ_apply (z : Variety.Point ZU.carrierVariety) :
          ZQ.inclusion.onPoints (pZ.onPoints z) =
            p.onPoints (ZU.inclusion.onPoints z) := by
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rfl
      have hpZsurj : Function.Surjective pZ.onPoints := by
        intro zQ
        have hzQfixed : ZQ.inclusion.onPoints zQ ∈
            semisimpleCommutatorFixedPoints UQ sQ hsQ :=
          (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
            UQ sQ hsQ _).mpr (ZQ.pointEquiv zQ).property
        obtain ⟨z, hz, hzMap⟩ := hp_fixed_surj hzQfixed
        have hzZU : z ∈ ZU.toSubgroup :=
          (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
            U s hs z).mp hz
        let zU := ZU.pointEquiv.symm ⟨z, hzZU⟩
        refine ⟨zU, ?_⟩
        apply ZQ.inclusion_injective
        rw [hpZ_apply]
        change p.onPoints z = ZQ.inclusion.onPoints zQ
        simpa [zU] using hzMap
      let n0 := nU.comp ZN.inclusion
      have hn0_mem (z : Variety.Point ZN.carrierVariety) :
          n0.onPoints z ∈ ZU.toSubgroup := by
        apply (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
          U s hs _).mp
        apply hnU_fixed
        apply (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
          N s hsN _).mpr
        exact (ZN.pointEquiv z).property
      let nZ : AlgebraicGroup.Morphism ZN.carrierVariety ZU.carrierVariety :=
        n0.codRestrictClosedSubgroup ZU hn0_mem
      have hnZ_apply (z : Variety.Point ZN.carrierVariety) :
          ZU.inclusion.onPoints (nZ.onPoints z) =
            nU.onPoints (ZN.inclusion.onPoints z) := by
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        rfl
      have hnZker (z : Variety.Point ZN.carrierVariety) :
          nZ.onPoints z ∈ pZ.kernelClosedSubgroup.toSubgroup := by
        change pZ.onPoints (nZ.onPoints z) = 1
        apply ZQ.inclusion_injective
        rw [hpZ_apply, ZQ.inclusion.onPoints.map_one, hnZ_apply, hp_nU]
      letI : AlgebraicGroup pZ.kernelClosedSubgroup.carrierVariety :=
        pZ.kernelClosedSubgroup.carrierAlgebraicGroup
      let nK : AlgebraicGroup.Morphism ZN.carrierVariety
          pZ.kernelClosedSubgroup.carrierVariety :=
        nZ.codRestrictClosedSubgroup pZ.kernelClosedSubgroup hnZker
      have hnKsurj : Function.Surjective nK.onPoints := by
        intro x
        let xZ := pZ.kernelClosedSubgroup.inclusion.onPoints x
        have hxKer : pZ.onPoints xZ = 1 :=
          (pZ.kernelClosedSubgroup.pointEquiv x).property
        have hpX : p.onPoints (ZU.inclusion.onPoints xZ) = 1 := by
          rw [← hpZ_apply, hxKer, ZQ.inclusion.onPoints.map_one]
        obtain ⟨n, hn⟩ := hker_lift hpX
        have hxFixed : ZU.inclusion.onPoints xZ ∈
            semisimpleCommutatorFixedPoints U s hs :=
          (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
            U s hs _).mpr (ZU.pointEquiv xZ).property
        have hnFixed : n ∈ semisimpleCommutatorFixedPoints N s hsN := by
          change semisimpleCommutatorOn N s hsN n = 1
          apply hnUinj
          rw [hnU_c, hn, hxFixed, nU.onPoints.map_one]
        have hnZN : n ∈ ZN.toSubgroup :=
          (semisimpleCommutatorFixedPoints_iff_mem_fixedSubgroup
            N s hsN n).mp hnFixed
        let zN := ZN.pointEquiv.symm ⟨n, hnZN⟩
        refine ⟨zN, ?_⟩
        apply pZ.kernelClosedSubgroup.inclusion_injective
        rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
        apply ZU.inclusion_injective
        rw [hnZ_apply]
        change nU.onPoints n = ZU.inclusion.onPoints xZ
        simpa [zN] using hn
      have hkerConn : Variety.IsConnected
          pZ.kernelClosedSubgroup.carrierVariety :=
        connected_of_surjective_morphism nK hNpackage.2 hnKsurj
      exact source_connected_of_surjective_morphism_of_connected_kernel
        pZ hpZsurj hUQpackage.2 hkerConn

/-- Bor1 Proposition 9.3(2): the subgroup of a connected unipotent group fixed
by a normalizing semisimple point is connected.  The subgroup is represented
by the closed equalizer `semisimpleCommutatorFixedSubgroup`, so the conclusion
can be used directly in closed-subgroup induction arguments. -/
public theorem semisimpleCommutatorFixedSubgroup_isConnected
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Variety.IsConnected
      (semisimpleCommutatorFixedSubgroup U s).carrierVariety :=
  (semisimpleCommutator_decomposition U hUconn hU s hsSemi hs).2

/-! The private induction above is exposed only through this point-level
factorization.  Keeping the result at the level of points avoids imposing a
closed-image assertion that is not supplied by Bor1 9.3. -/

public theorem semisimpleCommutator_factorization
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    (∀ u, ∃ m, m ∈ semisimpleCommutatorImage U s hs ∧
      ∃ z, z ∈ semisimpleCommutatorFixedPoints U s hs ∧ u = m * z) ∧
    (∀ {m₁ m₂ z₁ z₂},
      m₁ ∈ semisimpleCommutatorImage U s hs →
      m₂ ∈ semisimpleCommutatorImage U s hs →
      z₁ ∈ semisimpleCommutatorFixedPoints U s hs →
      z₂ ∈ semisimpleCommutatorFixedPoints U s hs →
      m₁ * z₁ = m₂ * z₂ → m₁ = m₂ ∧ z₁ = z₂) := by
  exact (semisimpleCommutator_decomposition U hUconn hU s hsSemi hs).1

/-- Bor1 Proposition 9.3(3), at the level of points: the image of the
semisimple commutator map is invariant under that map. -/
public theorem semisimpleCommutator_image_image_eq
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Set.image (semisimpleCommutatorOn U s hs)
        (semisimpleCommutatorImage U s hs) =
      semisimpleCommutatorImage U s hs := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · rintro _ ⟨u, rfl⟩
    obtain ⟨m, hm, z, hz, hu⟩ :=
      (semisimpleCommutator_decomposition U hUconn hU s hsSemi hs).1.1 u
    refine ⟨m, hm, ?_⟩
    rw [hu, semisimpleCommutatorOn_mul, hz]
    group

/-- The restriction of `c_s` to its point image. -/
@[expose]
public def semisimpleCommutatorImageMap
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (s : Variety.Point G)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    semisimpleCommutatorImage U s hs → semisimpleCommutatorImage U s hs :=
  fun x ↦ ⟨semisimpleCommutatorOn U s hs x.1, ⟨x.1, rfl⟩⟩

/-- The commutator map restricts bijectively to its point image. -/
public theorem semisimpleCommutatorImageMap_bijective
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    Function.Bijective (semisimpleCommutatorImageMap U s hs) := by
  let hdecomp := (semisimpleCommutator_decomposition U hUconn hU s hsSemi hs).1
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hc : semisimpleCommutatorOn U s hs x.1 =
        semisimpleCommutatorOn U s hs y.1 := congrArg Subtype.val hxy
    have hz : y.1⁻¹ * x.1 ∈ semisimpleCommutatorFixedPoints U s hs :=
      (semisimpleCommutatorOn_eq_iff U s hs x.1 y.1).mp hc
    have heq : x.1 * 1 = y.1 * (y.1⁻¹ * x.1) := by group
    exact (hdecomp.2 x.2 y.2
      (semisimpleCommutatorFixedPoints_one U s hs) hz heq).1
  · intro y
    have hy : y.1 ∈ Set.image (semisimpleCommutatorOn U s hs)
        (semisimpleCommutatorImage U s hs) := by
      rw [semisimpleCommutator_image_image_eq U hUconn hU s hsSemi hs]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- The point-image permutation induced by the semisimple commutator map. -/
@[expose]
public noncomputable def semisimpleCommutatorImageEquiv
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hs : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    semisimpleCommutatorImage U s hs ≃ semisimpleCommutatorImage U s hs :=
  Equiv.ofBijective (semisimpleCommutatorImageMap U s hs)
    (semisimpleCommutatorImageMap_bijective U hUconn hU s hsSemi hs)

end Theory.AlgebraicGroup
