module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.BinaryOffender.SubspaceAction
public import CFSG.Quasithin.ChapterH.Section13To16.Defs
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary

/-!
# The conditional local geometry of a genuine `3.M₂₂`

This file records the H.12.1 local argument at its actual induction boundary.
The component is a quasisimple group with centre of order three and an actual
central quotient `M₂₂`; the split carrier `M22CoverModel 3` never occurs.  The
representation, its compatible six-dimensional Hermitian realization, and the
native local calculations are inputs to this helper.  This is the source
correct boundary: those calculations are supplied by the recognition and
native-H.14 owners, while the consequences below are proved here.

The numerical part is deliberately proved from displacement and rank bounds.
In particular, the exclusion of an `(F - 1)` offender does not appear as a
field of the result.  The local geometry record keeps relative subgroups and
intrinsic two-cores explicit, so a later assembly can lift the native catalogue
through the odd central quotient without identifying a cover with a split one.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.12.1(1)--(13), printed pp.393--394 (PDF pp.404--405).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterH.Section10To12

open Subgroup Theory.GroupTheory
open Representation.BinaryOffender
open Sporadic.Mathieu
open CFSG.Quasithin.ChapterH.Section13To16

/-! ## The actual Hermitian input -/

/- The form is the concrete nondegenerate form over `GF(4)` used by the
source.  A compatibility proposition is retained as a premise because it is
the representation-recognition task, not a consequence of quasisimplicity. -/
structure HermitianRestrictionInput (L : Type*) [Group L] where
  action : L →* Theory.SpecificGroups.U6Two.form.specialSubgroup
  faithful : Function.Injective action
  compatible : Prop

theorem hermitianRestriction_field_card :
    Nat.card Theory.SpecificGroups.U6Two.Field = 4 :=
  Theory.SpecificGroups.U6Two.field_card

/-! ## Representation and displacement inputs -/

structure TripleModuleInput (G : Type*) [Group G] [Finite G]
    (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] where
  component : Subgroup G
  triple : IsTripleM22 component
  representation : Representation (ZMod 2) G V
  faithful : Function.Injective representation
  irreducible : Representation.IsIrreducible representation
  dimension : Module.finrank (ZMod 2) V = 12
  hermitian : HermitianRestrictionInput component
  /-- The noncentral cubic displacement in the component. -/
  cubic_displacement :
    ∀ x : component, orderOf x = 3 →
      x ∉ (center component : Set component) →
      fixedCodim (representation.comp component.subtype)
        (Subgroup.zpowers x) = 8
  /-- The involution displacement used in the offender argument. -/
  involution_displacement :
    ∀ t : G, orderOf t = 2 →
      4 ≤ fixedCodim representation (Subgroup.zpowers t)

namespace TripleModuleInput

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

abbrev L (d : TripleModuleInput G V) := d.component
abbrev ρ (d : TripleModuleInput G V) := d.representation
abbrev ρL (d : TripleModuleInput G V) :
    Representation (ZMod 2) d.component V :=
  d.representation.comp d.component.subtype

end TripleModuleInput

/-! ## The two genuine maximal overgroups -/

structure SylowOvergroups {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (d : TripleModuleInput G V) where
  T : Sylow 2 d.component
  M : Subgroup (d.component)
  N : Subgroup (d.component)
  sylow_le_M : (T : Subgroup (d.component)) ≤ M
  sylow_le_N : (T : Subgroup (d.component)) ≤ N
  maximal_M : IsCoatom M
  maximal_N : IsCoatom N
  /-- The actual `A₆` quotient of `M/O₂(M)`. -/
  M_quotient : Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 6))
  /-- The actual `S₅ × 3` quotient of `N/O₂(N)`. -/
  N_quotient :
    Nonempty ((N ⧸ pCore 2 N) ≃* (Equiv.Perm (Fin 5) × Multiplicative (ZMod 3)))
  generated : M ⊔ N = ⊤

namespace SylowOvergroups

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {d : TripleModuleInput G V}

abbrev QM (s : SylowOvergroups d) : Subgroup d.component :=
  (pCore 2 s.M).map s.M.subtype
abbrev QN (s : SylowOvergroups d) : Subgroup d.component :=
  (pCore 2 s.N).map s.N.subtype

theorem sylow_le_twoCores (s : SylowOvergroups d) :
    (s.T : Subgroup d.component) ≤ s.M ∧
      (s.T : Subgroup d.component) ≤ s.N :=
  ⟨s.sylow_le_M, s.sylow_le_N⟩

end SylowOvergroups

/-! ## The source clauses that use the Hermitian geometry -/

structure LocalGeometry {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (d : TripleModuleInput G V) (s : SylowOvergroups d) where
  /-- The binary subspaces underlying the two isotropic `F₄`-points. -/
  V1 : Submodule (ZMod 2) V
  V2 : Submodule (ZMod 2) V
  f4Dimension : Submodule (ZMod 2) V → ℕ
  isotropic : Submodule (ZMod 2) V → Prop
  V1_isotropic : isotropic V1
  V2_isotropic : isotropic V2
  V1_dimension : f4Dimension V1 = 1
  V2_dimension : f4Dimension V2 = 1
  distinct : V1 ≠ V2
  /-- `T` fixes one and only one isotropic `F₄`-point. -/
  sylow_unique_isotropic :
    ∀ W : Submodule (ZMod 2) V, isotropic W → f4Dimension W = 1 →
      (s.T : Subgroup d.component) ≤
        subspaceStabilizer (TripleModuleInput.ρL d) W → W = V1
  N_is_stabilizer :
    s.N = subspaceStabilizer (TripleModuleInput.ρL d) V1
  VM : Submodule (ZMod 2) V
  VM_eq_fixed :
    VM = fixedSpace (TripleModuleInput.ρL d) (SylowOvergroups.QM s)
  VM_eq_commutator :
    VM = subspaceCommutator (TripleModuleInput.ρL d) ⊤ (SylowOvergroups.QM s)
  VM_isotropic : isotropic VM
  VM_dimension : f4Dimension VM = 3
  QM_eq_pointwise_centralizer :
    SylowOvergroups.QM s =
      subspaceKernel (TripleModuleInput.ρL d) VM ⊤
  /-- The two `M`-orbits on the isotropic points in `VM`. -/
  same_M_orbit : Submodule (ZMod 2) V → Submodule (ZMod 2) V → Prop
  M_orbits_in_VM :
    ∀ W : Submodule (ZMod 2) V, isotropic W → W ≤ VM →
      same_M_orbit W V1 ∨ same_M_orbit W V2
  M_orbit_separation : ¬ same_M_orbit V1 V2
  V1_V2_sum_dimension : f4Dimension (V1 ⊔ V2) = 2
  /-- The second point has the native `A₅ × 3` stabilizer. -/
  V2_stabilizer_le_M :
    subspaceStabilizer (TripleModuleInput.ρL d) V2 ≤ s.M
  V2_stabilizer_quotient :
    Nonempty ((subspaceStabilizer (TripleModuleInput.ρL d) V2 ⧸
      pCore 2 (subspaceStabilizer (TripleModuleInput.ρL d) V2)) ≃*
      (alternatingGroup (Fin 5) × Multiplicative (ZMod 3)))
  /-- The two representatives are also the two `L`-orbits. -/
  same_L_orbit : Submodule (ZMod 2) V → Submodule (ZMod 2) V → Prop
  L_orbits :
    ∀ W : Submodule (ZMod 2) V, isotropic W →
      same_L_orbit W V1 ∨ same_L_orbit W V2
  L_orbit_separation : ¬ same_L_orbit V1 V2
  /-- An involution in `Q_M` moves exactly the two distinguished points. -/
  t : s.M
  t_in_QM : (t : d.component) ∈ SylowOvergroups.QM s
  t_involution : orderOf (t : d.component) = 2
  t_displacement :
    subspaceCommutator (TripleModuleInput.ρL d) ⊤
        (Subgroup.zpowers (t : d.component)) = V1 ⊔ V2

/-! ## The ambient clauses and rank transfer -/

structure AmbientGeometry {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (d : TripleModuleInput G V) (s : SylowOvergroups d)
    (g : LocalGeometry d s) where
  TG : Sylow 2 G
  T_le_TG :
    (s.T : Subgroup d.component).map d.component.subtype ≤
      (TG : Subgroup G)
  fixedTG : Submodule (ZMod 2) V
  fixedTG_on_V1 : Submodule (ZMod 2) V
  fixed_line : fixedTG = fixedTG_on_V1
  fixed_line_dimension : Module.finrank (ZMod 2) fixedTG = 1
  /-- The exact displacement-four witness for H.12.1(10). -/
  displacement_four :
    ∃ t : G, orderOf t = 2 ∧
      fixedCodim d.representation (Subgroup.zpowers t) = 4

/-! ## Rank transfer through the actual automorphism action -/

structure RankTransferInput {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (d : TripleModuleInput G V) where
  /-- The ambient action on the actual component, not on a split model. -/
  actor : G →* MulAut d.component
  actor_injective_on_elementary :
    ∀ A : Subgroup G, IsElementaryTwo A →
      Function.Injective (actor.comp A.subtype)
  m22_two_rank : primeRank 2 Sporadic.Mathieu.M22 ≤ 4
  aut_m22_two_rank : primeRank 2 (MulAut Sporadic.Mathieu.M22) ≤ 5

namespace RankTransferInput

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {d : TripleModuleInput G V}

/-- A genuine triple cover inherits the automorphism rank of its quotient. -/
theorem component_aut_rank_le (r : RankTransferInput d) :
    primeRank 2 (MulAut d.component) ≤ 5 := by
  let hperfect : Group.IsPerfect d.component := d.triple.quasisimple.toIsPerfect
  obtain ⟨e⟩ := d.triple.centralQuotient
  let f : PerfectCentralCovering.Cover d.component Sporadic.Mathieu.M22 := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center d.component))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := hperfect
    ker_le_center := by
      intro x hx
      have hx' : e (QuotientGroup.mk' (center d.component) x) = 1 :=
        (MonoidHom.mem_ker.mp hx)
      have hx'' : e (QuotientGroup.mk' (center d.component) x) = e 1 := by
        simpa using hx'
      exact (QuotientGroup.eq_one_iff x).mp (e.injective hx'') }
  have hk : f.toMonoidHom.ker = center d.component := by
    ext x
    change e (QuotientGroup.mk' (center d.component) x) = 1 ↔ _
    constructor
    · intro hx
      have hx' : e (QuotientGroup.mk' (center d.component) x) = e 1 := by
        simpa using hx
      exact (QuotientGroup.eq_one_iff x).mp (e.injective hx')
    · intro hx
      have hx' : QuotientGroup.mk' (center d.component) x = 1 :=
        (QuotientGroup.eq_one_iff x).2 hx
      rw [hx', map_one]
  exact (f.automorphism_primeRank_le hk 2).trans r.aut_m22_two_rank

/-- Every elementary abelian actor has binary rank at most five. -/
theorem rank_le_five (r : RankTransferInput d)
    (A : Subgroup G) (hA : IsElementaryTwo A) : Group.rank A ≤ 5 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let _ : IsMulCommutative A := hA.2.toIsMulCommutative
  let B := A.map r.actor
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map r.actor
  let _ : IsMulCommutative B := inferInstance
  have hrestr : Function.Injective (r.actor.subgroupMap A) := by
    intro x y hxy
    apply r.actor_injective_on_elementary A hA
    exact congrArg (fun z : B => (z : MulAut d.component)) hxy
  have hAB : Group.rank A = Group.rank B :=
    Group.rank_congr
      (MulEquiv.ofBijective (r.actor.subgroupMap A)
        ⟨hrestr, r.actor.subgroupMap_surjective A⟩)
  have hB : Group.rank B ≤ primeRank 2 (MulAut d.component) :=
    Subgroup.rank_le_primeRank 2 B (IsElementaryAbelian.isPGroup 2 B)
  rw [hAB]
  exact hB.trans (r.component_aut_rank_le)

/-- The offender rank is the binary logarithmic rank used in H.12.1. -/
theorem binary_rank_le_five (r : RankTransferInput d)
    (A : Subgroup G) (hA : IsElementaryTwo A) : rank A ≤ 5 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let _ : IsMulCommutative A := hA.2.toIsMulCommutative
  let B := A.map r.actor
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map r.actor
  let _ : IsMulCommutative B := inferInstance
  have hrestr : Function.Injective (r.actor.subgroupMap A) := by
    intro x y hxy
    apply r.actor_injective_on_elementary A hA
    exact congrArg (fun z : B => (z : MulAut d.component)) hxy
  let e : A ≃* B :=
    MulEquiv.ofBijective (r.actor.subgroupMap A)
      ⟨hrestr, r.actor.subgroupMap_surjective A⟩
  have hcardB : Nat.card B ≤ 2 ^ 5 :=
    (primeRank_le_iff_elementary_card_le (MulAut d.component)).mp
      r.component_aut_rank_le B inferInstance
  have hcard : Nat.card A ≤ 2 ^ 5 := by
    calc
      Nat.card A = Nat.card B := Nat.card_congr e.toEquiv
      _ ≤ 2 ^ 5 := hcardB
  have hlog : Nat.log 2 (Nat.card A) < 6 := by
    apply Nat.log_lt_of_lt_pow (Nat.ne_of_gt (Nat.card_pos))
    exact hcard.trans_lt (by norm_num)
  simpa [Representation.BinaryOffender.rank] using (show Nat.log 2 (Nat.card A) ≤ 5 by omega)

/-- The same transfer gives the ambient prime-rank formulation of H.12.1(13). -/
theorem ambient_primeRank_le_five (r : RankTransferInput d) :
    primeRank 2 G ≤ 5 := by
  apply (primeRank_le_iff_elementary_card_le G).2
  intro A hA
  let _ : IsElementaryAbelian 2 A := hA
  let _ : IsMulCommutative A := inferInstance
  let B := A.map r.actor
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map r.actor
  let _ : IsMulCommutative B := inferInstance
  have hinj : Function.Injective (r.actor.comp A.subtype) := by
    by_cases hbot : A = ⊥
    · subst A
      intro x y _
      exact Subsingleton.elim _ _
    · exact r.actor_injective_on_elementary A ⟨hbot, hA⟩
  have hrestr : Function.Injective (r.actor.subgroupMap A) := by
    intro x y hxy
    apply hinj
    exact congrArg (fun z : B => (z : MulAut d.component)) hxy
  let e : A ≃* B :=
    MulEquiv.ofBijective (r.actor.subgroupMap A)
      ⟨hrestr, r.actor.subgroupMap_surjective A⟩
  calc
    Nat.card A = Nat.card B := Nat.card_congr e.toEquiv
    _ ≤ 2 ^ 5 :=
      (primeRank_le_iff_elementary_card_le (MulAut d.component)).mp
        r.component_aut_rank_le B inferInstance

end RankTransferInput

/-! ## The proved numerical offender elimination -/

theorem no_fMinusOne_offender_of_displacement
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (d : TripleModuleInput G V)
    (r : RankTransferInput d)
    (hdisp : ∀ A : Subgroup G, IsElementaryTwo A → 3 ≤ rank A →
      8 ≤ fixedCodim d.representation A) :
    ∀ A : Subgroup G, ¬ IsFMinusOneOffender d.representation A := by
  intro A hAoff
  rcases hAoff with ⟨hA, hoff⟩
  have hrank : rank A ≤ 5 := r.binary_rank_le_five A hA
  let _ : IsElementaryAbelian 2 A := hA.2
  by_cases hsmall : rank A ≤ 2
  · have hnontriv : A ≠ ⊥ := hA.1
    have hfour : 4 ≤ fixedCodim d.representation A := by
      obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hnontriv
      have ha2 : orderOf a = 2 :=
        orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
      have hle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
      have hcod := d.involution_displacement (a : G) ha2
      have hmono := CFSG.Quasithin.ChapterE.fixedCodim_mono d.representation hle
      exact hcod.trans hmono
    omega
  · have hlarge : 3 ≤ rank A := by omega
    have height := hdisp A hA hlarge
    omega

/-! ## The source-level package consumed by H.12's parent -/

structure TripleLocalGeometryConclusion {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (d : TripleModuleInput G V) (s : SylowOvergroups d)
    (g : LocalGeometry d s) (a : AmbientGeometry d s g)
    (r : RankTransferInput d) where
  /-- Clauses (4)--(8), with the actual local quotient structures. -/
  local_geometry : LocalGeometry d s
  /-- Clause (9). -/
  outer_fixed_line : a.fixedTG = a.fixedTG_on_V1 ∧
    Module.finrank (ZMod 2) a.fixedTG = 1
  /-- The displacement-four witness used for clause (10). -/
  displacement_four : ∃ t : G, orderOf t = 2 ∧
    fixedCodim d.representation (Subgroup.zpowers t) = 4
  /-- Clause (12), after the native displacement case split. -/
  no_offender : ∀ A : Subgroup G, ¬ IsFMinusOneOffender d.representation A
  /-- Clause (13). -/
  rank_transfer : ∀ A : Subgroup G, IsElementaryTwo A → rank A ≤ 5
  prime_rank_transfer : primeRank 2 G ≤ 5

noncomputable def assembleTripleLocalGeometry
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (d : TripleModuleInput G V) (s : SylowOvergroups d)
    (g : LocalGeometry d s) (a : AmbientGeometry d s g)
    (r : RankTransferInput d)
    (hdisp : ∀ A : Subgroup G, IsElementaryTwo A → 3 ≤ rank A →
      8 ≤ fixedCodim d.representation A) :
    TripleLocalGeometryConclusion d s g a r := by
  refine {
    local_geometry := g
    outer_fixed_line := ⟨a.fixed_line, a.fixed_line_dimension⟩
    displacement_four := a.displacement_four
    no_offender := no_fMinusOne_offender_of_displacement d r hdisp
    rank_transfer := fun A hA => r.binary_rank_le_five A hA
    prime_rank_transfer := r.ambient_primeRank_le_five }

end CFSG.Quasithin.ChapterH.Section10To12

end
