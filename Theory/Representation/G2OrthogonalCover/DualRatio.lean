module

public import Theory.Representation.G2OrthogonalCover.Universal
public import Theory.Representation.G2OrthogonalCover.RootGeometry
public import Theory.Representation.BinaryOffender.DualQuotientBound
public import Theory.Representation.BinaryGroupAction
public import Theory.ElementaryAbelian.Quotient

/-!
# Dual bounds for central G₂ natural covers

The long root subgroup of the derived group has binary rank equal to the
field degree. Its moved plane is two-dimensional over the coefficient
field and fixed pointwise by that subgroup. Duality therefore gives a
ratio at most two, and the universal covering map passes the bound to
every binary central cover. This includes the literal derived group G₂(2)′.

Source: Aschbacher–Smith B.5.13 and I.2.3, printed pp.111 and 413.
-/

public section

open Representation Representation.OneCohomology Representation.BinaryOffender
namespace Atlas.G2.Natural.OrthogonalCover
variable (F : Type*) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem longRoot_injective : Function.Injective (longRootHom F) := by
  intro a b h
  exact Multiplicative.toAdd.injective (rootA_injective (congrArg Subtype.val h))

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem longRoot_card : Nat.card (longRoot F) = Nat.card F :=
  Nat.card_congr (MonoidHom.ofInjective (longRoot_injective F)).toEquiv.symm

omit [CharP F 2] in
private theorem longRoot_elementary : IsElementaryTwo (longRoot F) := by
  let : IsElementaryAbelian 2 (Multiplicative F) := BinaryGroupAction.elementary
  refine ⟨?_, IsElementaryAbelian.of_surjective (longRootHom F).rangeRestrict
    (longRootHom F).rangeRestrict_surjective⟩
  intro hb
  have hc := longRoot_card F
  rw [hb, Subgroup.card_bot] at hc
  exact (Finite.one_lt_card (α := F)).ne hc

omit [CharP F 2] in
private theorem longRoot_rank : rank (longRoot F) = Module.finrank (ZMod 2) F := by
  rw [rank, longRoot_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, Nat.log_pow (by decide)]

omit [CharP F 2] in
/-- The literal universal cover has dual quadratic ratio at most two. -/
theorem model_dual_ratio : quadraticRatio (binaryAction F).dual ≤ 2 := by
  let : Module.Free F (singularPlane F) := Module.Free.of_divisionRing (K := F) (V := singularPlane F)
  let A := longRoot F
  have hc : Coinvariants.ker ((binaryAction F).comp A.subtype) =
      (singularPlane F).restrictScalars (ZMod 2) := by
    change Coinvariants.ker (restrictScalars (k := ZMod 2) ((action F).comp A.subtype)) = _
    rw [coinvariants_restrictScalars, longRoot_commutator]
  have hq : Coinvariants.ker ((binaryAction F).comp A.subtype) ≤
      Representation.invariants ((binaryAction F).comp A.subtype) := by
    rw [hc]
    rintro v ⟨w,rfl⟩ ⟨g,⟨a,rfl⟩⟩
    apply sub_eq_zero.mp
    change action F (longRootElement F a.toAdd) (planeLift F w) - planeLift F w = 0
    rw [longRoot_displacement]
    simp [planeLift]
  have hqd := (commutator_le_invariants_iff_dual
    ((binaryAction F).comp A.subtype)).mp hq
  refine (quadraticRatio_le_two_iff _).mpr ⟨A, longRoot_elementary F, ?_, ?_⟩
  · exact fun a ha b hb v =>
      (commutator_le_invariants_iff _).mp hqd ⟨a,ha⟩ ⟨b,hb⟩ v
  · change Module.finrank (ZMod 2) (_ ⧸ _) ≤ _
    change Module.finrank (ZMod 2) (_ ⧸ Representation.invariants (Representation.dual ((binaryAction F).comp A.subtype))) ≤ _
    rw [finrank_dual_quotient_invariants, hc]
    rw [((Submodule.restrictScalarsEquiv (ZMod 2) F (TraceZero F) (singularPlane F)).restrictScalars (ZMod 2)).finrank_eq,
      ← Module.finrank_mul_finrank (ZMod 2) F (singularPlane F), singularPlane_finrank]
    rw [show rank A = Module.finrank (ZMod 2) F from longRoot_rank F]
    omega

/-- Every binary central cover retains the same dual bound. -/
theorem cover_dual_quadraticRatio_le_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (commutator (Model F)) W}
    (p : σ.IntertwiningMap (binaryNatural F)) (hp : IsCover p) :
    quadraticRatio σ.dual ≤ 2 := by
  obtain ⟨f,hf,_⟩ := exists_quotient F p hp
  exact dual_quadraticRatio_le_two_of_surjective f hf (model_dual_ratio F)
end Atlas.G2.Natural.OrthogonalCover
