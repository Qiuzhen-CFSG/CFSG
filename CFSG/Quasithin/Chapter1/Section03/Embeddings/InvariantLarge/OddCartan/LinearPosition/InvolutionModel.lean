module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Canonical
public import Theory.SpecificGroups.LinearCoefficientEquiv
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.ProjectiveResidual

/-!
# Involution residuals in an ambient PSL₃ model

The `IsPSL` witness may use any finite field of the given prime order.
An actual field isomorphism induces the entrywise special-linear and
projective equivalences. Restricting the resulting group equivalence to
an involution centralizer transports its solvable residual.

For a subgroup D of J and an involution z in D, `involutionResidual D z`
is the ambient image of the residual of the relative centralizer C_D(z).
We identify it with SL₂(q). This does not identify it with the residual
of C_D(Z(S)); the full Sylow-center position is a separate obligation.

Source: Aschbacher–Smith, A.3.21(a), printed p.55, and the proof of 1.3.4,
printed pp.510–511 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

private noncomputable def centralizerEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) : centralizer ({z} : Set G) ≃* centralizer ({e z} : Set H) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

private noncomputable def solvableResidualEquiv {G H : Type*} [Group G] [Finite G] [Group H]
    (e : G ≃* H) : solvableResidual G ≃* solvableResidual H :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_solvableResidual_eq e.toMonoidHom e.surjective))

/-- The involution residual in any actual PSL₃(q) model, with its field witness discharged. -/
theorem isPSL_involution_solvableResidual {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hG : ClassicalGroup.IsPSL G 3 q) (z : G) (hz : orderOf z = 2) :
    Nonempty (solvableResidual (centralizer ({z} : Set G)) ≃* SL(2, ZMod q)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hG
  let _ : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using hF)
  let f : G ≃* PSL(3, ZMod q) := e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)
  exact ⟨(solvableResidualEquiv (centralizerEquiv f z)).trans
    (psl3_involution_solvableResidual_equiv q hq hlarge (f z) ((f.orderOf_eq z).trans hz))⟩

variable {J : Type*} [Group J]

/-- The solvable residual of C_D(z), included into the original ambient group. -/
@[expose] def involutionResidual (D : Subgroup J) (z : J) : Subgroup J :=
  (solvableResidual (D ⊓ centralizer ({z} : Set J) : Subgroup J)).map
    (D ⊓ centralizer ({z} : Set J)).subtype

private noncomputable def relativeCentralizerEquiv (D : Subgroup J) (z : D) :
    (D ⊓ centralizer ({(z : J)} : Set J) : Subgroup J) ≃*
      centralizer ({z} : Set D) where
  toFun x := ⟨⟨x, x.property.1⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
  invFun y := ⟨y, ⟨y.val.property, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.property))⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The relative involution centralizer has residual SL₂(q) in the ambient group. -/
theorem involutionResidual_equiv [Finite J] {D : Subgroup J}
    {q : ℕ} [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hD : ClassicalGroup.IsPSL D 3 q) {z : J} (hzD : z ∈ D) (hz : orderOf z = 2) :
    Nonempty (involutionResidual D z ≃* SL(2, ZMod q)) := by
  let C := D ⊓ centralizer ({z} : Set J)
  let zD : D := ⟨z, hzD⟩
  have hzD2 : orderOf zD = 2 := (orderOf_injective D.subtype D.subtype_injective zD).symm.trans hz
  obtain ⟨e⟩ := isPSL_involution_solvableResidual hq hlarge hD zD hzD2
  exact ⟨((solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
    ((solvableResidualEquiv (relativeCentralizerEquiv D zD)).trans e)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
