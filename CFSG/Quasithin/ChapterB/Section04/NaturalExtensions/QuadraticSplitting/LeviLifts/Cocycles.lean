module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Coordinates
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

/-!
# The displacement-cocycle and averaging arguments for B.4.9(1)

A vector fixed modulo the original natural submodule defines its displacement
cocycle on the literal Levi. A principal cocycle corrects that vector to a
fixed lift without changing its image under the original quotient map.
Alternatively a seed fixed by a subgroup of odd index is averaged over cosets.

For a binary SL_r Levi with r ≥ 3, its natural-plus-trivial module has no
nonprincipal cocycle vanishing on an elementary transvection. Perfectness kills
the trivial component. In dimension three the explicit exceptional cocycle has
a nonzero spare coordinate at every transvection; in higher dimension H¹
vanishes. Thus this calculation includes every binary n ≥ 4 in B.4.9.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(1), printed p.93, and I.1.6, printed p.408.
-/

@[expose] public section
open Representation Representation.BinaryOffender Representation.OneCohomology
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N : Subrepresentation ρ) (K : Subgroup G)

/-- Displacement of a lift whose image under the original quotient map is K-fixed. -/
def relativeCocycle (v : V)
    (hv : N.toSubmodule.mkQ v ∈ fixedSpace N.quotientRepresentation K) :
    cocycles (N.toRepresentation.comp K.subtype) :=
  ⟨fun g => ⟨ρ g v - v, by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change N.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hv g)⟩, by
    intro g h
    apply Subtype.ext
    change ρ (g.val * h.val) v - v = ρ g (ρ h v - v) + (ρ g v - v)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel⟩

/-- Subtract the principal vector to obtain a fixed lift with the same quotient image. -/
theorem lift_of_principal (v : V)
    (hv : N.toSubmodule.mkQ v ∈ fixedSpace N.quotientRepresentation K)
    (u : N.toSubmodule)
    (hu : principal (N.toRepresentation.comp K.subtype) u = relativeCocycle ρ N K v hv) :
    ∃ w : V, w ∈ fixedSpace ρ K ∧ N.toSubmodule.mkQ w = N.toSubmodule.mkQ v := by
  refine ⟨v - u, ?_, ?_⟩
  · intro g
    have he := congrArg (fun f : cocycles (N.toRepresentation.comp K.subtype) =>
      (f.val g : V)) hu
    change ρ g u - u = ρ g v - v at he
    change ρ g (v - u) = v - u
    rw [map_sub]
    calc
      ρ g v - ρ g u = (ρ g v - v) - (ρ g u - u) + (v - u) := by abel
      _ = v - u := by rw [← he]; abel
  · have hz : N.toSubmodule.mkQ (u : V) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr u.property
    rw [map_sub, hz, sub_zero]

/-- Sum the translates of a P-fixed lift over K/P; odd index preserves its quotient image. -/
theorem lift_of_odd_index (P : Subgroup K) (hindex : Odd P.index) (v : V)
    (hv : N.toSubmodule.mkQ v ∈ fixedSpace N.quotientRepresentation K)
    (hP : ∀ p : P, ρ p.val.val v = v) :
    ∃ w : V, w ∈ fixedSpace ρ K ∧ N.toSubmodule.mkQ w = N.toSubmodule.mkQ v := by
  classical
  let : P.FiniteIndex := ⟨by obtain ⟨r, hr⟩ := hindex; omega⟩
  let := Fintype.ofFinite (K ⧸ P)
  let f : K ⧸ P → V := fun q => ρ q.out.val v
  have hf (g : K) : f (QuotientGroup.mk g) = ρ g.val v := by
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul P g
    change ρ (QuotientGroup.mk g : K ⧸ P).out.val v = _
    rw [hb]
    change ρ (g.val * b.val.val) v = _
    rw [map_mul, Module.End.mul_apply, hP b]
  have hcov (g : K) (q : K ⧸ P) : f (g • q) = ρ g.val (f q) := by
    induction q using Quotient.inductionOn with
    | h a =>
      change f (QuotientGroup.mk (g * a)) = _
      rw [hf, hf]
      exact LinearMap.congr_fun (ρ.map_mul g.val a.val) v
  refine ⟨∑ q, f q, ?_, ?_⟩
  · intro g
    change ρ g.val (∑ q, f q) = ∑ q, f q
    rw [map_sum]
    simp_rw [← hcov]
    exact Equiv.sum_comp (MulAction.toPerm g) f
  · have hodd : (Fintype.card (K ⧸ P) : ZMod 2) = 1 := by
      have hc : Odd (Fintype.card (K ⧸ P)) := by
        simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hindex
      obtain ⟨r, hr⟩ := hc
      rw [hr]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    rw [map_sum]
    have he (q : K ⧸ P) : N.toSubmodule.mkQ (f q) = N.toSubmodule.mkQ v := hv q.out
    simp_rw [he]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod 2),
      hodd, one_smul]

/-- The actual binary Levi module: one trivial coordinate plus the natural r-space. -/
noncomputable def binaryModel (r : ℕ) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin r) (ZMod 2))
      (ZMod 2 × (Fin r → ZMod 2)) :=
  (Representation.trivial (ZMod 2) _ (ZMod 2)).prod (specialLinearNatural r)

/-- A cocycle vanishing on an elementary transvection is principal, including r = 3. -/
theorem binaryModel_principal {r : ℕ} (hr : 3 ≤ r)
    (f : cocycles (binaryModel r)) {a b : Fin r} (hab : a ≠ b)
    (hf : f.val (transvection hab 1) = 0) :
    ∃ u, principal (binaryModel r) u = f := by
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup r) := BinaryLinear.linearGroup_isPerfect r hr
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin r) (ZMod 2)) :=
    Group.IsPerfect.ofSurjective
      (f := (BinaryLinear.OuterCyclic.slEquivLinear r).symm.toMonoidHom)
      (BinaryLinear.OuterCyclic.slEquivLinear r).symm.surjective
  let q : Matrix.SpecialLinearGroup (Fin r) (ZMod 2) →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (f.val g).1
      map_one' := by
        have he := congrArg Prod.fst (f.property 1 1)
        change (f.val 1).1 = (0 : ZMod 2)
        simpa [binaryModel] using he.symm
      map_mul' := by
        intro g h
        have he := congrArg Prod.fst (f.property g h)
        change (f.val (g*h)).1 = (f.val g).1 + (f.val h).1
        simpa [binaryModel, add_comm] using he }
  have hz (g : Matrix.SpecialLinearGroup (Fin r) (ZMod 2)) : (f.val g).1 = 0 := by
    let : Group.IsPerfect q.range := Group.IsPerfect.range q
    have he := Subsingleton.elim (⟨q g, ⟨g,rfl⟩⟩ : q.range) 1
    exact congrArg (fun x : q.range => Multiplicative.toAdd x.val) he
  let c : cocycles (specialLinearNatural (k := ZMod 2) r) :=
    ⟨fun g => (f.val g).2, fun g h => congrArg Prod.snd (f.property g h)⟩
  have hc : ∃ u, principal (specialLinearNatural (k := ZMod 2) r) u = c := by
    by_cases hr3 : r = 3
    · subst r
      obtain ⟨k, hka, hkb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by decide)
      obtain ⟨x, u, hu⟩ := SLHigherNatural.SLThreeBinary.normal_form c
      have he := congrArg (fun z : cocycles (specialLinearNatural (k := ZMod 2) 3) =>
        z.val (transvection hab 1) k) hu
      have hzero : c.val (transvection hab 1) k = 0 :=
        congrArg (fun z : ZMod 2 × (Fin 3 → ZMod 2) => z.2 k) hf
      change c.val (transvection hab 1) k =
        x * SLHigherNatural.SLThreeBinary.exceptional.val (transvection hab 1) k +
          (principal (specialLinearNatural 3) u).val (transvection hab 1) k at he
      rw [hzero, SLHigherNatural.SLThreeBinary.exceptional_spare a b k hab hka.symm hkb.symm,
        SLHigherNatural.principal_transvection] at he
      have hx : x = 0 := by simpa [Pi.single_eq_of_ne hka] using he.symm
      exact ⟨u, by simpa [hx] using hu.symm⟩
    · obtain ⟨u, hu⟩ := SLHigherNatural.exists_principal_of_four_le (by omega) c
      exact ⟨u, hu.symm⟩
  obtain ⟨u, hu⟩ := hc
  refine ⟨(0,u), ?_⟩
  apply Subtype.ext
  funext g
  apply Prod.ext
  · change (0 : ZMod 2) - 0 = (f.val g).1
    simp [hz]
  · exact congrArg (fun z : cocycles (specialLinearNatural (k := ZMod 2) r) => z.val g) hu

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
