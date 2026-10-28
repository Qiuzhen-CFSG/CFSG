module

public import Theory.Representation.HexacodeAction.FullWeightVectorQuotient
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# The commutant of the actual full-weight vector stabilizer

The fixed space is the field line through the vector. A commuting binary
endomorphism therefore descends to the natural quotient, where the SL₂
centralizer calculation makes it a field scalar. Subtracting that scalar
gives a commuting map into the fixed line. Such a map kills the whole
commutator space, which is the entire hexacode, and hence is zero.

This is the centralizer calculation for the nonsplit module in
Aschbacher--Smith, 12.7.4(2), printed pp.839--840.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender

private theorem fullWeight_fixedSpace (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit)) :
    fixedSpace evenAction (fullWeightVectorStabilizer v) =
      (Submodule.span F {v}).restrictScalars Bit := by
  refine le_antisymm ?_ (fullWeightVectorStabilizer_fixes_point v)
  intro x hx
  obtain ⟨e, b, hb⟩ := fullWeightVectorQuotient_natural v hv hP
  apply (Submodule.Quotient.mk_eq_zero (Submodule.span F {v})).mp
  apply b.injective
  rw [map_zero]
  apply SL2FourNatural.natural_fixed_eq_zero
  intro g
  obtain ⟨h, rfl⟩ := e.surjective g
  change specialLinearNatural 2 (e h)
    (b ((Submodule.span F {v}).mkQ x)) = b ((Submodule.span F {v}).mkQ x)
  rw [← hb, fullWeightVectorQuotientAction_mk]
  exact congrArg (fun y => b ((Submodule.span F {v}).mkQ y)) (hx h)

/-- Every binary endomorphism commuting with the actual full-weight vector
stabilizer is multiplication by a scalar in the same four-element field. -/
theorem fullWeightVectorStabilizer_commutant_scalar (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit))
    (f : Module.End Bit hexacode)
    (hf : ∀ (g : fullWeightVectorStabilizer v) (x : hexacode),
      f (evenAction g.val x) = evenAction g.val (f x)) :
    ∃ c : F, ∀ x, f x = c • x := by
  let P := Submodule.span F {v}
  let PB := P.restrictScalars Bit
  have hpres : PB ≤ PB.comap f := by
    intro x hx
    have hfixed : f x ∈ fixedSpace evenAction (fullWeightVectorStabilizer v) := by
      intro g
      exact (hf g x).symm.trans (congrArg f (fullWeightVectorStabilizer_fixes_point v hx g))
    rw [fullWeight_fixedSpace v hv hP] at hfixed
    exact hfixed
  let R := Submodule.Quotient.restrictScalarsEquiv Bit P
  let fQ : Module.End Bit (hexacode ⧸ P) :=
    R.toLinearMap.comp ((PB.mapQ PB f hpres).comp R.symm.toLinearMap)
  have hmk (x : hexacode) : fQ (P.mkQ x) = P.mkQ (f x) := rfl
  have hcomm (g : fullWeightVectorStabilizer v) (q : hexacode ⧸ P) :
      fQ (fullWeightVectorQuotientAction v g q) =
        fullWeightVectorQuotientAction v g (fQ q) := by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    rw [fullWeightVectorQuotientAction_mk, hmk, hmk, fullWeightVectorQuotientAction_mk]
    exact congrArg P.mkQ (hf g x)
  obtain ⟨e, b, hb⟩ := fullWeightVectorQuotient_natural v hv hP
  let fN : (Fin 2 → F) →+ (Fin 2 → F) :=
    b.toAddMonoidHom.comp (fQ.toAddMonoidHom.comp b.symm.toAddMonoidHom)
  have hN : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin 2 → F),
      fN (g.val.mulVec x) = g.val.mulVec (fN x) := by
    intro g x
    obtain ⟨h, rfl⟩ := e.surjective g
    obtain ⟨q, rfl⟩ := b.surjective x
    change b (fQ (b.symm (specialLinearNatural 2 (e h) (b q)))) =
      specialLinearNatural 2 (e h) (b (fQ (b.symm (b q))))
    rw [← hb, b.symm_apply_apply, b.symm_apply_apply, hcomm, hb]
  obtain ⟨c, hc⟩ := SL2NaturalOffenders.centralizer_scalar fN hN
  have hscalar (q : hexacode ⧸ P) : fQ q = c • q := by
    apply b.injective
    rw [map_smul]
    have h := hc (b q)
    change b (fQ (b.symm (b q))) = c • b q at h
    rwa [b.symm_apply_apply] at h
  let δ : Module.End Bit hexacode :=
    f - (c • (LinearMap.id : Module.End F hexacode)).restrictScalars Bit
  have hδ (x : hexacode) : δ x ∈ PB := by
    apply (Submodule.Quotient.mk_eq_zero P).mp
    change P.mkQ (f x - c • x) = 0
    rw [map_sub, map_smul, ← hmk, hscalar, sub_self]
  have hδcomm (g : fullWeightVectorStabilizer v) (x : hexacode) :
      δ (evenAction g.val x) = evenAction g.val (δ x) := by
    change f (evenAction g.val x) - c • evenAction g.val x =
      evenFieldAction g.val (f x - c • x)
    rw [map_sub, map_smul, hf]
    rfl
  have hkill : subspaceCommutator evenAction ⊤ (fullWeightVectorStabilizer v) ≤ δ.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, x, _, rfl⟩
    have hfix : evenAction g (δ x) = δ x :=
      fullWeightVectorStabilizer_fixes_point v (hδ x) ⟨g, hg⟩
    change δ (evenAction g x - x) = 0
    rw [map_sub, hδcomm ⟨g, hg⟩, hfix, sub_self]
  have hweight : hammingNorm v.val = 6 :=
    hP.2.2 ⟨v, Submodule.mem_span_singleton_self v⟩ (fun h => hv (congrArg Subtype.val h))
  rw [fullWeightVectorStabilizer_commutator v hweight] at hkill
  refine ⟨c, fun x => ?_⟩
  have hx : δ x = 0 := hkill (Submodule.mem_top : x ∈ (⊤ : Submodule Bit hexacode))
  exact sub_eq_zero.mp hx

/-- A commuting binary endomorphism fixing the same nonzero vector is the
identity on the whole original hexacode module. -/
theorem fullWeightVectorStabilizer_commutant_eq_id (v : hexacode) (hv : v ≠ 0)
    (hP : IsFullWeightScalarPlane ((Submodule.span F {v}).restrictScalars Bit))
    (f : Module.End Bit hexacode)
    (hf : ∀ (g : fullWeightVectorStabilizer v) (x : hexacode),
      f (evenAction g.val x) = evenAction g.val (f x))
    (hfv : f v = v) : f = LinearMap.id := by
  obtain ⟨c, hc⟩ := fullWeightVectorStabilizer_commutant_scalar v hv hP f hf
  have hc1 : c = 1 := (smul_left_injective F hv)
    ((hc v).symm.trans (hfv.trans (one_smul F v).symm))
  apply LinearMap.ext
  intro x
  change f x = x
  rw [hc, hc1, one_smul]

end Representation.Hexacode
