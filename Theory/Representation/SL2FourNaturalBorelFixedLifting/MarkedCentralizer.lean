module

public import Theory.Representation.SL2FourNaturalBorelFixedLifting
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.SpecificGroups.Alternating.FiveSubgroupExtension.Generators

/-!
# Trivial symmetric centralizer of a marked SL₂(4) Borel

Transport the actual upper-root Sylow subgroup through the prescribed
SL₂(4)-to-A₅ marking. Its normalizer is an even point stabilizer. The known
three-cycle and double-transposition generators, conjugated to that point,
have trivial common centralizer in S₅. This works for every marking and
retains the literal Borel and inclusion into the symmetric group.

Source application: Aschbacher--Smith, 14.7.74, printed p.1077 (PDF p.1094),
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix.SpecialLinearGroup
namespace Representation.SL2FourNaturalBorelFixedLifting
open AlternatingFiveSubgroupExtension.Generators

private theorem stabilizer_centralizer (i : Fin 5) :
    centralizer (((MulAction.stabilizer (alternatingGroup (Fin 5)) i).map
      (alternatingGroup (Fin 5)).subtype) : Set (Equiv.Perm (Fin 5))) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  let t : Equiv.Perm (Fin 5) := Equiv.swap 4 i
  let c : MulAut (Equiv.Perm (Fin 5)) := MulAut.conj t
  have hc (x : alternatingGroup (Fin 5)) (hx : x.val 4 = 4) :
      c x.val ∈ (MulAction.stabilizer (alternatingGroup (Fin 5)) i).map
        (alternatingGroup (Fin 5)).subtype := by
    have heven : c x.val ∈ alternatingGroup (Fin 5) :=
      (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem x.val x.property t
    refine ⟨⟨c x.val, heven⟩, ?_, rfl⟩
    change (t * x.val * t⁻¹) i = i
    simp [t, Equiv.Perm.mul_apply, hx]
  have ha := hg (c a.val) (hc a (by decide))
  have hb := hg (c b.val) (hc b (by decide))
  have hga : c.symm g * a.val = a.val * c.symm g := by
    apply c.injective
    simpa only [map_mul, c.apply_symm_apply] using ha.symm
  have hgb : c.symm g * b.val = b.val * c.symm g := by
    apply c.injective
    simpa only [map_mul, c.apply_symm_apply] using hb.symm
  have hz := centralizer_pair (c.symm g) hga hgb
  exact (map_eq_one_iff c.symm c.symm.injective).mp hz

/-- Every marked upper Borel has trivial centralizer in the actual S₅. -/
theorem marked_borel_centralizer
    (e : SL2FourNatural.SL ≃* alternatingGroup (Fin 5)) :
    centralizer (((rankOneBorel SL2FourNatural.F).map
      ((alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom)) :
        Set (Equiv.Perm (Fin 5))) = ⊥ := by
  let P := (upperUnipotentSylow SL2FourNatural.F 2).mapSurjective
    (f := e.toMonoidHom) e.surjective
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  have he : (rankOneBorel SL2FourNatural.F).map e.toMonoidHom =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    rw [rankOneBorel, map_equiv_normalizer_eq]
    exact hi
  rw [← map_map, he]
  exact stabilizer_centralizer i
end Representation.SL2FourNaturalBorelFixedLifting
