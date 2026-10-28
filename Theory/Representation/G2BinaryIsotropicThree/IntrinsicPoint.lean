module

public import Theory.Representation.G2BinaryIsotropicThree.PairHyperplanes


/-!
# The distinguished point of the binary isotropic three-space

Norm preservation lifts a natural-module image in the upper three-space to
its unique singular octonion representative. Products of these representatives
span the first line: e₁e₂=e₀. An automorphism stabilizing the three-space must
therefore fix its first vector over F₂. This identifies the distinguished
point intrinsically and controls all local changes of the three-space marking.

Source: Aschbacher–Smith 13.3.12(4), printed p.890, the compatible point and
three-space normalizers used in the final conjugator adjustment.
-/

public section

open Atlas.SplitOctonion Subgroup Module Submodule
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates

private theorem lift_upper (g : Model K) (w : Three)
    (hg : rho g (targetEmbed false w)∈target false) :
    g.val (representative K (targetEmbed false w)).val=
      (representative K (rho g (targetEmbed false w))).val := by
  have he : mk K (traceZeroAction K g (representative K (targetEmbed false w)))=
      mk K (representative K (rho g (targetEmbed false w))) := by
    apply (equiv K).injective
    change rho g (equiv K (mk K (representative K (targetEmbed false w))))=_
    change rho g (coordinates K (quotientClass K (targetEmbed false w)))=
      coordinates K (quotientClass K (rho g (targetEmbed false w)))
    rw [coordinates_quotientClass,coordinates_quotientClass]
  obtain ⟨r,hr⟩ := (mk_eq_mk_iff K _ _).mp he
  change r • unit=g.val (representative K (targetEmbed false w)).val-
    (representative K (rho g (targetEmbed false w))).val at hr
  have hx : g.val (representative K (targetEmbed false w)).val=
      r • unit+(representative K (rho g (targetEmbed false w))).val := (eq_sub_iff_add_eq.mp hr).symm
  have hn := automorphism_norm g (representative K (targetEmbed false w)).val
  rw [hx] at hn
  change (rho g (targetEmbed false w)) 3=0 ∧
    (rho g (targetEmbed false w)) 4=0 ∧ (rho g (targetEmbed false w)) 5=0 at hg
  have hr0 : r=0 := by
    have hformula : SplitOctonion.norm
        (r • unit+(representative K (rho g (targetEmbed false w))).val)=r*r := by
      simp [SplitOctonion.norm,unit,representative,hg.1,hg.2.1,hg.2.2]
    rw [hformula] at hn
    have hh : r*r=0 := by simpa [SplitOctonion.norm,representative,targetEmbed] using hn
    exact (mul_self_eq_zero.mp hh)
  simpa [hr0] using hx

theorem point_fixed_of_target_invariant (g : Model K)
    (hg : ∀v∈target false,rho g v∈target false) : rho g firstVector=firstVector := by
  let v1 : Three := ![0,1,0]
  let v2 : Three := ![0,0,1]
  have htarget (v : Three) : targetEmbed false v∈target false := (targetEquiv false v).property
  have h1 := lift_upper g v1 (hg _ (htarget v1))
  have h2 := lift_upper g v2 (hg _ (htarget v2))
  have hh := automorphism_mul g (representative K (targetEmbed false v1)).val
    (representative K (targetEmbed false v2)).val
  rw [h1,h2] at hh
  have hp : mul (representative K (targetEmbed false v1)).val
      (representative K (targetEmbed false v2)).val=(basisVector 0 : Carrier K) := by
    decide +kernel
  rw [hp] at hh
  let x := rho g (targetEmbed false v1)
  let y := rho g (targetEmbed false v2)
  have hx : x 3=0 ∧ x 4=0 ∧ x 5=0 := hg _ (htarget v1)
  have hy : y 3=0 ∧ y 4=0 ∧ y 5=0 := hg _ (htarget v2)
  have he : g.val (basisVector 0)=(x 1*y 2+x 2*y 1) • (basisVector 0 : Carrier K) := by
    rw [hh]
    change mul (representative K x).val (representative K y).val=_
    ext i
    fin_cases i <;> simp [SplitOctonion.mul,representative,basisVector,hx.1,hx.2.1,hx.2.2,
      hy.1,hy.2.1,hy.2.2,CharTwo.neg_eq]
  have hn : x 1*y 2+x 2*y 1≠0 := by
    intro hh
    rw [hh,zero_smul] at he
    have hz := g.val.injective (he.trans (map_zero g.val).symm)
    have hc := congrFun hz 0
    simp [basisVector] at hc
  have hc : x 1*y 2+x 2*y 1=1 :=
    ((show ∀a : K,a=0∨a=1 by decide +kernel) _).resolve_left hn
  rw [hc,one_smul] at he
  have hb : (basisVector 0 : Carrier K)=![1,0,0,0,0,0,0,0] := by
    ext j
    fin_cases j <;> simp [basisVector]
  rw [hb] at he
  ext i
  have hi := congrFun he (show Fin 8 from ![0,1,2,5,6,7] i)
  fin_cases i <;> simpa [rho,firstVector,action_apply,representative,
    Atlas.G2.Restricted.NaturalCoordinates.projection,traceZeroAction_val,basisVector] using hi
end Atlas.G2.Natural.BinaryIsotropicThree
