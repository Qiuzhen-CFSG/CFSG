module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Displacement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import Theory.Representation.NormalConstituentDisplacement.FixedLine

/-!
# The full constituent alternative on the source quotient

The action is the faithful conjugation representation of the literal
`H/O₂(H)` on `U/Z`. The Sylow-fixed line argument supplies irreducibility.
The rank-two displacement theorem then proves noncentralization and the
irreducible-or-two-summand alternative, including equal dimensions and a
transvection on each summand.

The remaining earlier-source inputs are explicitly visible: the kernel from
15.3.48(3); the Sylow-fixed line from 15.3.56(7), with its line sizes and
centrality from 15.3.48; the centrality of `v` in the Sylow image; containment
of the distinguished line in the displacement plane from 15.3.53(2); the
rank-two displacement; and the total dimension from 15.3.56(2). The simple
constituent rank bound is precisely the hypothesis of 15.3.57(2).

No two-residual assumption is needed by this proof, so it applies in
particular to the source's nontrivial normal `K* = O²(K*)`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1148.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition

variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- Full 15.3.57(2), conditional on the earlier source kernel, dimension,
Sylow-fixed line and displacement-plane identities. The actual representation
is the faithful conjugation action of `H/O₂(H)` on `U/Z`. -/
theorem normalConstituentConclusion_of_source_fixed_line
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4)
    (hcommZS : ⁅ZS, (T : Subgroup G)⁆ ≤ Z)
    (J : Subgroup (centralizerH Z))
    (hJT : J ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hJ : letI := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
      FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS)
    (K : Subgroup (ActorQuotient Z)) [K.Normal] (v : ActorQuotient Z) (s : ℕ)
    (hvT : ∀ t : actorImage Z (T : Subgroup G), Commute v (t : ActorQuotient Z))
    (hline : ∀ w : Space Z ZS, w.toMul ∈ distinguishedLine Z ZS →
      w ∈ LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id))
    (hsmall : ∀ A : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype),
      A.toRepresentation.IsIrreducible → 3 ≤ Module.finrank (ZMod 2) A.toSubmodule)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) (Space Z ZS) = 2 * (s + 2)) :
    NormalConstituentConclusion (actorRepresentation Z ZS hkernel) K v s := by
  have hρ := actorRepresentation_irreducible_of_pair_fixed_line Z ZS hkernel
    T hTH hZZS hZ hZS hcommZS J hJT hJ
  have hT : IsPGroup 2 (actorImage Z (T : Subgroup G)) :=
    (T.isPGroup'.of_equiv (subgroupOfEquivOfLe hTH).symm).map
      (QuotientGroup.mk' (pCore 2 (centralizerH Z)))
  have hfixed (w : Space Z ZS)
      (hw : ∀ t : actorImage Z (T : Subgroup G), actorRepresentation Z ZS hkernel t w = w) :
      w ∈ LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id) := by
    apply hline
    let := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
    have hf := fixedPoints_eq_distinguishedLine Z ZS (T : Subgroup G) hcommZS J hJT hJ
    rw [← hf]
    intro t
    let tstar : actorImage Z (T : Subgroup G) :=
      ⟨QuotientGroup.mk' (pCore 2 (centralizerH Z)) t.val,
        Subgroup.mem_map.mpr ⟨t.val, t.property, rfl⟩⟩
    exact congrArg Additive.toMul (hw tstar)
  exact Representation.NormalConstituentDisplacement.constituent_alternative
    (actorRepresentation Z ZS hkernel) hρ K (actorImage Z (T : Subgroup G)) v (s + 2)
    hT hvT hfixed hsmall hrank hdim

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
