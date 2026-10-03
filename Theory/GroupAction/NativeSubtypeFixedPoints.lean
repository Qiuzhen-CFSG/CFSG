module
public import Theory.GroupAction.Invariant
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Fixed points for a subgroup and its literal subtype image

Let D ≤ P be subgroups of a group G, and retain a supplied action of P
on X. For K ≤ D, the fixed subgroup obtained by restricting first to D
and then K equals the fixed subgroup for the actual image of K in G,
restricted directly along its inclusion in P. Both restrictions use the
same supplied action and the exact one-compHom construction.

The proof lifts each actor through the subtype map and compares the
resulting elements of P explicitly; no action replacement, faithfulness,
finiteness or quotient hypothesis is needed. This transports the same
chosen actor lines between native centralizers and quotient fixed groups
in Stellmacher (10.1), printed p.64, on both V/Z and U/V.
-/

namespace Subgroup
public theorem fixedPoints_subgroup_of_subtype_image
    {G X:Type*} [Group G] [Group X] (P D:Subgroup G) (hDP:D≤P)
    (action:P→*MulAut X) (K:Subgroup D) (hKP:K.map D.subtype≤P) :
    let _ : MulDistribMulAction D X:=MulDistribMulAction.compHom X (action.comp (inclusion hDP))
    let _ : MulDistribMulAction (K.map D.subtype) X:=
      MulDistribMulAction.compHom X (action.comp (inclusion hKP))
    FixedPoints.subgroup (K.map D.subtype) X=FixedPoints.subgroup K X := by
  let _ : MulDistribMulAction D X:=MulDistribMulAction.compHom X (action.comp (inclusion hDP))
  let _ : MulDistribMulAction (K.map D.subtype) X:=
    MulDistribMulAction.compHom X (action.comp (inclusion hKP))
  ext x
  constructor
  · intro hx k
    exact hx ⟨((k:D):G),mem_map_of_mem D.subtype k.property⟩
  · intro hx a
    obtain ⟨d,hd,hda⟩:=a.property
    have hh:=hx (⟨d,hd⟩:K)
    change action ⟨(a:G),hKP a.property⟩ x=x
    have hp:(⟨(a:G),hKP a.property⟩:P)=⟨(d:G),hDP d.property⟩:=Subtype.ext hda.symm
    rw [hp]
    exact hh

end Subgroup
