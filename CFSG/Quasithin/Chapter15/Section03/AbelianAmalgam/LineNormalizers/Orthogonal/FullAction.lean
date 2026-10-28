module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.Action
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts.Transport
public import Theory.SpecificGroups.OrthogonalFourBinary.SingularLineExtension

/-!
# The full ambient action on a singular four-subgroup

The graph-extension theorem lifts through the specified natural action
of `M` on `V`. Compatibility with conjugation puts the chosen lift in
`M_E`, and its action on `E` is exactly the prescribed automorphism.
In particular `G_E` has full action on `E`, so its normal two-core
centralizes `E`. This proves the `Q_E` assertion of 15.3.66(5) from
geometry, independently of the residual-action calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66 and its proof, printed p.1152, PDF p.1169.
-/

@[expose] public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts

variable {G : Type*} [Group G] {V M : Subgroup G}

/-- The coordinates restrict to an actual equivalence on the chosen line. -/
def coordinateLineEquiv (d : NaturalAction V M) (E : Subgroup G) (hEV : E ≤ V) :
    E ≃* coordinateLine d E :=
  (subgroupOfEquivOfLe hEV).symm.trans (d.coordinates.subgroupMap (E.subgroupOf V))

/-- Every automorphism of the singular four-group is induced by an element of `M_E`. -/
theorem lineM_full_action (d : NaturalAction V M) (E : Subgroup G)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩) :
    Function.Surjective (lineAction E (lineM M E) inf_le_right) := by
  intro f
  let c := coordinateLineEquiv d E hEV
  let f' : MulAut (coordinateLine d E) := c.symm.trans (f.trans c)
  obtain ⟨g, hg⟩ := singular_line_aut_extends (coordinateLine d E)
    ((coordinateLine_card d E hEV).trans hcard) (coordinateLine_singular d E hEV hs) f'
  obtain ⟨m, hm⟩ := d.onto g
  have hmE : (m : G) ∈ lineNormalizer E :=
    (coordinateLine_stabilizer_iff d E hEV m).mp
      (hm.symm ▸ mem_lineStabilizer_of_extends _ f' g hg)
  refine ⟨⟨m, m.property, hmE⟩, ?_⟩
  apply MulEquiv.ext
  intro e
  apply Subtype.ext
  have he := hg (c e)
  change vectorAction g (d.coordinates ⟨e, hEV e.property⟩) = (f' (c e) : Multiplicative Space) at he
  have hf : f' (c e) = c (f e) := by
    change c (f (c.symm (c e))) = c (f e)
    rw [c.symm_apply_apply]
  rw [hf] at he
  have hd := d.intertwines m ⟨e, hEV e.property⟩
  change (d.coordinates.symm (vectorAction (d.action m)
    (d.coordinates ⟨e, hEV e.property⟩)) : G) = (m : G) * (e : G) * (m : G)⁻¹ at hd
  rw [hm, he] at hd
  exact hd.symm.trans (congrArg Subtype.val
    (d.coordinates.symm_apply_apply ⟨f e, hEV (f e).property⟩))

/-- The full normalizer also induces every automorphism of the singular line. -/
theorem lineNormalizer_full_action (d : NaturalAction V M) (E : Subgroup G)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩) :
    Function.Surjective E.normalizerMonoidHom := by
  intro f
  obtain ⟨m, hm⟩ := lineM_full_action d E hEV hcard hs f
  exact ⟨inclusion (show lineM M E ≤ lineNormalizer E from inf_le_right) m, hm⟩

/-- The singular line is a Klein four-group through its actual graph coordinates. -/
theorem singularLine_isKleinFour (d : NaturalAction V M) (E : Subgroup G)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩) : IsKleinFour E := by
  obtain ⟨i,hi⟩ := singular_four_eq_graph (coordinateLine d E)
    ((coordinateLine_card d E hEV).trans hcard) (coordinateLine_singular d E hEV hs)
  let e := (coordinateLineEquiv d E hEV).trans
    ((MulEquiv.subgroupCongr hi).trans (graphCoordinates i).symm)
  exact ⟨hcard, (Monoid.exponent_eq_of_mulEquiv e).trans (by simp)⟩

/-- Source 15.3.66(5): the two-core of `G_E` centralizes the chosen singular line. -/
theorem lineQ_le_centralizer [Finite G] (d : NaturalAction V M) (E : Subgroup G)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩) :
    lineQ E ≤ centralizer (E : Set G) := by
  let := singularLine_isKleinFour d E hEV hcard hs
  exact lineQ_le_centralizer_of_full_action E (lineNormalizer_full_action d E hEV hcard hs)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
