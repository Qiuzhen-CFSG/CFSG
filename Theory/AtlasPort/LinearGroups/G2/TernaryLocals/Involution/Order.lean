module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.Involution.Generators

/-!
# Order of the ternary involution root subgroup

We exhibit 576 distinct elements of the concrete subgroup `generated`. There
are 24 long-root words, distinguished by their images of the odd vector `w`;
they all fix `u` and `v`. There are also 24 short-root/torus words, distinguished
by their images of the pair `(u,v)`. In a product of a short-root/torus word
with a long-root word, the fixed pair determines the first word. Cancellation
and the odd vector then determine the second. The finite coordinate checks
are performed by kernel reduction. Combining this injection with the frame
upper bound proves the exact order, without assuming either root-factor order,
their intersection, or an index in the centralizer.

This supplies the order calculation for the concrete involution centralizer
appearing in Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.4(G1), printed p.417, used for Main Theorem 0.1.2(4), printed pp.3–4
(repeated on pp.481–482). It does not assume the source configuration.
Coordinates use the licensed ATLAS split-octonion port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.TernaryLocals.Involution

/-- The 24 words `I^a J^b x^c`, with `a < 4`, `b < 2`, `c < 3`. -/
private def longWord (i : Fin 24) : P :=
  quaternionI false ^ (i.val / 6) * quaternionJ false ^ (i.val / 3 % 2) *
    positive false ^ (i.val % 3)

/-- The 24 words `I^a J^b x^c t^d`, with `a,b,d < 2`, `c < 3`. -/
private def shortWord (i : Fin 24) : P :=
  quaternionI true ^ (i.val / 12) * quaternionJ true ^ (i.val / 6 % 2) *
    positive true ^ (i.val / 2 % 3) * torusActor ^ (i.val % 2)

private theorem longWord_mem (i : Fin 24) : longWord i ∈ generated :=
  generated.mul_mem (generated.mul_mem
    (generated.pow_mem (quaternionI_mem false) _)
    (generated.pow_mem (quaternionJ_mem false) _))
    (generated.pow_mem (positive_mem false) _)

private theorem shortWord_mem (i : Fin 24) : shortWord i ∈ generated :=
  generated.mul_mem (generated.mul_mem (generated.mul_mem
    (generated.pow_mem (quaternionI_mem true) _)
    (generated.pow_mem (quaternionJ_mem true) _))
    (generated.pow_mem (positive_mem true) _))
    (generated.pow_mem torusActor_mem _)

set_option maxRecDepth 100000 in
private theorem longWord_u (i : Fin 24) : (longWord i).val.val u = u := by
  exact (by decide +kernel : ∀ i : Fin 24, (longWord i).val.val u = u) i

set_option maxRecDepth 100000 in
private theorem longWord_v (i : Fin 24) : (longWord i).val.val v = v := by
  exact (by decide +kernel : ∀ i : Fin 24, (longWord i).val.val v = v) i

set_option maxRecDepth 100000 in
private theorem longWord_odd_injective :
    Function.Injective (fun i : Fin 24 => oddCoordinates ((longWord i).val.val w)) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem shortWord_fixed_injective :
    Function.Injective (fun i : Fin 24 =>
      (fixedCoordinates ((shortWord i).val.val u),
        fixedCoordinates ((shortWord i).val.val v))) := by
  decide +kernel

private def word (p : Fin 24 × Fin 24) : generated :=
  ⟨shortWord p.2 * longWord p.1, generated.mul_mem (shortWord_mem _) (longWord_mem _)⟩

private theorem word_injective : Function.Injective word := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have he : shortWord b * longWord a = shortWord d * longWord c :=
    congrArg Subtype.val h
  have hu := congrArg (fun g : P => g.val.val u) he
  have hv := congrArg (fun g : P => g.val.val v) he
  change (shortWord b).val.val ((longWord a).val.val u) =
    (shortWord d).val.val ((longWord c).val.val u) at hu
  change (shortWord b).val.val ((longWord a).val.val v) =
    (shortWord d).val.val ((longWord c).val.val v) at hv
  rw [longWord_u, longWord_u] at hu
  rw [longWord_v, longWord_v] at hv
  have hbd : b = d := shortWord_fixed_injective
    (Prod.ext (congrArg fixedCoordinates hu) (congrArg fixedCoordinates hv))
  subst d
  have hac : a = c := longWord_odd_injective
    (congrArg (fun g : P => oddCoordinates (g.val.val w)) (mul_left_cancel he))
  exact Prod.ext hac rfl

/-- The five concrete root and torus generators generate exactly 576 elements. -/
theorem card_generated : Nat.card generated = 576 := by
  apply Nat.le_antisymm (generated.card_le_card_group.trans card_le)
  simpa using Nat.card_le_card_of_injective word word_injective

end Atlas.G2.TernaryLocals.Involution
