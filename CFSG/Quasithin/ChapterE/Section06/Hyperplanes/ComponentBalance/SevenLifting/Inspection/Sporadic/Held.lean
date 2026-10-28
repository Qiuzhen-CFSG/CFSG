module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import Theory.SpecificGroups.Held.Model.Basic

/-!
# The Held outer-involution obstruction to unrestricted seven inspection

GLS3 Table 5.3p gives the normalizer in He of an outer involution of class
2C as `3#S₇ = 3A₇ · 2`. Since the actor has order two, this normalizer is
its fixed subgroup. The interpretation of Tables 5.3a–z specifies that
`3A₇` is a perfect covering group. Consequently this row has a normal
quasisimple triple cover of A₇, hence a component of exactly the kind
excluded by `SevenActionInspection`.

The theorem below proves this implication from the actual local data: an
order-two automorphism, a subgroup normal in its fixed subgroup, perfectness,
and genuine center and quotient isomorphisms. It constructs the cyclic actor
and identifies its common fixed subgroup before proving component membership.
The second theorem transports the obstruction through an actual Held
equivalence, in arbitrary universe.

The concrete Held row remains an explicit premise. These are conditional
obstruction theorems, not a construction of that row or a proof of the
requested unrestricted inspection. The literal inspection sentence in E.6.18
therefore requires a source-level repair before it can be assembled from this
table. The surrounding E.6.18–19 argument also has `U ≤ V ≤ Z(Q)` with Q
Sylow in H₁; the unrestricted predicate does not retain that information.

Sources: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18–19,
printed p.252 (PDF p.263), and Theorem C, printed p.33;
GLS3, interpretation of Tables 5.3a–z, pp.260–261, Table 5.3p, p.277,
and its discussion in §5.4. The local transcription is
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
namespace HeldInspection

/-- A normal perfect triple cover in an involution fixed subgroup contradicts
the unrestricted inspection. Normality is relative to the actual fixed subgroup;
component membership and the nontrivial cyclic two-action are proved here. -/
theorem not_inspection_of_fixed_normal_triple_cover {G : Type*} [Group G] [Finite G]
    (r : MulAut G) (hr : orderOf r = 2) (L : Subgroup G)
    (hLF : L ≤ r.fixedSubgroup)
    (hn : (L.subgroupOf r.fixedSubgroup).Normal)
    [Group.IsPerfect L]
    (eZ : center L ≃* Multiplicative (ZMod 3))
    (eQ : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) :
    ¬ SevenActionInspection G := by
  intro hi
  let P := zpowers r
  have hp : IsPGroup 2 P := IsPGroup.of_card_dvd_pow (n := 1) (by
    simp only [P, Nat.card_zpowers, hr, pow_one, dvd_refl])
  have hF : FixedPoints.subgroup P G = r.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup r x).mpr (hx ⟨r, mem_zpowers r⟩)
    · intro hx
      have hle : P ≤ MulAction.stabilizer (MulAut G) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup r x).mp hx)
      exact fun a => hle a.property
  let hq : IsQuasisimple L :=
    { toIsPerfect := inferInstance
      simple := (MulEquiv.isSimpleGroup_congr eQ).mpr
        (alternatingGroup.isSimpleGroup (by simp)) }
  have hc : IsComponent r.fixedSubgroup (L.subgroupOf r.fixedSubgroup) :=
    ⟨hn.isSubnormal, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLF).symm⟩
  have hseven : IsSeven L := Or.inr ⟨hq, ⟨eZ⟩, ⟨eQ⟩⟩
  have hb : P = ⊥ := hi P hp L (hF.symm ▸ hLF) (hF.symm ▸ hc) hseven
  have hrone : r = 1 := mem_bot.mp (hb ▸ mem_zpowers r)
  simp [hrone] at hr

/-- The same obstruction applies to any actual Held model. The 2C row is an
explicit unproved model input, not a conclusion inferred from a family label. -/
theorem not_inspection_of_held_equiv_of_fixed_normal_triple_cover
    {S : Type*} [Group S] (e : S ≃* Held.He)
    (r : MulAut Held.He) (hr : orderOf r = 2) (L : Subgroup Held.He)
    (hLF : L ≤ r.fixedSubgroup)
    (hn : (L.subgroupOf r.fixedSubgroup).Normal)
    [Group.IsPerfect L]
    (eZ : center L ≃* Multiplicative (ZMod 3))
    (eQ : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) :
    ¬ SevenActionInspection S := by
  intro hi
  exact not_inspection_of_fixed_normal_triple_cover r hr L hLF hn eZ eQ
    (SporadicInspection.of_equiv e.symm hi)

end HeldInspection
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
