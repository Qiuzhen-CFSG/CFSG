module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.SpecificGroups.G2.MultiplierOrdinary.RootLifts
public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient

/-!
# The individual root defects in covers of G₂(4)

For each literal positive root A–F, take its full preimage in a finite central
extension of the actual octonion group. Its derived subgroup is central and
has order at most two: the quotient by the restricted projection kernel is
the additive group of GF(4), so the central elementary-four extension bound
applies. No hypothesis that the covering kernel is a two-group is needed.

These six bounds do not show that the defects coincide, nor do they bound
commutators between distinct root preimages. Those further lifted relations
are needed for the exceptional multiplier in Aschbacher–Smith I.1.3(1),
printed p.407 (PDF p.418), and GLS III §6.1. The source calculation is
Griess, Trans. AMS 183 (1973), 355–421, pp.357–371. This module supplies
only the elementary individual-root input, including its canonical-cover
application. The root maps are from the licensed ATLAS port.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary
open MultiplierOrdinary Subgroup
open scoped commutatorElement IsMulCommutative
variable {E : Type*} [Group E]

/-- The full preimage of one of the literal A–F root subgroups. -/
noncomputable def rootPreimage (f : E →* FourBase) (i : Fin 6) : Subgroup E :=
  (positiveRootHom (F := FourField) i).range.comap f

/-- The obstruction to commutativity inside that root preimage. -/
noncomputable def rootDefect (f : E →* FourBase) (i : Fin 6) : Subgroup E :=
  ⁅rootPreimage f i, rootPreimage f i⁆

/-- Root subgroups are abelian downstairs, so each defect lies in the kernel. -/
theorem rootDefect_le_kernel (f : E →* FourBase) (i : Fin 6) :
    rootDefect f i ≤ f.ker := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rw [MonoidHom.mem_ker, map_commutatorElement, ← ha, ← hb]
  exact (Commute.map (Commute.all a b) (positiveRootHom i)).commutator_eq

/-- Each individual root defect is central in a central extension. -/
theorem rootDefect_le_center (f : E →* FourBase)
    (hk : f.ker ≤ center E) (i : Fin 6) : rootDefect f i ≤ center E :=
  (rootDefect_le_kernel f i).trans hk

/-- The elementary-four quotient bounds an individual root defect by two. -/
theorem rootDefect_card_le_two [Finite E]
    (f : E →* FourBase) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (i : Fin 6) : Nat.card (rootDefect f i) ≤ 2 := by
  let R := (positiveRootHom (F := FourField) i).range
  let H := rootPreimage f i
  let g : H →* R := (f.comp H.subtype).codRestrict R (fun x => x.property)
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hf x
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    change f y ∈ R
    rw [hy]
    exact x.property
  have hkg : g.ker ≤ center H := by
    intro x hx
    have hfx : f (x : E) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hk hfx) y)
  let u := positiveRootHom (F := FourField) i
  have hui : Function.Injective u := fun a b h =>
    Multiplicative.toAdd.injective (positiveRoot_injective i h)
  let er : Multiplicative FourField ≃* R :=
    MulEquiv.ofBijective u.rangeRestrict
      ⟨(MonoidHom.rangeRestrict_injective_iff).mpr hui, u.rangeRestrict_surjective⟩
  let eqr := QuotientGroup.quotientKerEquivOfSurjective g hg
  let eqf : (H ⧸ g.ker) ≃* Multiplicative FourField := eqr.trans er.symm
  let : IsMulCommutative (H ⧸ g.ker) :=
    ⟨⟨fun x y => eqf.injective (by simpa only [map_mul] using mul_comm (eqf x) (eqf y))⟩⟩
  let : IsElementaryAbelian 2 (H ⧸ g.ker) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply eqf.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      change (2 : ℕ) • (eqf x).toAdd = 0
      exact CharTwo.two_nsmul _) }
  have hcard : Nat.card (H ⧸ g.ker) = 4 := by
    rw [Nat.card_congr eqf.toEquiv]
    change Nat.card FourField = 4
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  have hbound := card_commutator_le_two_of_central_elementary_four_quotient g.ker hkg hcard
  have hmap : (commutator H).map H.subtype = rootDefect f i := map_subtype_commutator H
  rw [← hmap]
  exact (Nat.le_of_dvd (Nat.card_pos (α := commutator H)) (card_map_dvd _ _)).trans hbound

/-- The unconditional individual-root bounds for the prescribed universal
cover. They do not yet control the whole universal kernel. -/
theorem universal_rootDefect_card_le_two (i : Fin 6) :
    Nat.card (rootDefect (PerfectCentralCovering.universalProjection FourBase) i) ≤ 2 :=
  rootDefect_card_le_two _ (PerfectCentralCovering.universalProjection_surjective FourBase)
    (PerfectCentralCovering.universalProjection_ker_le_center FourBase) i

end Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary

end
