module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz

/-!+# Seven Leech-related sporadic carriers for the known-simple catalogue

These are the seven entries J₂, HS, Co₁, Co₂, Co₃, McL and sporadic Suz.
The source catalogue is GLS3, Theorem 2.2.7 and Definition 2.2.8
(`refs/KGroup/GLS3/chapter2.tex`), and Aschbacher–Smith, *The Classification
of Quasithin Groups*, §0.1 (printed pp. 4 and 482).

We use independently sourced ATLAS representations: `J2G1-p100B0`,
`HSG1-p100B0`, `Co1G1-f2r24B0`, `Co2G1-p2300B0`, `Co3G1-p276B0`,
`McLG1-p275B0` and `SuzG1-p1782B0`. Each carrier is the subgroup generated
by the published permutations or invertible matrices. The original data,
attribution and action conventions are retained in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/`.

These are alternate representations to the unfinished lattice ports:
J₂ as `IcosianProjectiveModel` (the full icosian Hermitian group modulo
its two central signs), HS as `HSModel` (a Leech 2-3-3 triangle stabilizer),
Co₁ as `LeechCentralQuotient` (the full Leech isometry group modulo ±1),
Co₂ and Co₃ as full norm-four and norm-six vector stabilizers,
McL as `McLModel` (the pointwise 2-2-3 triangle stabilizer), and Suz as
`EisensteinProjectiveModel` (the Eisenstein centralizer modulo its six
scalar isometries). No comparison isomorphism with those ports is asserted.
In particular, the Co₁ entry is the published representation of Co₁ itself,
and the Suz entry is sporadic Suz, not its central cover or the Lie family.

Membership uses actual multiplicative equivalences; transport composes them.
No finiteness, order, simplicity or recognition certificate is a prerequisite
for this contribution. This module neither defines the full catalogue nor
changes its existing union and guard interfaces.
-/

@[expose] public section

namespace CFSG.KnownSimple

universe u v

/-- The seven sporadic entries supplied by this contribution. -/
inductive LeechSporadicName
  | j2
  | hs
  | co1
  | co2
  | co3
  | mcl
  | suz

/-- A fixed sourced carrier for each of the seven entries. -/
def LeechSporadicName.Carrier : LeechSporadicName → Type
  | .j2 => Sporadic.LeechRelated.J2.Carrier
  | .hs => Sporadic.LeechRelated.HS.Carrier
  | .co1 => Sporadic.LeechRelated.Co1.Carrier
  | .co2 => Sporadic.LeechRelated.Co2.Carrier
  | .co3 => Sporadic.LeechRelated.Co3.Carrier
  | .mcl => Sporadic.LeechRelated.McL.Carrier
  | .suz => Sporadic.LeechRelated.Suz.Carrier

instance LeechSporadicName.carrierGroup (name : LeechSporadicName) :
    Group name.Carrier := by
  cases name <;> unfold LeechSporadicName.Carrier <;> infer_instance

/-- Isomorphism to one of the seven concrete sourced carriers. -/
def IsLeechSporadicCarrier (G : Type u) [Group G] : Prop :=
  ∃ name : LeechSporadicName, Nonempty (G ≃* name.Carrier)

theorem isLeechSporadicCarrier_carrier (name : LeechSporadicName) :
    IsLeechSporadicCarrier name.Carrier := ⟨name, ⟨MulEquiv.refl _⟩⟩

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsLeechSporadicCarrier.of_mulEquiv
    (h : IsLeechSporadicCarrier G) (e : H ≃* G) :
    IsLeechSporadicCarrier H := by
  obtain ⟨name, ⟨f⟩⟩ := h
  exact ⟨name, ⟨e.trans f⟩⟩

theorem isLeechSporadicCarrier_mulEquiv_iff (e : G ≃* H) :
    IsLeechSporadicCarrier G ↔ IsLeechSporadicCarrier H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end CFSG.KnownSimple
