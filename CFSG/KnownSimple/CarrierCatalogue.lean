module

public import CFSG.KnownSimple.ClassicalModels
public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.KnownSimple.ConstructedSporadicCarriers
public import CFSG.KnownSimple.SporadicCarriers
public import CFSG.Quasithin.KGroupGuards
public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.SpecificGroups.ReeF4.Model
public import Theory.AtlasPort.LinearGroups.G2.Basic
public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.SpecificGroups.Tits.Presentation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The complete known-simple carrier catalogue

`IsKnownSimpleCarrier` contains prime cyclic groups, alternating groups of
degree at least five, all six classical families, all exceptional Lie
families, the conventional small derived cases, and all twenty-six sporadics.
Its finite-simple guard `IsKnownSimple` specifies the source class K. The
earlier partial predicates `IsConstructedCarrier` and
`IsConstructedKnownSimple` are preserved, with proved inclusions in the full
catalogue; their old guard bridges retain their original statements.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*, §0.1
(printed pp. 4 and 482); GLS3, Theorem 2.2.7 and Definition 2.2.8
(`refs/KGroup/GLS3/chapter2.tex`). The G₂ carrier is the automorphism group
of the explicit split octonions. Suzuki and small Ree use their sourced
root, torus and Weyl matrices. We include the actual commutator carriers
PSp₄(2)′, G₂(2)′ and ²G₂(3)′, so their conventional simple endpoints do not
require an exceptional-isomorphism theorem just to name them. The remaining
endpoint ²F₄(2)′ is Parrott's Tits presentation, not the full group ²F₄(2).

The split F/E families are the central quotients of integral root-generated
groups. Twisted ²E₆ and ³D₄ use the actual pinned graph-field actions and
the characteristic-prime generated subgroups of their fixed groups, followed
by central quotient. The Ree ²F₄ construction uses the exceptional long-short
endomorphism, with q > 2. The sporadic carriers and their precise source
representations are listed in `SporadicCarriers`; the Monster entry uses the
fixed Griess forms and their actual source Leech comparison and spin action.

The K-group bridges specialize the general guard lemmas: each simple section
of a finite group already satisfies the finite-simple guard. Defining K this
way requires no unrelated order or simplicity certificates for its entries.
It also does not prove that every finite simple group belongs to K. Transport
uses composition of actual multiplicative equivalences throughout.
-/

@[expose] public section

universe u v

namespace CFSG.KnownSimple

/-- Prime cyclic groups, represented by the additive group of the prime ring. -/
def IsPrimeCyclicCarrier (G : Type u) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* Multiplicative (ZMod p))

/-- Split G₂ in its simple range, using the full split-octonion automorphisms. -/
def IsG2Carrier (G : Type u) [Group G] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F),
    2 < Nat.card F ∧ Nonempty (G ≃* Atlas.G2.Model F)

/-- The conventional small simple derived carriers. No assertion about their
order or simplicity is used in specifying these concrete groups. -/
inductive IsSmallDerivedCarrier (G : Type u) [Group G] : Prop
  | symplectic (iso : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
  | g2 (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | ree (iso : Nonempty (G ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)))
  | tits (iso : Nonempty (G ≃* Tits.ParrottGroup))

/-- All currently available branches; explicitly not the full known-simple K. -/
inductive IsConstructedCarrier (G : Type u) [Group G] : Prop
  | cyclic (model : IsPrimeCyclicCarrier G)
  | alternating (n : ℕ) (hn : 5 ≤ n)
      (iso : Nonempty (G ≃* alternatingGroup (Fin n)))
  | classical (model : IsClassicalModel G)
  | g2 (model : IsG2Carrier G)
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | smallRee (q : ℕ) (model : ExceptionalGroup.IsReeG2 G q)
  | smallDerived (model : IsSmallDerivedCarrier G)
  | sporadic (model : IsConstructedSporadicCarrier G)

/-- The finite simple guard of the explicitly partial carrier catalogue. -/
def IsConstructedKnownSimple (G : Type u) [Group G] : Prop :=
  Finite G ∧ IsSimpleGroup G ∧ IsConstructedCarrier G

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsPrimeCyclicCarrier.of_mulEquiv (h : IsPrimeCyclicCarrier G)
    (e : H ≃* G) : IsPrimeCyclicCarrier H := by
  obtain ⟨p, hp, ⟨f⟩⟩ := h
  exact ⟨p, hp, ⟨e.trans f⟩⟩

theorem IsG2Carrier.of_mulEquiv (h : IsG2Carrier G) (e : H ≃* G) :
    IsG2Carrier H := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := h
  exact ⟨F, hF, hfin, hcard, ⟨e.trans f⟩⟩

theorem IsSmallDerivedCarrier.of_mulEquiv (h : IsSmallDerivedCarrier G)
    (e : H ≃* G) : IsSmallDerivedCarrier H := by
  cases h with
  | symplectic iso => exact .symplectic (iso.map fun f => e.trans f)
  | g2 iso => exact .g2 (iso.map fun f => e.trans f)
  | ree iso => exact .ree (iso.map fun f => e.trans f)
  | tits iso => exact .tits (iso.map fun f => e.trans f)

/-- Every constructed branch is invariant under isomorphism across universes. -/
theorem IsConstructedCarrier.of_mulEquiv (h : IsConstructedCarrier G)
    (e : H ≃* G) : IsConstructedCarrier H := by
  cases h with
  | cyclic h => exact .cyclic (h.of_mulEquiv e)
  | alternating n hn iso => exact .alternating n hn (iso.map fun f => e.trans f)
  | classical h => exact .classical (h.of_mulEquiv e)
  | g2 h => exact .g2 (h.of_mulEquiv e)
  | suzuki m hm iso => exact .suzuki m hm (iso.map fun f => e.trans f)
  | smallRee q h => exact .smallRee q (h.of_mulEquiv e)
  | smallDerived h => exact .smallDerived (h.of_mulEquiv e)
  | sporadic h => exact .sporadic (h.of_mulEquiv e)

theorem isConstructedCarrier_mulEquiv_iff (e : G ≃* H) :
    IsConstructedCarrier G ↔ IsConstructedCarrier H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem IsConstructedKnownSimple.of_mulEquiv (h : IsConstructedKnownSimple G)
    (e : H ≃* G) : IsConstructedKnownSimple H := by
  let : Finite G := h.1
  exact ⟨Finite.of_injective e e.injective,
    e.isSimpleGroup_congr.mpr h.2.1, h.2.2.of_mulEquiv e⟩

theorem isConstructedKnownSimple_mulEquiv_iff (e : G ≃* H) :
    IsConstructedKnownSimple G ↔ IsConstructedKnownSimple H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem constructedCarrier_isIsoInvariant :
    Quasithin.GroupClass.IsIsoInvariant IsConstructedCarrier.{u} :=
  fun _ _ _ _ e => isConstructedCarrier_mulEquiv_iff e

theorem constructedKnownSimple_isIsoInvariant :
    Quasithin.GroupClass.IsIsoInvariant IsConstructedKnownSimple.{u} :=
  fun _ _ _ _ e => isConstructedKnownSimple_mulEquiv_iff e

/-- Guarding the partial catalogue does not change its K-group hypothesis on
finite ambient groups. This is not a completeness assertion about that list. -/
theorem isKGroup_constructed_guard_iff (G : Type u) [Group G] [Finite G] :
    Quasithin.IsKGroup IsConstructedKnownSimple G ↔
      Quasithin.IsKGroup IsConstructedCarrier G :=
  Quasithin.isKGroup_finiteSimple_guard_iff IsConstructedCarrier G

/-- The same bridge for the proper-subgroup hypothesis. -/
theorem hasProperKSubgroups_constructed_guard_iff
    (G : Type u) [Group G] [Finite G] :
    Quasithin.HasProperKSubgroups IsConstructedKnownSimple G ↔
      Quasithin.HasProperKSubgroups IsConstructedCarrier G :=
  Quasithin.hasProperKSubgroups_finiteSimple_guard_iff IsConstructedCarrier G

/-- The complete concrete carrier catalogue for K. Every branch is specified
by actual group isomorphisms, independently of the classification hypothesis. -/
inductive IsKnownSimpleCarrier (G : Type u) [Group G] : Prop
  | cyclic (model : IsPrimeCyclicCarrier G)
  | alternating (n : ℕ) (hn : 5 ≤ n)
      (iso : Nonempty (G ≃* alternatingGroup (Fin n)))
  | classical (model : IsClassicalModel G)
  | g2 (model : IsG2Carrier G)
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | exceptional (model : IsExceptionalExtensionModel G)
  | triality (model : Triality.Standard.IsTrialityGroup G)
  | reeF4 (model : ReeF4.IsReeF4Model G)
  | smallDerived (model : IsSmallDerivedCarrier G)
  | sporadic (model : IsSporadicCarrier G)

/-- The source class K, with its finite-simple guard. This definition does not
require order or simplicity certification of every carrier in advance. -/
def IsKnownSimple (G : Type u) [Group G] : Prop :=
  Finite G ∧ IsSimpleGroup G ∧ IsKnownSimpleCarrier G

/-- All the earlier partial entries belong to the full catalogue. -/
theorem IsConstructedCarrier.isKnownSimpleCarrier (h : IsConstructedCarrier G) :
    IsKnownSimpleCarrier G := by
  cases h with
  | cyclic h => exact .cyclic h
  | alternating n hn iso => exact .alternating n hn iso
  | classical h => exact .classical h
  | g2 h => exact .g2 h
  | suzuki m hm iso => exact .suzuki m hm iso
  | smallRee q h => exact .exceptional (.reeG2 q h)
  | smallDerived h => exact .smallDerived h
  | sporadic h => exact .sporadic h.isSporadicCarrier

theorem IsConstructedKnownSimple.isKnownSimple (h : IsConstructedKnownSimple G) :
    IsKnownSimple G :=
  ⟨h.1, h.2.1, h.2.2.isKnownSimpleCarrier⟩

/-- Cross-universe transport of the entire catalogue. -/
theorem IsKnownSimpleCarrier.of_mulEquiv (h : IsKnownSimpleCarrier G)
    (e : H ≃* G) : IsKnownSimpleCarrier H := by
  cases h with
  | cyclic h => exact .cyclic (h.of_mulEquiv e)
  | alternating n hn iso => exact .alternating n hn (iso.map fun f => e.trans f)
  | classical h => exact .classical (h.of_mulEquiv e)
  | g2 h => exact .g2 (h.of_mulEquiv e)
  | suzuki m hm iso => exact .suzuki m hm (iso.map fun f => e.trans f)
  | exceptional h => exact .exceptional (h.of_mulEquiv e)
  | triality h => exact .triality (h.of_mulEquiv e)
  | reeF4 h => exact .reeF4 (h.of_mulEquiv e)
  | smallDerived h => exact .smallDerived (h.of_mulEquiv e)
  | sporadic h => exact .sporadic (h.of_mulEquiv e)

theorem isKnownSimpleCarrier_mulEquiv_iff (e : G ≃* H) :
    IsKnownSimpleCarrier G ↔ IsKnownSimpleCarrier H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem IsKnownSimple.of_mulEquiv (h : IsKnownSimple G) (e : H ≃* G) :
    IsKnownSimple H := by
  let : Finite G := h.1
  exact ⟨Finite.of_injective e e.injective,
    e.isSimpleGroup_congr.mpr h.2.1, h.2.2.of_mulEquiv e⟩

theorem isKnownSimple_mulEquiv_iff (e : G ≃* H) :
    IsKnownSimple G ↔ IsKnownSimple H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem knownSimpleCarrier_isIsoInvariant :
    Quasithin.GroupClass.IsIsoInvariant IsKnownSimpleCarrier.{u} :=
  fun _ _ _ _ e => isKnownSimpleCarrier_mulEquiv_iff e

theorem knownSimple_isIsoInvariant :
    Quasithin.GroupClass.IsIsoInvariant IsKnownSimple.{u} :=
  fun _ _ _ _ e => isKnownSimple_mulEquiv_iff e

/-- A finite simple group needs only its actual catalogue isomorphism. -/
theorem isKnownSimple_iff_carrier [Finite G] [IsSimpleGroup G] :
    IsKnownSimple G ↔ IsKnownSimpleCarrier G :=
  ⟨fun h => h.2.2, fun h => ⟨inferInstance, inferInstance, h⟩⟩

/-- On finite ambient groups, the full source K-group condition can be used
with either the guarded class or its concrete carrier catalogue. -/
theorem isKGroup_knownSimple_guard_iff (G : Type u) [Group G] [Finite G] :
    Quasithin.IsKGroup IsKnownSimple G ↔
      Quasithin.IsKGroup IsKnownSimpleCarrier G :=
  Quasithin.isKGroup_finiteSimple_guard_iff IsKnownSimpleCarrier G

/-- The full proper-K hypothesis is likewise unchanged by its guard. -/
theorem hasProperKSubgroups_knownSimple_guard_iff
    (G : Type u) [Group G] [Finite G] :
    Quasithin.HasProperKSubgroups IsKnownSimple G ↔
      Quasithin.HasProperKSubgroups IsKnownSimpleCarrier G :=
  Quasithin.hasProperKSubgroups_finiteSimple_guard_iff IsKnownSimpleCarrier G

/-- Every named sporadic carrier is present in the full catalogue. -/
theorem isKnownSimpleCarrier_sporadic (name : SporadicName) :
    IsKnownSimpleCarrier name.Carrier :=
  .sporadic (isSporadicCarrier_carrier name)

/-- The fixed Griess carrier supplies the Monster entry without action parameters. -/
theorem isKnownSimpleCarrier_monster :
    IsKnownSimpleCarrier Sporadic.Monster.GriessGroup :=
  .sporadic isSporadicCarrier_monster

/-- All prime powers, including 2 and odd ones, occur in the triality branch. -/
theorem isKnownSimpleCarrier_triality (P : Triality.Standard.Parameters) :
    IsKnownSimpleCarrier (Triality.Standard.Carrier P) :=
  .triality (Triality.Standard.isTrialityGroup_carrier P)

/-- The Ree family above its nonsimple q = 2 endpoint. -/
theorem isKnownSimpleCarrier_reeF4 (m : ℕ) (hm : 1 ≤ m) :
    IsKnownSimpleCarrier (ReeF4.Model m) := .reeF4 (ReeF4.isReeF4Model_self m hm)

/-- The separate simple endpoint ²F₄(2)′. -/
theorem isKnownSimpleCarrier_tits : IsKnownSimpleCarrier Tits.ParrottGroup :=
  .smallDerived (.tits ⟨MulEquiv.refl _⟩)

/-- Every Suzuki parameter in its simple range belongs to K's carrier list. -/
theorem isKnownSimpleCarrier_suzuki (m : ℕ) (hm : 1 ≤ m) :
    IsKnownSimpleCarrier (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
  .suzuki m hm ⟨MulEquiv.refl _⟩

end CFSG.KnownSimple
