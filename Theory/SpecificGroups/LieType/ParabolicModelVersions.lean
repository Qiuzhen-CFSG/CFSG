module

public import Theory.GroupTheory.FixedElementaryTransport
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Model comparisons for finite Lie-type parabolics

This file records the interfaces which are needed when a concrete root model is
compared with a sigma setup.  The comparison is an actual multiplicative
equivalence of carriers; in particular, the central quotient is transported by
`FixedElementary.carrierEquiv`, rather than by identifying a quotient with its
source by notation.  A parabolic comparison also transports the embedded
`O^{p'}` subgroup, while retaining relative normality in the parabolic.

The four small endpoints have a separate source theorem: the group in the
parabolic construction is the full fixed group, whereas the theorem in the
classification concerns its derived subgroup.  `DerivedParabolicVersion`
therefore keeps the derived carrier, the covering statement, and the relative
index as explicit fields.  This prevents the common but incorrect replacement
of a derived endpoint by `O^{p'}` by convention.

Sources: GLS3, §§2.2.6--2.2.8 and Chapter 3, §3.3 (printed p.124), together
with the root-generated parabolics in the concrete Lie-type model modules.
-/

@[expose] public section

namespace Theory.SpecificGroups.LieType.ParabolicModelVersions

open Theory.GroupTheory.FixedElementary

variable {G H : Type*} [Group G] [Group H]

/-- A root-defined Borel, parabolic and radical candidate in a concrete carrier.

The record only contains inclusions.  Parabolicity and the assertion that the
radical is the intrinsic p-core are geometric theorems and belong to the
corresponding model owner or to the finite-realization assembly.
-/
structure Candidate (G : Type*) [Group G] where
  borel : Subgroup G
  parabolic : Subgroup G
  radical : Subgroup G
  borel_le_parabolic : borel ≤ parabolic
  radical_le_parabolic : radical ≤ parabolic

/-- Transport a candidate through an actual multiplicative equivalence. -/
def Candidate.map (e : G ≃* H) (D : Candidate G) : Candidate H where
  borel := D.borel.map e.toMonoidHom
  parabolic := D.parabolic.map e.toMonoidHom
  radical := D.radical.map e.toMonoidHom
  borel_le_parabolic := Subgroup.map_mono D.borel_le_parabolic
  radical_le_parabolic := Subgroup.map_mono D.radical_le_parabolic

@[simp] theorem Candidate.map_borel (e : G ≃* H) (D : Candidate G) :
    (D.map e).borel = D.borel.map e.toMonoidHom := rfl

@[simp] theorem Candidate.map_parabolic (e : G ≃* H) (D : Candidate G) :
    (D.map e).parabolic = D.parabolic.map e.toMonoidHom := rfl

@[simp] theorem Candidate.map_radical (e : G ≃* H) (D : Candidate G) :
    (D.map e).radical = D.radical.map e.toMonoidHom := rfl

/-- The finite local factor embedded back into the ambient group.

The residual is computed in the subtype `D.parabolic`, so this definition
preserves the source convention `O^{p'}(P)` and its actual embedding into `G`.
-/
def localFactor (p : ℕ) (D : Candidate G) : Subgroup G :=
  (Subgroup.primeToResidual p D.parabolic).map D.parabolic.subtype

theorem localFactor_le_parabolic (p : ℕ) (D : Candidate G) :
    localFactor p D ≤ D.parabolic := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

@[simp] theorem localFactor_subgroupOf (p : ℕ) (D : Candidate G) :
    (localFactor p D).subgroupOf D.parabolic =
      Subgroup.primeToResidual p D.parabolic := by
  change ((Subgroup.primeToResidual p D.parabolic).map D.parabolic.subtype).comap
    D.parabolic.subtype = _
  exact Subgroup.comap_map_eq_self_of_injective D.parabolic.subtype_injective _

@[simp] theorem localFactor_map (p : ℕ) [Finite G] (e : G ≃* H)
    (D : Candidate G) [Fact p.Prime] :
    localFactor p (D.map e) = (localFactor p D).map e.toMonoidHom := by
  symm
  change ((Subgroup.primeToResidual p D.parabolic).map D.parabolic.subtype).map
      e.toMonoidHom =
    (Subgroup.primeToResidual p (D.parabolic.map e.toMonoidHom)).map
      (D.parabolic.map e.toMonoidHom).subtype
  exact Subgroup.map_embedded_primeToResidual_of_hom p D.parabolic e.toMonoidHom

/-- A model comparison preserves the three named root subgroups. -/
structure Compatible (e : G ≃* H) (D : Candidate G) (E : Candidate H) : Prop where
  borel : D.borel.map e.toMonoidHom = E.borel
  parabolic : D.parabolic.map e.toMonoidHom = E.parabolic
  radical : D.radical.map e.toMonoidHom = E.radical

theorem Compatible.localFactor (p : ℕ) [Finite G] (e : G ≃* H)
    (D : Candidate G) (E : Candidate H) (h : Compatible e D E) [Fact p.Prime] :
    (localFactor p D).map e.toMonoidHom = localFactor p E := by
  calc
    (Theory.SpecificGroups.LieType.ParabolicModelVersions.localFactor p D).map
        e.toMonoidHom =
      Theory.SpecificGroups.LieType.ParabolicModelVersions.localFactor p (D.map e) :=
      (localFactor_map p e D).symm
    _ = Theory.SpecificGroups.LieType.ParabolicModelVersions.localFactor p E := by
      change (Subgroup.primeToResidual p (D.parabolic.map e.toMonoidHom)).map
          (D.parabolic.map e.toMonoidHom).subtype =
        (Subgroup.primeToResidual p E.parabolic).map E.parabolic.subtype
      rw [h.parabolic]

theorem Compatible.borel_le (e : G ≃* H) (D : Candidate G) (E : Candidate H)
    (h : Compatible e D E) : D.borel.map e.toMonoidHom ≤ E.parabolic := by
  rw [h.borel]
  exact E.borel_le_parabolic

theorem Compatible.radical_le (e : G ≃* H) (D : Candidate G) (E : Candidate H)
    (h : Compatible e D E) : D.radical.map e.toMonoidHom ≤ E.parabolic := by
  rw [h.radical]
  exact E.radical_le_parabolic

/-- Transport of the elementary fixed-point central quotient used by a
sigma-setup.  The equivariance hypothesis is intentionally explicit: it is
where the root/model comparison proves compatibility with graph-field or
exceptional endomorphisms.
-/
def centralQuotientTransport (p : ℕ) (σ : G ≃* G) (τ : H ≃* H)
    (e : G ≃* H) (he : ∀ g, e (σ g) = τ (e g)) :
    Carrier p σ ≃* Carrier p τ :=
  Theory.GroupTheory.FixedElementary.carrierEquiv p σ τ e he

@[simp] theorem centralQuotientTransport_mk (p : ℕ) (σ : G ≃* G) (τ : H ≃* H)
    (e : G ≃* H) (he : ∀ g, e (σ g) = τ (e g))
    (x : elementarySubgroup p σ) :
    centralQuotientTransport p σ τ e he (QuotientGroup.mk x) =
      QuotientGroup.mk (elementaryEquiv p σ τ e he x) := by
  exact Theory.GroupTheory.FixedElementary.carrierEquiv_mk p σ τ e he x

/-- The same transport when the ambient map is an injective homomorphism whose
image contains every target fixed point. -/
noncomputable def centralQuotientTransportOfEmbedding
    (p : ℕ) (σ : G ≃* G) (τ : H ≃* H) (f : G →* H)
    (hf : Function.Injective f) (he : ∀ g, f (σ g) = τ (f g))
    (hfixed : ∀ h, τ h = h → ∃ g, f g = h) :
    Carrier p σ ≃* Carrier p τ :=
  Theory.GroupTheory.FixedElementary.carrierEquivOfEmbedding p σ τ f hf he hfixed

/-- The literal source assertion for a small derived Lie-type endpoint.

`covers` means that the image of the derived group covers the quotient
`P/U`; it is recorded as `P ≤ U ⊔ K` in the ambient carrier.  The index is
`|U : U ∩ K|`, hence the order is `K.relIndex U`, not `U.relIndex K`.
`root_intersection` is the root/model witness that the intersection is
nontrivial; it is kept as data so that no abstract endpoint convention can
silently discharge it.
-/
structure DerivedParabolicVersion (G : Type*) [Group G] where
  p : ℕ
  p_prime : p.Prime
  K : Subgroup G
  P : Subgroup G
  U : Subgroup G
  borel : Subgroup G
  radical : Subgroup G
  borel_le_P : borel ≤ P
  radical_le_U : radical ≤ U
  U_le_P : U ≤ P
  U_normal : (U.subgroupOf P).Normal
  covers : P ≤ U ⊔ K
  intersection_index : K.relIndex U = p
  U_isPGroup : IsPGroup p U
  root_intersection : ∃ x, x ∈ U ∧ x ∈ K ∧ x ≠ 1

theorem DerivedParabolicVersion.intersection_ne_bot
    (D : DerivedParabolicVersion G) : D.U ⊓ D.K ≠ ⊥ := by
  rintro hbot
  obtain ⟨x, hxU, hxK, hx1⟩ := D.root_intersection
  have hx : x ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact ⟨hxU, hxK⟩
  exact hx1 (Subgroup.mem_bot.mp hx)

theorem DerivedParabolicVersion.intersection_index_eq
    (D : DerivedParabolicVersion G) : D.K.relIndex D.U = D.p :=
  D.intersection_index

theorem DerivedParabolicVersion.relative_normal
    (D : DerivedParabolicVersion G) : (D.U.subgroupOf D.P).Normal :=
  D.U_normal

theorem DerivedParabolicVersion.cover_modulo_radical
    (D : DerivedParabolicVersion G) : D.P ≤ D.U ⊔ D.K :=
  D.covers

end Theory.SpecificGroups.LieType.ParabolicModelVersions

end
