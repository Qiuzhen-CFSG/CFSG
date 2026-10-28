module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Marking

/-!
# The two natural Omega constituents of P/V

`NaturalQuotientPair` expresses the actual equivariant decomposition in
15.3.54(4), specialized to s = 1 as established by 15.3.58(2). An
isomorphism on the image of I identifies its two Omega factors. Both
move all of V, as required by 15.3.53(1), so these are not the original
definite-plane factors. Separate coordinates identify P/V with two
natural binary planes, and the compatibility equation retains conjugation
by the same element of I on the literal quotient.

In the source application I = pairI Z ZS g and P = pairP Z ZS g;
V = localModule T M. Only normality inside P is required for the
quotient. These are explicit earlier-source inputs, not conclusions
extracted from the legacy cardinality-only `G26Witness`.

The elementary centralizer reduction proved here says that an element
of P commuting with an actor that is fixed-point-free on both quotient
constituents lies in V. Determining the cubic actor on these constituents
and constructing its symmetric centralizer remain separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53–54,
printed p.1146; 15.3.58(2), p.1148; setup of 15.3.60, p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
variable {G : Type*} [Group G] {M V : Subgroup G}

/-- Restrict the actual actor to its image on I. -/
def imageActor (d : NaturalOrthogonalAction M V) (I : Subgroup G) (hIM : I ≤ M) :
    I →* d.image I where
  toFun a := ⟨d.actor ⟨a, hIM a.property⟩, ⟨⟨a, hIM a.property⟩, a.property, rfl⟩⟩
  map_one' := Subtype.ext (d.actor.map_one)
  map_mul' a b := Subtype.ext
    (d.actor.map_mul (⟨a, hIM a.property⟩ : M) ⟨b, hIM b.property⟩)

/-- The first Omega factor, as an actual subgroup of I in G. -/
def firstOmegaFactor (d : NaturalOrthogonalAction M V) (I : Subgroup G) (hIM : I ≤ M)
    (e : d.image I ≃* OrthogonalPlaneActor × OrthogonalPlaneActor) : Subgroup G :=
  ((MonoidHom.snd OrthogonalPlaneActor OrthogonalPlaneActor).comp
    (e.toMonoidHom.comp (imageActor d I hIM))).ker.map I.subtype

/-- The second Omega factor, as an actual subgroup of I in G. -/
def secondOmegaFactor (d : NaturalOrthogonalAction M V) (I : Subgroup G) (hIM : I ≤ M)
    (e : d.image I ≃* OrthogonalPlaneActor × OrthogonalPlaneActor) : Subgroup G :=
  ((MonoidHom.fst OrthogonalPlaneActor OrthogonalPlaneActor).comp
    (e.toMonoidHom.comp (imageActor d I hIM))).ker.map I.subtype

/-- The genuine two natural constituents in 15.3.54(4), specialized to s = 1.
The factor coordinates describe the Omega image on V, and the separate
quotient coordinates describe P/V. Full displacement on V distinguishes
the Omega factors from the original definite-plane factors. -/
structure NaturalQuotientPair (d : NaturalOrthogonalAction M V)
    (I P : Subgroup G) (hIM : I ≤ M) (hIP : I ≤ normalizer (P : Set G))
    [(V.subgroupOf P).Normal] where
  factors : d.image I ≃* OrthogonalPlaneActor × OrthogonalPlaneActor
  first_moves : ⁅V, firstOmegaFactor d I hIM factors⁆ = V
  second_moves : ⁅V, secondOmegaFactor d I hIM factors⁆ = V
  coordinates : (P ⧸ V.subgroupOf P) ≃* OrthogonalPlaneVector × OrthogonalPlaneVector
  compatible : letI := FourGroupMatrixCoordinates.naturalAction
    ∀ (a : I) (p : P),
      coordinates (QuotientGroup.mk' (V.subgroupOf P)
        ⟨(a : G) * (p : G) * (a : G)⁻¹,
          (mem_normalizer_iff.mp (hIP a.property) p).mp p.property⟩) =
      ((factors (imageActor d I hIM a)).1 •
          (coordinates (QuotientGroup.mk' (V.subgroupOf P) p)).1,
        (factors (imageActor d I hIM a)).2 •
          (coordinates (QuotientGroup.mk' (V.subgroupOf P) p)).2)

namespace NaturalQuotientPair
variable {d : NaturalOrthogonalAction M V}
  {I P : Subgroup G} {hIM : I ≤ M} {hIP : I ≤ normalizer (P : Set G)}
  [(V.subgroupOf P).Normal]
  (r : NaturalQuotientPair d I P hIM hIP)
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction

/-- A centralizing element of P belongs to V when the actor fixes no
nonidentity vector in either of the two genuine quotient constituents. -/
theorem mem_lower_of_commute (a : I)
    (hfirst : ∀ v : OrthogonalPlaneVector,
      (r.factors (imageActor d I hIM a)).1 • v = v → v = 1)
    (hsecond : ∀ v : OrthogonalPlaneVector,
      (r.factors (imageActor d I hIM a)).2 • v = v → v = 1)
    (p : P) (hcomm : (a : G) * (p : G) = (p : G) * (a : G)) : (p : G) ∈ V := by
  have he : (⟨(a : G) * (p : G) * (a : G)⁻¹,
      (mem_normalizer_iff.mp (hIP a.property) p).mp p.property⟩ : P) = p := by
    apply Subtype.ext
    change (a : G) * (p : G) * (a : G)⁻¹ = (p : G)
    rw [hcomm, mul_inv_cancel_right]
  have hc := r.compatible a p
  rw [he] at hc
  have h1 := hfirst _ (congrArg Prod.fst hc).symm
  have h2 := hsecond _ (congrArg Prod.snd hc).symm
  have hq : QuotientGroup.mk' (V.subgroupOf P) p = 1 := by
    apply r.coordinates.injective
    rw [map_one]
    exact Prod.ext h1 h2
  exact (QuotientGroup.eq_one_iff p).mp hq

include r in
/-- The explicit two natural summands have order sixteen. -/
theorem card_quotient : Nat.card (P ⧸ V.subgroupOf P) = 16 := by
  rw [Nat.card_congr r.coordinates.toEquiv]
  norm_num [OrthogonalPlaneVector, Nat.card_eq_fintype_card]
end NaturalQuotientPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
