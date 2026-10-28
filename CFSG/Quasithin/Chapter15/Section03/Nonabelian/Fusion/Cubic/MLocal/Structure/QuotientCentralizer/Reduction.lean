module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientAction
public import Theory.GroupAction.PrimeGroupFixedImage

/-!
# The marked lower centralizer and the quotient reduction

For the actual Sylow three-subgroup D of C_M(V₁), the coprime kernel of
the prescribed action gives a nonidentity cubic actor. A calculation in
the literal orthogonal model shows that its fixed vectors are exactly V₁.
Orbit counting in fibers lifts centralizers through the same coprime
kernel and gives the entire image of C_M(D), without normality of D.

On the genuine two natural constituents of P/V, a nontrivial cubic actor
has no nonidentity fixed vector. Consequently, once both projections are
proved nontrivial, the compatible quotient action puts C_P(D) inside V;
the lower calculation then gives C_P(D) = V₁. The projection hypotheses
in the final two helpers are explicit remaining obligations. This module
does not assert them or the separate local equality C_M(V) = P.

The normalization needed for P/V comes from the literal two-core P = O₂(I)
and the earlier center equality V = Z(P), with normality only inside P.
No legacy G.2.6 cardinality witness or centralizer splitting is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.49(4),
15.3.53–55, 15.3.58(2), and the setup of 15.3.60, printed pp.1142, 1146–1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
open OrthogonalGeometry
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
private instance : DecidableEq OrthogonalActor :=
  (RegularWreathProduct.equivProd _ _).decidableEq
private instance : Fintype OrthogonalActor := Fintype.ofEquiv
  ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
  (RegularWreathProduct.equivProd _ _).symm

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 4000 in
private theorem cubic_plane_certificate : ∀ (i : OrthogonalPlaneIndex) (a : OrthogonalActor),
    a ^ 3 = 1 → a ≠ 1 →
    (∀ w : OrthogonalVector, (∀ j, j ≠ i → w j = 1) → a • w = w) →
    ∀ w : OrthogonalVector, a • w = w ↔ ∀ j, j ≠ i → w j = 1 := by
  decide +kernel

private theorem cubic_natural_certificate : ∀ a : OrthogonalPlaneActor,
    a ^ 3 = 1 → a ≠ 1 → ∀ w : OrthogonalPlaneVector, a • w = w → w = 1 := by
  decide +kernel

variable {G : Type*} [Group G] {M V : Subgroup G}

/-- A three-subgroup centralizer maps onto the centralizer of its actual image. -/
theorem image_centralizer_cubic [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    {D : Subgroup G} (hDM : D ≤ M) (hD : IsPGroup 3 D) :
    d.image (M ⊓ centralizer (D : Set G)) = centralizer (d.image D : Set OrthogonalActor) := by
  have hker : ¬ 3 ∣ Nat.card d.actor.ker := by
    rw [d.ker_actor]
    exact (Nat.prime_three.coprime_iff_not_dvd).mp hcop
  have hc := centralizer_map_of_prime_free_kernel d.actor d.onto hker
    (D.subgroupOf M) hD.comap_subtype
  have he : (M ⊓ centralizer (D : Set G)).subgroupOf M =
      centralizer (D.subgroupOf M : Set M) := by
    ext m
    constructor
    · intro hm n hn
      exact Subtype.ext (hm.2 n hn)
    · intro hm
      exact ⟨m.property, fun n hn => congrArg Subtype.val (hm ⟨n, hDM hn⟩ hn)⟩
  simpa only [NaturalOrthogonalAction.image, he] using hc

/-- The full image equality for the actual selected source cubic. -/
theorem image_centralizer_planeCubic [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G)) :
    d.image (M ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G)) =
      centralizer (d.image (planeCubic M (d.plane i) PM3) : Set OrthogonalActor) :=
  image_centralizer_cubic d hcop (planeCubic_le_M M (d.plane i) PM3)
    (PM3.isPGroup'.map _)

/-- The selected plane cubic has a nonidentity actor of order three. -/
theorem planeCubic_generator [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G)) :
    ∃ a : M, (a : G) ∈ planeCubic M (d.plane i) PM3 ∧
      zpowers (a : G) = planeCubic M (d.plane i) PM3 ∧
      orderOf a = 3 ∧ d.actor a ≠ 1 := by
  let D := planeCubic M (d.plane i) PM3
  have hcard : Nat.card D = 3 := card_planeCubic d hcop i PM3
  let : IsCyclic D := isCyclic_of_prime_card hcard
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic D)
  have hord : orderOf a = 3 := (orderOf_eq_card_of_zpowers_eq_top ha).trans hcard
  have hDM : D ≤ M := planeCubic_le_M M (d.plane i) PM3
  let aM : M := ⟨a, hDM a.property⟩
  have hordM : orderOf aM = 3 := by
    have he := orderOf_injective (inclusion hDM) (inclusion_injective hDM) a
    exact he.trans hord
  have hgen : zpowers (a : G) = D := by
    have he := congrArg (Subgroup.map D.subtype) ha
    rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at he
    exact he
  refine ⟨aM, a.property, hgen, hordM, ?_⟩
  have hDi : IsPGroup 3 (D.subgroupOf M) :=
    (show IsPGroup 3 D from PM3.isPGroup'.map _).comap_subtype
  have hker : Nat.Coprime 3 (Nat.card d.actor.ker) := by rwa [d.ker_actor]
  have hinj := injective_comp_subtype_of_coprime_ker d.actor hker (D.subgroupOf M) hDi
  intro he
  have hone : (⟨aM, a.property⟩ : D.subgroupOf M) = 1 := hinj (by
    change d.actor aM = d.actor 1
    simpa using he)
  have haone : aM = 1 := congrArg Subtype.val hone
  rw [haone, orderOf_one] at hordM
  omega

/-- The marked lower constituent has precisely its named fixed plane. -/
theorem fixedPlane_planeCubic [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G)) :
    fixedPlane V (planeCubic M (d.plane i) PM3) = d.plane i := by
  obtain ⟨a, ha, hgen, hord, hne⟩ := planeCubic_generator d hcop i PM3
  have hpow : d.actor a ^ 3 = 1 := by
    rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  have hpoint : d.actor a ∈ pointwise (orthogonalCoordinatePlane i) := by
    have h : a ∈ (centralizer (d.plane i : Set G)).subgroupOf M :=
      planeCubic_le_centralizer M (d.plane i) PM3 ha
    rwa [d.plane_eq_map, d.centralizer_map_eq_comap] at h
  rw [d.fixedPlane_eq_map (planeCubic_le_M M (d.plane i) PM3)]
  conv_rhs => rw [d.plane_eq_map]
  congr 1
  ext w
  constructor
  · intro hw
    exact (cubic_plane_certificate i (d.actor a) hpow hne hpoint w).mp
      (hw (d.actor a) ⟨a, ha, rfl⟩)
  · intro hw b hb
    obtain ⟨m, hm, rfl⟩ := hb
    have h : m ∈ (centralizer (d.plane i : Set G)).subgroupOf M :=
      planeCubic_le_centralizer M (d.plane i) PM3 hm
    rw [d.plane_eq_map, d.centralizer_map_eq_comap] at h
    exact h w hw

/-- The two-core definition supplies precisely the needed relative normalization. -/
theorem pairI_normalizes_pairP (Z ZS : Subgroup G) (g : G) :
    pairI Z ZS g ≤ normalizer (pairP Z ZS g : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

/-- The denominator in P/V is normal inside P, by the actual center equality. -/
theorem normal_lower_of_center {P : Subgroup G}
    (hcenter : V = (center P).map P.subtype) : (V.subgroupOf P).Normal := by
  rw [hcenter, subgroupOf_map_subtype_eq]
  infer_instance

/-- The center equality makes every element of P centralize V. -/
theorem le_centralizer_lower_of_center {P : Subgroup G}
    (hcenter : V = (center P).map P.subtype) : P ≤ centralizer (V : Set G) := by
  intro p hp v hv
  rw [hcenter] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  exact congrArg Subtype.val (mem_center_iff.mp hv ⟨p, hp⟩).symm

namespace NaturalQuotientPair
variable {d : NaturalOrthogonalAction M V}
  {I P : Subgroup G} {hIM : I ≤ M} {hIP : I ≤ normalizer (P : Set G)}
  [(V.subgroupOf P).Normal]
  (r : NaturalQuotientPair d I P hIM hIP)

/-- Nontrivial cubic projections are fixed-point-free on the natural planes. -/
theorem cubic_constituents_fixed_point_free (a : I) (hpow : a ^ 3 = 1)
    (hfirst : (r.factors (imageActor d I hIM a)).1 ≠ 1)
    (hsecond : (r.factors (imageActor d I hIM a)).2 ≠ 1) :
    (∀ w : OrthogonalPlaneVector,
      (r.factors (imageActor d I hIM a)).1 • w = w → w = 1) ∧
    (∀ w : OrthogonalPlaneVector,
      (r.factors (imageActor d I hIM a)).2 • w = w → w = 1) := by
  have he : (r.factors (imageActor d I hIM a)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hpow, map_one, map_one]
  exact ⟨cubic_natural_certificate _ (congrArg Prod.fst he) hfirst,
    cubic_natural_certificate _ (congrArg Prod.snd he) hsecond⟩

/-- Conditional quotient reduction: the separate projection calculation is
required explicitly and is not asserted as a source conclusion here. -/
theorem centralizer_le_lower_of_cubic_projections {D : Subgroup G}
    (a : I) (haD : (a : G) ∈ D) (hpow : a ^ 3 = 1)
    (hfirst : (r.factors (imageActor d I hIM a)).1 ≠ 1)
    (hsecond : (r.factors (imageActor d I hIM a)).2 ≠ 1) :
    P ⊓ centralizer (D : Set G) ≤ V := by
  obtain ⟨hf, hs⟩ := r.cubic_constituents_fixed_point_free a hpow hfirst hsecond
  intro p hp
  exact r.mem_lower_of_commute a hf hs ⟨p, hp.1⟩ (hp.2 a haD)

/-- Once the two nontrivial projections have been proved, the quotient
reduction and the marked lower action identify the whole kernel centralizer. -/
theorem centralizer_eq_plane_of_cubic_projections [Finite G]
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (hVP : V ≤ P) (a : I) (haD : (a : G) ∈ planeCubic M (d.plane i) PM3)
    (hpow : a ^ 3 = 1)
    (hfirst : (r.factors (imageActor d I hIM a)).1 ≠ 1)
    (hsecond : (r.factors (imageActor d I hIM a)).2 ≠ 1) :
    P ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G) = d.plane i := by
  apply le_antisymm
  · intro p hp
    apply (fixedPlane_planeCubic d hcop i PM3).le
    exact ⟨r.centralizer_le_lower_of_cubic_projections a haD hpow hfirst hsecond hp, hp.2⟩
  · exact le_inf ((d.plane_le i).trans hVP)
      (le_centralizer_iff.mp (planeCubic_le_centralizer M (d.plane i) PM3))

end NaturalQuotientPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
