module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Setup

/-!
# Deductions from the two orthogonal orbits

The fixed line in the definite plane supplies a nonsingular vector whose full
centralizer is in `M`, by 15.3.45(3). The actual relative Sylow subgroup has
index two in `T`. Thus the two local orbits cannot fuse in `G`. Transport along
the nonsingular orbit gives every required centralizer bound, and the quadratic
lemmas give singular intersections, `r(G,V) > 1`, and `N_G(Z_S) ≤ M`.

The orbit and Sylow calculations remain explicit intermediate inputs. They
must be constructed from the full natural action; they are not earlier-source
conclusions. No global fusion-separation premise occurs here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.46(1–3,5),
printed p.1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]
  {T : Sylow 2 G} {M V P : Subgroup G} [IsElementaryAbelian 2 V]
  {Q : QuadraticForm (ZMod 2) (Additive V)}

/-- The chosen nonsingular vector lies in the actual fixed subgroup `Z_S`. -/
theorem OrthogonalFusionCalculations.vector_mem_fixedPlane
    (c : OrthogonalFusionCalculations T M V P Q) (hPV : P ≤ V) :
    (c.v : G) ∈ fixedPlane V (planeStabilizer T P) := by
  have hv : (c.v : G) ∈ fixedPlane P (planeStabilizer T P) :=
    c.fixed_line.symm ▸ mem_zpowers _
  exact ⟨hPV hv.1, hv.2⟩

/-- Definiteness ties the orbit representative to the quadratic form. -/
theorem OrthogonalFusionCalculations.vector_nonsingular
    (c : OrthogonalFusionCalculations T M V P Q) (hP : IsDefinitePlane Q P) :
    Q (Additive.ofMul c.v) ≠ 0 := by
  have hv : (c.v : G) ∈ fixedPlane P (planeStabilizer T P) :=
    c.fixed_line.symm ▸ mem_zpowers _
  exact hP.2.2 c.v hv.1 c.v_ne_one

/-- 15.3.45(3) bounds the full centralizer of the nonsingular representative. -/
theorem OrthogonalFusionCalculations.vector_centralizer_le
    (c : OrthogonalFusionCalculations T M V P Q)
    (h : EarlierFusionInputs T M V P) :
    centralizer ({(c.v : G)} : Set G) ≤ M := by
  have hc := h.plane_fixed_centralizer
  rw [c.fixed_line, Subgroup.zpowers_eq_closure, centralizer_closure] at hc
  exact hc

/-- Relative Sylow order, rather than an abstract actor order, separates the orbits. -/
theorem OrthogonalFusionCalculations.sylow_card_lt [Finite G]
    (c : OrthogonalFusionCalculations T M V P Q) :
    Nat.card c.centralizer_sylow < Nat.card T := by
  have hc : Nat.card c.centralizer_sylow = Nat.card (planeStabilizer T P) := by
    rw [← c.sylow_image, card_map_of_injective (centralizer ({(c.v : G)} : Set G)).subtype_injective]
  have hST : planeStabilizer T P ≤ (T : Subgroup G) := inf_le_left
  have hmul := ((planeStabilizer T P).subgroupOf T).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hST).toEquiv] at hmul
  change Nat.card (planeStabilizer T P) * (planeStabilizer T P).relIndex T =
    Nat.card T at hmul
  rw [c.stabilizer_index] at hmul
  have hpos := Nat.card_pos (α := planeStabilizer T P)
  omega

/-- The local calculations prove global fusion control by distinct Sylow-centrality. -/
theorem controlsFusion_of_orthogonal_calculations [Finite G]
    (c : OrthogonalFusionCalculations T M V P Q)
    (h : EarlierFusionInputs T M V P) :
    ∀ x ∈ V, ∀ g : G, MulAut.conj g x ∈ V →
      ConjugateBy M x (MulAut.conj g x) := by
  apply controlsFusion_of_two_orbits M V T (c.z : G) (c.v : G)
    ?_ c.centralizer_sylow c.sylow_card_lt
  · intro x hx hx1
    let u : V := ⟨x, hx⟩
    have hu : u ≠ 1 := fun he => hx1 (congrArg Subtype.val he)
    by_cases hq : Q (Additive.ofMul u) = 0
    · exact Or.inl (c.singular_orbit u hu hq)
    · exact Or.inr (c.nonsingular_orbit u hq)
  · have hz := h.central_fixed ▸ c.z_central
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hz.2 t ht)

/-- The representative's full-centralizer bound transports to all nonsingular vectors. -/
theorem nonsingular_centralizer_le_of_orthogonal_calculations
    (c : OrthogonalFusionCalculations T M V P Q)
    (h : EarlierFusionInputs T M V P) (v : V) (hv : Q (Additive.ofMul v) ≠ 0) :
    centralizer ({(v : G)} : Set G) ≤ M :=
  centralizer_le_of_conjugateBy (c.nonsingular_orbit v hv) (c.vector_centralizer_le h)

/-- The actual fixed plane contains a nonsingular vector, so its normalizer is local. -/
theorem normalizer_fixedPlane_le_of_orthogonal_calculations [Finite G]
    (c : OrthogonalFusionCalculations T M V P Q)
    (h : EarlierFusionInputs T M V P) (hP : IsDefinitePlane Q P) :
    normalizer (fixedPlane V (planeStabilizer T P) : Set G) ≤ M := by
  apply normalizer_le_of_not_totallySingular Q h.normalizer_eq
    (controlsFusion_of_orthogonal_calculations c h)
    (nonsingular_centralizer_le_of_orthogonal_calculations c h) inf_le_left
  intro hs
  exact c.vector_nonsingular hP (hs.2 c.v (c.vector_mem_fixedPlane hP.1))

end CFSG.Quasithin.Chapter15.Section03.FusionCore
