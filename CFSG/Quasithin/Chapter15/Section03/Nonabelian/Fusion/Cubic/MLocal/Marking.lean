module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.ModelCalculations
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.ThreePart

/-!
# Marked cubic Sylow groups and the source product

The natural action proves that Z_S meets the definite plane V₁ in exactly
two elements. With V = ⟨Ω₁(Z(T))^M⟩ it also proves |Ω₁(Z(T))| = 2, giving
actual generators z and v. The earlier centralizer control and the three-part
calculation construct both P_M,3 and P_v with the same ambient image.

Since T lies in H = C_G(Z), it normalizes U = ⟨Z_S^H⟩. Consequently the
join U ∨ C_T(V) is precisely the set product U C_T(V). Its elements act
on V like their U-factor. Thus the source transvection calculation can
exclude an element by its actual fixed subgroup, independently of a
choice of quotient model. The fixed-cardinality hypotheses of that last
helper remain to be supplied by the P/V and orthogonal action calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the setup
of 15.3.60 and the proof of 15.3.61(1), printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
variable {G : Type*} [Group G] {M V : Subgroup G}
open OrthogonalGeometry

theorem marked_intersection_eq_fixedPlane (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (i : OrthogonalPlaneIndex) :
    fixedPlane V (planeStabilizer T (d.plane i)) ⊓ d.plane i =
      fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) := by
  change (V ⊓ centralizer _) ⊓ d.plane i = d.plane i ⊓ centralizer _
  rw [inf_right_comm, inf_eq_right.mpr (d.plane_le i)]

theorem card_marked_intersection [Finite G] (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex) :
    Nat.card (fixedPlane V (planeStabilizer T (d.plane i)) ⊓ d.plane i : Subgroup G) = 2 := by
  rw [marked_intersection_eq_fixedPlane, d.card_plane_fixed (X := planeStabilizer T (d.plane i)) (inf_le_left.trans hTM),
    d.image_planeStabilizer]
  exact plane_sylow_fixed_line_card (d.sylowImage T hTM) i

theorem source_marked_involutions [Finite G] (d : NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (Z : Subgroup G) (hZ : Nat.card Z = 2) :
    ∃ z v : G, orderOf z = 2 ∧ orderOf v = 2 ∧ zpowers z = Z ∧
      zpowers v = fixedPlane V (planeStabilizer T (d.plane i)) ⊓ d.plane i := by
  exact exists_marked_involutions Z _ _ hZ (card_marked_intersection d T hTM i)

open scoped Pointwise in
theorem closureU_sup_centralizer_eq_product (Z ZS V : Subgroup G) (T : Subgroup G)
    (hTH : T ≤ centralizerH Z) :
    ((closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)) : Subgroup G) : Set G) =
      (closureU Z ZS : Set G) * (T ⊓ centralizer (V : Set G) : Subgroup G) := by
  apply coe_mul_of_right_le_normalizer_left
  exact (inf_le_left.trans hTH).trans (H_normalizes_closureU Z ZS)

/-- The ambient image of the chosen source Sylow subgroup of C_M(V₁). -/
def planeCubic (M V₁ : Subgroup G)
    (P : Sylow 3 (M ⊓ centralizer (V₁ : Set G) : Subgroup G)) : Subgroup G :=
  (P : Subgroup (M ⊓ centralizer (V₁ : Set G) : Subgroup G)).map
    (M ⊓ centralizer (V₁ : Set G)).subtype

theorem planeCubic_le_M (M V₁ : Subgroup G)
    (P : Sylow 3 (M ⊓ centralizer (V₁ : Set G) : Subgroup G)) : planeCubic M V₁ P ≤ M :=
  (map_subtype_le _).trans inf_le_left

theorem planeCubic_le_centralizer (M V₁ : Subgroup G)
    (P : Sylow 3 (M ⊓ centralizer (V₁ : Set G) : Subgroup G)) :
    planeCubic M V₁ P ≤ centralizer (V₁ : Set G) :=
  (map_subtype_le _).trans inf_le_right

theorem card_planeCubic [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (P : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G)) :
    Nat.card (planeCubic M (d.plane i) P) = 3 := by
  rw [planeCubic, card_map_of_injective (M ⊓ centralizer (d.plane i : Set G)).subtype_injective]
  exact sylow_three_card_plane d hcop i P

/-- The chosen plane cubic is Sylow in the full involution centralizer.
The three-part calculation is proved from the marked action and 15.3.49(4). -/
theorem exists_sylow_involution_image [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (P : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (v : G) (hv : v ∈ d.plane i) (hne : v ≠ 1)
    (hcontrol : centralizer ({v} : Set G) ≤ M) :
    ∃ Pv : Sylow 3 (centralizer ({v} : Set G)),
      (Pv : Subgroup (centralizer ({v} : Set G))).map
        (centralizer ({v} : Set G)).subtype = planeCubic M (d.plane i) P := by
  let D := planeCubic M (d.plane i) P
  let C := centralizer ({v} : Set G)
  have hDC : D ≤ C := (planeCubic_le_centralizer M (d.plane i) P).trans
    (centralizer_le (Set.singleton_subset_iff.mpr hv))
  have hcard : Nat.card D = 3 := card_planeCubic d hcop i P
  have hD : IsPGroup 3 D := P.isPGroup'.map _
  have hDi : IsPGroup 3 (D.subgroupOf C) := hD.comap_subtype
  obtain ⟨Pv, hPv⟩ := hDi.exists_le_sylow
  have hPvcard : Nat.card Pv = 3 := by
    have h : ∀ Q : Sylow 3 (M ⊓ C : Subgroup G), Nat.card Q = 3 :=
      fun Q => sylow_three_card_plane_involution d hcop i v hv hne Q
    rw [inf_eq_right.mpr hcontrol] at h
    exact h Pv
  have he : D.subgroupOf C = (Pv : Subgroup C) := eq_of_le_of_card_ge hPv (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv, hcard, hPvcard])
  refine ⟨Pv, ?_⟩
  rw [← he, map_subgroupOf_eq_of_le hDC]

/-- Choose the two Sylow three-witnesses with exactly the same ambient image. -/
theorem exists_cubic_sylow_pair [Finite G] (d : NaturalOrthogonalAction M V)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex) (v : G) (hv : v ∈ d.plane i) (hne : v ≠ 1)
    (hcontrol : centralizer ({v} : Set G) ≤ M) :
    ∃ (P : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
      (Pv : Sylow 3 (centralizer ({v} : Set G))),
      Nat.card (planeCubic M (d.plane i) P) = 3 ∧
      (Pv : Subgroup (centralizer ({v} : Set G))).map
        (centralizer ({v} : Set G)).subtype = planeCubic M (d.plane i) P := by
  let P : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G) := Sylow.nonempty.some
  obtain ⟨Pv, hPv⟩ := exists_sylow_involution_image d hcop i P v hv hne hcontrol
  exact ⟨P, Pv, card_planeCubic d hcop i P, hPv⟩

/-- Construct both source generators and both Sylow three-groups from the
marked earlier action and the earlier involution-centralizer control. -/
theorem exists_source_marked_sylows [Finite G]
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (d : NaturalOrthogonalAction M (localModule T M)) (i : OrthogonalPlaneIndex)
    (hcop : Nat.Coprime 3
      (Nat.card ((centralizer (localModule T M : Set G)).subgroupOf M)))
    (hcontrol : centralizer
      (fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) : Set G) ≤ M) :
    ∃ (z v : G)
      (P : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
      (Pv : Sylow 3 (centralizer ({v} : Set G))),
      orderOf z = 2 ∧ orderOf v = 2 ∧ zpowers z = centralInvolutions T ∧
      zpowers v = fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ⊓ d.plane i ∧
      Nat.card (planeCubic M (d.plane i) P) = 3 ∧
      (Pv : Subgroup (centralizer ({v} : Set G))).map
        (centralizer ({v} : Set G)).subtype = planeCubic M (d.plane i) P := by
  have hZ : Nat.card (centralInvolutions T) = 2 := by
    rw [NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane T hTM d,
      d.card_fixedPlane hTM]
    exact sylow_fixedVectors_card (d.sylowImage T hTM)
  obtain ⟨z, v, hz, hv, hzgen, hvgen⟩ := source_marked_involutions d T hTM i _ hZ
  have hvplane : v ∈ d.plane i := by
    have h := mem_zpowers v
    rw [hvgen] at h
    exact h.2
  have hvne : v ≠ 1 := by intro h; simp only [h, orderOf_one] at hv; omega
  have hcentralizer : centralizer ({v} : Set G) =
      centralizer (fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) : Set G) := by
    calc
      centralizer ({v} : Set G) = centralizer (zpowers v : Set G) := by
        rw [zpowers_eq_closure, centralizer_closure]
      _ = _ := by rw [hvgen, marked_intersection_eq_fixedPlane]
  obtain ⟨P, Pv, hP, hPv⟩ := exists_cubic_sylow_pair d hcop i v hvplane hvne
    (hcentralizer ▸ hcontrol)
  exact ⟨z, v, P, Pv, hz, hv, hzgen, hvgen, hP, hPv⟩

/-- Multiplication by a pointwise vector centralizer does not change the fixed subgroup. -/
theorem fixedPlane_mul_centralizer (V : Subgroup G) (u c : G)
    (hc : c ∈ centralizer (V : Set G)) :
    fixedPlane V (zpowers (u * c)) = fixedPlane V (zpowers u) := by
  ext w
  simp only [fixedPlane, zpowers_eq_closure, centralizer_closure, mem_inf,
    mem_centralizer_singleton_iff]
  apply and_congr_right
  intro hw
  have he : c * w = w * c := (hc w hw).symm
  rw [← mul_assoc w u c, mul_assoc u c w, he, ← mul_assoc u w c, mul_right_cancel_iff]

open scoped Pointwise in
/-- The fixed-space calculation excludes membership in the source product. -/
theorem not_mem_source_product_of_fixed_card (Z ZS V : Subgroup G) (T : Subgroup G)
    (hTH : T ≤ centralizerH Z)
    (hU : ∀ u ∈ closureU Z ZS, Nat.card (fixedPlane V (zpowers u)) ≠ 8)
    (t : G) (ht : Nat.card (fixedPlane V (zpowers t)) = 8) :
    t ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)) := by
  intro hm
  have hp : t ∈ (closureU Z ZS : Set G) * (T ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [← closureU_sup_centralizer_eq_product Z ZS V T hTH]
    exact hm
  obtain ⟨u, hu, c, hc, rfl⟩ := hp
  rw [fixedPlane_mul_centralizer V u c hc.2] at ht
  exact hU u hu ht

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
