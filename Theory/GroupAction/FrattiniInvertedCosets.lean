module

public import Theory.GroupTheory.FrattiniInvolutionObstruction
public import Theory.ElementaryAbelian.TenPointConfiguration

/-!
# Bounding cosets with inverted lifts

Let D be an elementary abelian subgroup equal to both the Frattini subgroup
and the second center of a finite group. An automorphism fixing D pointwise
cannot invert lifts of ten nonidentity cosets when the quotient has order
sixteen and is elementary abelian.

Inversion of one lift determines inversion modulo the center for every
lift. The ten-point configuration then supplies generators and their
products with a fixed nonzero generator. Inverting these products forces
that generator to commute with all generators modulo the center, placing
it in D and giving a contradiction.

This is the automorphism version of the Frattini involution obstruction,
used for the ten outer cosets in Thompson VI, printed p.630; the underlying
configuration is Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 4, printed p.675.
-/

open Subgroup
namespace Theory.GroupAction

/-- Inversion of a lift propagates modulo the center throughout its coset. -/
public theorem inverts_mod_center_of_inverted_coset
    {G : Type*} [Group G] (D : Subgroup G) [D.Normal]
    [IsElementaryAbelian 2 D] (hD : D ≤ Subgroup.upperCentralSeries G 2)
    (e : MulAut G) (hfix : ∀ d ∈ D, e d = d)
    (x b : G) (hb : e b = b⁻¹)
    (hcoset : QuotientGroup.mk' D x = QuotientGroup.mk' D b) :
    QuotientGroup.mk' (center G) (e x) = (QuotientGroup.mk' (center G) x)⁻¹ := by
  let q := QuotientGroup.mk' (center G)
  let d := x / b
  have hd : d ∈ D := QuotientGroup.eq_iff_div_mem.mp hcoset
  have hdcentral : q d ∈ center (G ⧸ center G) := by
    have hh := hD hd
    rw [← Subgroup.comap_upperCentralSeries_quotient_center 1, Subgroup.upperCentralSeries_one] at hh
    exact hh
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) d hd)
  have hsplit : x = d * b := by simp [d]
  change q (e x) = (q x)⁻¹
  rw [hsplit, map_mul, hfix d hd, hb, map_mul, map_inv, map_mul, mul_inv_rev,
    ← map_inv q d, hdi]
  exact (mem_center_iff.mp hdcentral (q b)⁻¹).symm

/-- A generating family of inverted cosets has a product admitting no inverted lift. -/
public theorem exists_product_without_inverted_lift
    {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
    (hPhi : D = frattini G) (hUpper : D = Subgroup.upperCentralSeries G 2)
    (e : MulAut G) (hfix : ∀ d ∈ D, e d = d)
    {I : Type*} (v : I → G ⧸ D)
    (hgen : closure (Set.range v) = ⊤)
    (hlift : ∀ i, ∃ a : G, e a = a⁻¹ ∧ QuotientGroup.mk' D a = v i)
    (i : I) (hi : v i ≠ 1) :
    ∃ j, ¬ ∃ b : G, e b = b⁻¹ ∧ QuotientGroup.mk' D b = v i * v j := by
  classical
  choose a ha hqa using hlift
  let q := QuotientGroup.mk' (center G)
  have hmap : (closure (Set.range a)).map (QuotientGroup.mk' D) = ⊤ := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    simpa only [Function.comp_def, hqa] using hgen
  have hsup : closure (Set.range a) ⊔ frattini G = ⊤ := by
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' D)) hmap
    simpa [hPhi, sup_comm] using hh
  have hgena : closure (Set.range a) = ⊤ := frattini_nongenerating hsup
  by_contra! hall
  let C := (centralizer ({q (a i)} : Set (G ⧸ center G))).comap q
  have hC : closure (Set.range a) ≤ C := by
    apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨b, hb, hqb⟩ := hall j
    have hprod := inverts_mod_center_of_inverted_coset D hUpper.le e hfix
      (a i * a j) b hb (by rw [map_mul, hqa, hqa, hqb])
    change q (e (a i * a j)) = (q (a i * a j))⁻¹ at hprod
    simp only [map_mul, ha, map_inv, mul_inv_rev] at hprod
    have hc : q (a j) * q (a i) = q (a i) * q (a j) := by
      simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv hprod
    exact mem_centralizer_singleton_iff.mpr hc
  have hCtop : C = ⊤ := top_unique (hgena ▸ hC)
  have hai : a i ∈ D := by
    rw [hUpper, ← Subgroup.comap_upperCentralSeries_quotient_center 1, Subgroup.upperCentralSeries_one]
    change q (a i) ∈ center (G ⧸ center G)
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center G) y
    have hx : x ∈ C := hCtop ▸ mem_top x
    exact mem_centralizer_singleton_iff.mp hx
  exact hi ((hqa i).symm.trans ((QuotientGroup.eq_one_iff (N := D) _).mpr hai))

/-- Fewer than ten nonidentity Frattini cosets admit inverted lifts. -/
public theorem nonidentity_inverted_cosets_ncard_lt_ten
    {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
    [IsElementaryAbelian 2 (G ⧸ D)]
    (hPhi : D = frattini G) (hUpper : D = Subgroup.upperCentralSeries G 2)
    (hcard : Nat.card (G ⧸ D) = 16)
    (e : MulAut G) (hfix : ∀ d ∈ D, e d = d) :
    {x : G ⧸ D | x ≠ 1 ∧ ∃ a : G, e a = a⁻¹ ∧ QuotientGroup.mk' D a = x}.ncard < 10 := by
  classical
  let T : Set (G ⧸ D) :=
    {x | x ≠ 1 ∧ ∃ a : G, e a = a⁻¹ ∧ QuotientGroup.mk' D a = x}
  change T.ncard < 10
  by_contra! hlarge
  obtain ⟨v, hgen, hv, hprod⟩ :=
    Theory.ElementaryAbelian.exists_generating_configuration_of_ten_le_ncard
      hcard T (fun hh => hh.1 rfl) hlarge
  obtain ⟨j, hj⟩ := exists_product_without_inverted_lift D hPhi hUpper e hfix
    v hgen (fun i => (hv i).2) 0 (hv 0).1
  by_cases hj0 : j = 0
  · subst j
    apply hj
    refine ⟨1, by simp, ?_⟩
    rw [map_one, ← pow_two]
    exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ D)) (v 0)).symm
  · exact hj (hprod j hj0).2
end Theory.GroupAction
