module

public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionData
public import Theory.SpecificGroups.ReeTwo.OrbitFrameAlgebra
public import Theory.SpecificGroups.ReeTwo.OrbitCommutatorRigidity
public import Theory.SpecificGroups.ReeTwo.SemilinearOrbitTransport

/-!
# Intrinsic nonvanishing and assembly of the orbit commutators

Orbit generation rules out commuting residual images in the central quotient:
otherwise the residual derived subgroup, of order 32, would lie in the center,
of order 2. The fifth-orbit relation reduces this obstruction to the first four
orbit elements. Combined with binary coordinate rigidity, this proves the Ree
commutator table from the fifth-orbit relation and faithful, spanning binary
tail coordinates. The normalized symmetry supplies the intrinsic action
transport identities.

The transport interface is derived from the extension data and the fifth-orbit
relation. Sources: Thompson VI, pp.629–630; Parrott (1972),
pp.672–674; Shinoda (1975), pp.81–82.
-/

@[expose] public section
namespace ReeTwo
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {K A : Type*} [Group K] [Group A] [Finite K] [Finite A]
variable {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
omit [Finite A] in
/-- Some two actor images fail to commute modulo the center, since they generate
the residual and its derived subgroup is larger than the center. -/
theorem SemilinearExtensionData.not_all_actor_images_commute (h : SemilinearExtensionData ρ R t z b σ) :
    ¬ ∀ a a' : A, Commute (QuotientGroup.mk' (center K) (ρ a b))
      (QuotientGroup.mk' (center K) (ρ a' b)) := by
  intro hall
  let q := QuotientGroup.mk' (center K)
  have hR : R.map q = closure (Set.range (fun a : A => q (ρ a b))) := by
    calc
      R.map q = (closure (Set.range (fun a : A => ρ a (b : K)))).map q :=
        congrArg (fun S : Subgroup K => S.map q) h.seed_generates.symm
      _ = _ := by rw [MonoidHom.map_closure, ← Set.range_comp']
  have hc : IsMulCommutative (R.map q) := by
    rw [hR]
    apply isMulCommutative_closure
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    exact hall a a'
  let _ := hc
  have hD : (commutator R).map R.subtype ≤ center K := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact congrArg Subtype.val (mul_comm (⟨q x, mem_map_of_mem q hx⟩ : R.map q)
      (⟨q y, mem_map_of_mem q hy⟩ : R.map q))
  have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hD)
    (Subgroup.inclusion_injective hD)
  rw [h.derived_card, h.center_eq, h.center_card] at hcard
  omega

omit [Finite K] [Finite A] in
/-- The ambient derived subgroup is central after quotienting by the center. -/
theorem SemilinearExtensionData.derived_image_mem_center
    (h : SemilinearExtensionData ρ R t z b σ) {x : K} (hx : x ∈ commutator K) :
    QuotientGroup.mk' (center K) x ∈ center (K ⧸ center K) := by
  let q := QuotientGroup.mk' (center K)
  apply mem_center_iff.mpr
  intro w
  induction w using QuotientGroup.induction_on with | H w =>
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅q w, q x⁆ = 1
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [h.center_eq, ← h.derived_commutator, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (mem_top w) (h.derived_eq.symm ▸ hx)

/-- The fifth-orbit relation makes the first four images detect noncommutation
of the whole residual. -/
theorem SemilinearExtensionData.not_all_four_orbit_images_commute
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1)
    (hrel : ρ (g ^ 4) b / (ρ (g ^ 0) b * ρ (g ^ 1) b *
      ρ (g ^ 2) b * ρ (g ^ 3) b) ∈ commutator K) :
    ¬ ∀ i j : Fin 4, Commute
      (QuotientGroup.mk' (center K) (ρ (g ^ i.val) b))
      (QuotientGroup.mk' (center K) (ρ (g ^ j.val) b)) := by
  classical
  intro hall
  let q := QuotientGroup.mk' (center K)
  let f (n : ℕ) := q (ρ (g ^ n) b)
  have hz : f 4 / (f 0 * f 1 * f 2 * f 3) ∈ center (K ⧸ center K) := by
    simpa only [map_div, map_mul] using h.derived_image_mem_center hrel
  have h4 (i : Fin 4) : Commute (f 4) (f i.val) := by
    have hp : Commute (f 0 * f 1 * f 2 * f 3) (f i.val) :=
      (((hall 0 i).mul_left (hall 1 i)).mul_left (hall 2 i)).mul_left (hall 3 i)
    have hw : Commute (f 4 / (f 0 * f 1 * f 2 * f 3)) (f i.val) :=
      (mem_center_iff.mp hz (f i.val)).symm
    simpa only [div_mul_cancel] using hw.mul_left hp
  have h5 (i j : Fin 5) : Commute (f i.val) (f j.val) := by
    by_cases hi : i.val < 4
    · by_cases hj : j.val < 4
      · exact hall ⟨i.val, hi⟩ ⟨j.val, hj⟩
      · have hj4 : j.val = 4 := by omega
        rw [hj4]
        exact (h4 ⟨i.val, hi⟩).symm
    · have hi4 : i.val = 4 := by omega
      rw [hi4]
      by_cases hj : j.val < 4
      · exact h4 ⟨j.val, hj⟩
      · have hj4 : j.val = 4 := by omega
        rw [hj4]
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hgen := zpowers_eq_top_of_prime_card h.actor_card hg
  have ho : orderOf g = 5 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hgen, h.actor_card]
  have hex (a : A) : ∃ i : Fin 5, g ^ i.val = a := by
    have hm : a ∈ zpowers g := by rw [hgen]; exact mem_top _
    have hn := (isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp hm
    rw [ho] at hn
    obtain ⟨n, hn, ha⟩ := Finset.mem_image.mp hn
    exact ⟨⟨n, Finset.mem_range.mp hn⟩, ha⟩
  apply h.not_all_actor_images_commute
  intro a a'
  obtain ⟨i, rfl⟩ := hex a
  obtain ⟨j, rfl⟩ := hex a'
  exact h5 i j

/-- Assembly with the intrinsic transport identities kept explicit. The three
tail-coordinate hypotheses supply the fifth-orbit relation, injectivity, and
the first commutator's coordinates. The transport identities are a separate
obligation, rather than a commutator-table assumption. -/
theorem SemilinearExtensionData.orbitCommutatorCoordinates_of_transport
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1) :
    let q := QuotientGroup.mk' (center K)
    let B := fun n : ℕ => ρ (g ^ n) (b : K)
    let u := fun i : Fin 4 => q (B i.val)
    let P := binaryWord4 (fun i => rightComm (u i) (q t))
    B 4 / (B 0 * B 1 * B 2 * B 3) ∈ commutator K →
    Function.Injective P →
    (∀ x : K, x ∈ commutator K → ∃ e : OrbitBits, q x = P e) →
    OrbitCommutatorTransport u (q t) →
    OrbitCommutatorCoordinates u (q t) := by
  intro q B u P hrel hinj hspan htransport
  have hm : rightComm (B 0) (B 1) ∈ commutator K := by
    simpa [rightComm, commutatorElement_def, _root_.commutator_def] using
      (Subgroup.commutator_mem_commutator (mem_top (B 0)⁻¹) (mem_top (B 1)⁻¹))
  have hcoord : ∃ e : OrbitBits, rightComm (u 0) (u 1) = P e := by
    obtain ⟨e, he⟩ := hspan _ hm
    exact ⟨e, by simpa only [u, Fin.val_zero, Fin.val_one, rightComm, map_mul, map_inv] using he⟩
  rcases htransport.coordinates_or_commute hinj hcoord with hc | hc
  · exact False.elim (h.not_all_four_orbit_images_commute g hg hrel hc)
  · exact hc

/-- The fifth-orbit relation and faithful, spanning tail coordinates determine
all six orbit commutators via the intrinsic normalized symmetry. -/
theorem SemilinearExtensionData.orbitCommutatorCoordinates_of_tailCoordinates
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1) :
    let q := QuotientGroup.mk' (center K)
    let B := fun n : ℕ => ρ (g ^ n) (b : K)
    let u := fun i : Fin 4 => q (B i.val)
    let P := binaryWord4 (fun i => rightComm (u i) (q t))
    B 4 / (B 0 * B 1 * B 2 * B 3) ∈ commutator K →
    Function.Injective P →
    (∀ x : K, x ∈ commutator K → ∃ e : OrbitBits, q x = P e) →
    OrbitCommutatorCoordinates u (q t) := by
  intro q B u P hrel hinj hspan
  obtain ⟨htransport⟩ := h.orbitCommutatorTransport_of_fifthRelation g hg hrel
  exact h.orbitCommutatorCoordinates_of_transport g hg hrel hinj hspan htransport
end ReeTwo
