module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level2
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level3
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level4
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level5

/-!
# The ambient two-part bound from Rudvalis orbital rigidity

The stabilizers of the first k letters have successive orbit sizes
4060, 1755, 1024, 5, and 4. The existing forest and word representatives
prove the lower bounds; the checked orbital color refinements prove the
upper bounds. Fixing all five letters forces the identity. Orbit-stabilizer
therefore gives the required nondivisibility by 2^15.

This argument uses the certified orbital and its rigidity directly. It does
not import the unfinished Schreier-generator coverage or model-order proof.
Only the nondivisibility consequence is exported for the Sylow calculation.

Source: the preserved ATLAS degree-4060 action, documented in
`Model.PermutationData`, and GLS3 Table 5.3r, printed p.279. The quasithin
application is Aschbacher--Smith, printed p.511 (PDF p.528), citing [Asc86b].
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
open MulAction OuterNormalizer OuterNormalizer.RigidityCertificate OrderCertificate PrimitiveData

private def fixed (k : ℕ) : Subgroup Model where
  carrier := {g | ∀ x : Fin 4060, x.val < k → g • x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh x hx
    rw [mul_smul, hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    exact inv_smul_eq_iff.mpr (hg x hx).symm

private theorem mem_fixed (g : Model) (k : ℕ) :
    g ∈ fixed k ↔ ∀ x : Fin 4060, x.val < k → g • x = x := Iff.rfl

private def nextEquiv (k : Fin 4060) : stabilizer (fixed k.val) k ≃* fixed (k.val + 1) where
  toFun g := ⟨g.val.val, by
    intro x hx
    by_cases hlt : x.val < k.val
    · exact g.val.property x hlt
    · have he : x = k := Fin.ext (by omega)
      subst x
      exact g.property⟩
  invFun g := ⟨⟨g.val, fun x hx => g.property x (by omega)⟩,
    g.property k (by omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem card_step (k : Fin 4060) :
    Nat.card (fixed k.val) =
      Nat.card (orbit (fixed k.val) k) * Nat.card (fixed (k.val + 1)) := by
  have hi : Nat.card (orbit (fixed k.val) k) = (stabilizer (fixed k.val) k).index :=
    Nat.card_congr (orbitEquivQuotientStabilizer (fixed k.val) k)
  rw [hi, ← Nat.card_congr (nextEquiv k).toEquiv, Nat.mul_comm]
  exact (stabilizer (fixed k.val) k).card_mul_index.symm

private theorem model_relation (g : Model) : g.val ∈ relationAut :=
  model_le_relationAut aPerm_mem_relationAut bPerm_mem_relationAut g.property

private theorem card_fixed_zero : Nat.card (fixed 0) = Nat.card Model := by
  have he : fixed 0 = ⊤ := by ext g; simp [mem_fixed]
  rw [he, Subgroup.card_top]

private theorem orbit_zero : orbit (fixed 0) (0 : Fin 4060) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let g := (toBase (transDepth x) x)⁻¹
  exact ⟨⟨g, by intro y hy; omega⟩,
    inv_smul_eq_iff.mpr (toBase_smul x).symm⟩

private theorem orbit_one : orbit (fixed 1) (1 : Fin 4060) = {x | root x = 1} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have h := (model_relation g.val 0 1).mpr ((adj_zero 1).mpr (by decide +kernel))
    change adj (g.val • (0 : Fin 4060)) (g.val • (1 : Fin 4060)) at h
    rw [g.property 0 (by decide)] at h
    exact (adj_zero _).mp h
  · intro hx
    change root x = 1 at hx
    obtain ⟨g, hg0, hgx⟩ := root_reachable x
    refine ⟨⟨g, ?_⟩, ?_⟩
    · intro y hy
      have he : y = 0 := Fin.ext (by omega)
      subst y
      exact hg0
    · change g • (1 : Fin 4060) = x
      rw [hx] at hgx
      exact hgx

private theorem H2_model : H2 ≤ modelSubgroup := by
  rw [← H0_eq_model]
  exact H2_le.trans H1_le

private theorem H2_fixed (g : H2) : (⟨g.val, H2_model g.property⟩ : Model) ∈ fixed 2 := by
  intro x hx
  have he : x = 0 ∨ x = 1 := by
    have hv : x.val = 0 ∨ x.val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  rcases he with rfl | rfl
  · exact H1_fix ⟨g.val, H2_le g.property⟩
  · exact H2_fix g

private theorem H3_model : H3 ≤ modelSubgroup := H3_le.trans H2_model

private theorem H3_fixed (g : H3) : (⟨g.val, H3_model g.property⟩ : Model) ∈ fixed 3 := by
  intro x hx
  by_cases hlt : x.val < 2
  · exact H2_fixed ⟨g.val, H3_le g.property⟩ x hlt
  · have he : x = 2 := Fin.ext (by omega)
    subst x
    exact H3_fix g

private theorem H4_model : H4 ≤ modelSubgroup := H4_le.trans H3_model

private theorem H4_fixed (g : H4) : (⟨g.val, H4_model g.property⟩ : Model) ∈ fixed 4 := by
  intro x hx
  by_cases hlt : x.val < 3
  · exact H3_fixed ⟨g.val, H4_le g.property⟩ x hlt
  · have he : x = 3 := Fin.ext (by omega)
    subst x
    exact H4_fix g

private theorem orbit_two : orbit (fixed 2) (2 : Fin 4060) = Set.range L2Point := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact image2_mem_range g.val.val (model_relation g.val) g.property
  · rintro ⟨r, rfl⟩
    exact ⟨⟨⟨L2Rep r, H2_model (L2Rep_mem r)⟩, H2_fixed ⟨_, L2Rep_mem r⟩⟩,
      L2Rep_point r⟩

private theorem orbit_three : orbit (fixed 3) (3 : Fin 4060) = Set.range L3Point := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact image3_mem_range g.val.val (model_relation g.val) g.property
  · rintro ⟨r, rfl⟩
    exact ⟨⟨⟨L3Rep r, H3_model (L3Rep_mem r)⟩, H3_fixed ⟨_, L3Rep_mem r⟩⟩,
      L3Rep_point r⟩

private theorem orbit_four : orbit (fixed 4) (4 : Fin 4060) = Set.range L4Point := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact image4_mem_range g.val.val (model_relation g.val) g.property
  · rintro ⟨r, rfl⟩
    exact ⟨⟨⟨L4Rep r, H4_model (L4Rep_mem r)⟩, H4_fixed ⟨_, L4Rep_mem r⟩⟩,
      L4Rep_point r⟩

private theorem card_fixed_five : Nat.card (fixed 5) = 1 := by
  have he : fixed 5 = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    change g = 1
    apply Subtype.ext
    exact fix_five_eq_one g.val (model_relation g) hg
  rw [he, Subgroup.card_bot]

private theorem card_model_from_orbits : Nat.card Model = 145926144000 := by
  have h0 := card_step (0 : Fin 4060)
  have h1 := card_step (1 : Fin 4060)
  have h2 := card_step (2 : Fin 4060)
  have h3 := card_step (3 : Fin 4060)
  have h4 := card_step (4 : Fin 4060)
  change Nat.card (fixed 0) = Nat.card (orbit (fixed 0) (0 : Fin 4060)) * Nat.card (fixed 1) at h0
  change Nat.card (fixed 1) = Nat.card (orbit (fixed 1) (1 : Fin 4060)) * Nat.card (fixed 2) at h1
  change Nat.card (fixed 2) = Nat.card (orbit (fixed 2) (2 : Fin 4060)) * Nat.card (fixed 3) at h2
  change Nat.card (fixed 3) = Nat.card (orbit (fixed 3) (3 : Fin 4060)) * Nat.card (fixed 4) at h3
  change Nat.card (fixed 4) = Nat.card (orbit (fixed 4) (4 : Fin 4060)) * Nat.card (fixed 5) at h4
  have hu : Nat.card (Set.univ : Set (Fin 4060)) = 4060 := by
    simp [Nat.card_eq_fintype_card]
  rw [card_fixed_zero, orbit_zero, hu] at h0
  rw [orbit_one, Nat.card_coe_set_eq, root_one_card] at h1
  rw [orbit_two, Nat.card_range_of_injective L2Point_injective, Nat.card_fin] at h2
  rw [orbit_three, Nat.card_range_of_injective L3Point_injective, Nat.card_fin] at h3
  rw [orbit_four, Nat.card_range_of_injective L4Point_injective, Nat.card_fin,
    card_fixed_five] at h4
  omega

/-- The ambient model has no subgroup of order divisible by 2^15.
This follows from the checked orbital stabilizer bounds, without invoking
any theorem from the full model-order development. -/
public theorem not_two_pow_fifteen_dvd_card_model : ¬ 2 ^ 15 ∣ Nat.card Model := by
  rw [card_model_from_orbits]
  decide

end Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate
