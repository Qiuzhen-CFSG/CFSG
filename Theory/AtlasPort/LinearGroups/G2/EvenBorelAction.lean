module

public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear

/-!
# The actual field action on the even G₂ Borel quotient

An inner–field automorphism preserving the positive-root Sylow has its inner
factor in the Borel: coefficient transport preserves that Sylow, and its
normalizer is the Borel. Conjugation inside the Borel is trivial on its
abelian quotient, while coefficient transport applies the field automorphism
to both torus parameters. These statements derive the action from octonion
coordinates and do not assume Borel placement or a torus action table.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The coefficient
transport and torus coordinate calculation reuse the licensed ATLAS model
and the calculation in Chapter1/Section03/Embeddings/InvariantLarge/EvenActions/G2.
See LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
namespace Atlas.G2.EvenBorelTorus
open Subgroup Atlas.SplitOctonion LieAutomorphismExtensions
variable {F : Type*} [Field F]

/-- Coefficient transport acts on the two genuine torus parameters. -/
theorem field_torus (σ : F ≃+* F) (l m : Fˣ) :
    fieldEquiv σ (torus l m) =
      torus (Units.map σ.toMonoidHom l) (Units.map σ.toMonoidHom m) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [fieldEquiv, transportAutomorphism, transportLinear, mapCoefficients,
      torus, torusEquiv, torusLinear, torusWeights]

theorem field_map_torus (σ : F ≃+* F) :
    (splitTorus (K := F)).map (fieldEquiv σ).toMonoidHom = splitTorus := by
  ext t
  constructor
  · rintro ⟨_,⟨⟨l,m⟩,rfl⟩,rfl⟩
    exact ⟨(Units.map σ.toMonoidHom l,Units.map σ.toMonoidHom m),
      (field_torus σ l m).symm⟩
  · rintro ⟨⟨l,m⟩,rfl⟩
    refine ⟨torus (Units.map σ.symm.toMonoidHom l) (Units.map σ.symm.toMonoidHom m),
      ⟨(Units.map σ.symm.toMonoidHom l, Units.map σ.symm.toMonoidHom m),rfl⟩,?_⟩
    change fieldEquiv σ _ = _
    rw [field_torus]
    congr 1 <;> apply Units.ext <;> exact σ.apply_symm_apply _

theorem field_map_borel (σ : F ≃+* F) :
    (borel (K := F)).map (fieldEquiv σ).toMonoidHom = borel := by
  rw [borel, Subgroup.map_sup, SylowNormalizer.field_map_unipotent, field_map_torus]

/-- Restriction of a genuine Borel-preserving ambient automorphism. -/
noncomputable def restrictActor (α : MulAut (Model F))
    (hα : borel.map α.toMonoidHom = borel) : MulAut (borel (K := F)) :=
  (α.subgroupMap borel).trans (MulEquiv.subgroupCongr hα)

@[simp] theorem restrictActor_val (α : MulAut (Model F))
    (hα : borel.map α.toMonoidHom = borel) (b : borel (K := F)) :
    (restrictActor α hα b).val = α b.val := rfl

noncomputable def fieldBorel (σ : F ≃+* F) : MulAut (borel (K := F)) :=
  restrictActor (fieldEquiv σ) (field_map_borel σ)

theorem projection_unipotent (u : unipotent (K := F)) :
    projection (⟨u.val, (le_sup_left : unipotent ≤ borel) u.property⟩ : borel (K := F)) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [projection_ker]
  exact u.property

/-- The torus projection commutes with the coefficientwise field action. -/
theorem projection_field (σ : F ≃+* F) (b : borel (K := F)) :
    projection (fieldBorel σ b) =
      (Units.map σ.toMonoidHom (projection b).1,
       Units.map σ.toMonoidHom (projection b).2) := by
  obtain ⟨⟨u,t⟩,he⟩ := (borelProductEquiv (K := F)).surjective b
  obtain ⟨t,⟨p,rfl⟩⟩ := t
  let ub : borel (K := F) := ⟨u,(le_sup_left : unipotent ≤ borel) u.property⟩
  let tb : borel (K := F) := ⟨torusHom p,(le_sup_right : splitTorus ≤ borel) ⟨p,rfl⟩⟩
  have hb : b = ub * tb := (Subtype.ext (congrArg Subtype.val he)).symm
  have hu : projection (fieldBorel σ ub) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [projection_ker]
    have h := mem_map_of_mem (fieldEquiv σ).toMonoidHom u.property
    rw [SylowNormalizer.field_map_unipotent] at h
    exact h
  have ht : projection (fieldBorel σ tb) =
      (Units.map σ.toMonoidHom p.1,Units.map σ.toMonoidHom p.2) := by
    have he : fieldBorel σ tb =
        ⟨torusHom (Units.map σ.toMonoidHom p.1,Units.map σ.toMonoidHom p.2),
          (le_sup_right : splitTorus ≤ borel) ⟨_,rfl⟩⟩ :=
      Subtype.ext (field_torus σ p.1 p.2)
    rw [he, projection_torus]
  have hu' : projection ub = 1 := projection_unipotent u
  have ht' : projection tb = p := projection_torus p
  rw [hb, map_mul, map_mul, hu, ht, one_mul, map_mul, hu', ht', one_mul]

/-- Every inner automorphism of the Borel acts trivially on its torus quotient. -/
theorem projection_conj (g b : borel (K := F)) :
    projection (g * b * g⁻¹) = projection b := by
  simp only [map_mul, map_inv]
  rw [mul_comm (projection g) (projection b), mul_inv_cancel_right]

variable [CharP F 2]

/-- Sylow stabilization forces the inner factor into the Borel. -/
theorem semilinear_inner_mem_borel (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent) :
    z.left ∈ borel := by
  rw [← SylowNormalizer.normalizer_unipotent]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change unipotent.map ((MulAut.conj z.left).toMonoidHom.comp
    (fieldEquiv z.right).toMonoidHom) = unipotent at hz
  rwa [← map_map, SylowNormalizer.field_map_unipotent] at hz

theorem semilinear_map_borel (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent) :
    borel.map (semilinearAction z).toMonoidHom = borel := by
  change borel.map ((MulAut.conj z.left).toMonoidHom.comp
    (fieldEquiv z.right).toMonoidHom) = borel
  rw [← map_map, field_map_borel]
  exact mem_normalizer_iff_map_conj_eq.mp
    (borel.le_normalizer (semilinear_inner_mem_borel z hz))

/-- The quotient action of every Sylow-preserving inner–field actor. -/
theorem projection_semilinear (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent)
    (b : borel (K := F)) :
    projection (restrictActor (semilinearAction z) (semilinear_map_borel z hz) b) =
      (Units.map z.right.toMonoidHom (projection b).1,
       Units.map z.right.toMonoidHom (projection b).2) := by
  let g : borel (K := F) := ⟨z.left,semilinear_inner_mem_borel z hz⟩
  have he : restrictActor (semilinearAction z) (semilinear_map_borel z hz) b =
      g * fieldBorel z.right b * g⁻¹ := rfl
  rw [he, projection_conj, projection_field]

/-- Coverage is the only automorphism-classification input: placement is derived. -/
theorem stabilizing_actor_factorization
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (α : MulAut (Model F)) (hα : unipotent.map α.toMonoidHom = unipotent) :
    ∃ (g : borel (K := F)) (σ : F ≃+* F), α = MulAut.conj g.val * fieldAction σ := by
  obtain ⟨z,rfl⟩ := hcover α
  exact ⟨⟨z.left,semilinear_inner_mem_borel z hα⟩,z.right,rfl⟩

/-- An inner two-element stabilizing the Sylow is induced by that Sylow. -/
theorem inner_two_element_mem_unipotent [Finite F] (hq : 2 < Nat.card F)
    (g : borel (K := F)) (k : ℕ) (hk : (MulAut.conj g.val) ^ (2 ^ k) = 1) :
    g.val ∈ unipotent := by
  have hg : g ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    apply Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hq)
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using hk
  have horder : orderOf (projection g) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg, map_one])
  have hodd : Odd (Nat.card (Fˣ × Fˣ)) := by
    rw [Nat.card_congr torusParameterEquiv.toEquiv]
    exact card_torus_odd
  have he : projection g = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left k)
      horder (orderOf_dvd_natCard _))
  have hm : g ∈ (projection (F := F)).ker := he
  rwa [projection_ker] at hm

end Atlas.G2.EvenBorelTorus
