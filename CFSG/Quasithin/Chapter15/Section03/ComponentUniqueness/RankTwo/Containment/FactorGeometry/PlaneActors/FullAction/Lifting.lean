module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Kernel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.QuotientIntersection

/-!
# Lifting the two plane images

The images of the two residual centralizers are disjoint because a common
actor fixes both planes, hence all of V. If each image has order three,
their product fills the order-nine image of Y. Their join is normal inside
Y and has two-group quotient, so two-perfectness forces that join to be Y.
The previously identified two-group action kernel also shows that each
actor has three-part three.

The order-three image assertions remain explicit inputs here. They must
come from the literal natural-action calculation before constructing the
CaseOne actor pair.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7 and
15.3.39–40, printed pp.1122 and 1137–1138.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo

private theorem sup_eq_of_disjoint_card_three {H : Type*} [Group H] [Finite H]
    (A B C : Subgroup H) (hAC : A ≤ C) (hBC : B ≤ C)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hC : Nat.card C = 9)
    (hd : Disjoint A B) : A ⊔ B = C := by
  let f : A × B → (A ⊔ B : Subgroup H) := fun x =>
    ⟨x.1 * x.2, mul_mem_sup x.1.property x.2.property⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have he : (a : H) * b = (a' : H) * b' := congrArg Subtype.val h
    have hi : (a' : H)⁻¹ * a = (b' : H) * (b : H)⁻¹ := by
      calc
        _ = (a' : H)⁻¹ * ((a : H) * b) * (b : H)⁻¹ := by group
        _ = _ := by rw [he]; group
    have hx : (a' : H)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.property) a.property,
        hi ▸ B.mul_mem b'.property (B.inv_mem b.property)⟩
    rw [hd.eq_bot, mem_bot, inv_mul_eq_one] at hx
    have ha : a = a' := Subtype.ext hx.symm
    have hb : b = b' := by
      apply Subtype.ext
      rw [ha] at he
      exact mul_left_cancel he
    exact Prod.ext ha hb
  apply eq_of_le_of_card_ge (sup_le hAC hBC)
  calc
    Nat.card C = Nat.card (A × B) := by rw [hC, Nat.card_prod, hA, hB]
    _ ≤ Nat.card (A ⊔ B : Subgroup H) := Nat.card_le_card_of_injective f hf

private theorem perfect_generated_of_image {X H : Type*}
    [Group X] [Finite X] [Group H] [Finite H]
    (f : X →* H) (hX : IsPPerfect 2 X) (hk : IsPGroup 2 f.ker)
    (A B : Subgroup X) [A.Normal] [B.Normal]
    (hA : Nat.card (A.map f) = 3) (hB : Nat.card (B.map f) = 3)
    (hR : Nat.card f.range = 9) (hd : Disjoint (A.map f) (B.map f)) :
    A ⊔ B = ⊤ := by
  have hgen : (A ⊔ B).map f = f.range := by
    rw [Subgroup.map_sup]
    exact sup_eq_of_disjoint_card_three _ _ _ (map_le_range _ _) (map_le_range _ _)
      hA hB hR hd
  have hcover : (A ⊔ B) ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hgen]
    ext x
    simp
  exact hX (A ⊔ B) inferInstance
    (isPGroup_quotient_of_sup_eq_top (A ⊔ B) f.ker hk hcover)

variable {G : Type*} [Group G]

/-- Transport an ambient subgroup through the actual restricted actor. -/
public theorem natural_restricted_actor_map {M V X Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M) (hXY : X ≤ Y) :
    (X.subgroupOf Y).map (d.actor.comp (inclusion hYM)) = d.image X := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨inclusion hYM x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hXY hx⟩, hx, rfl⟩

/-- Residual centralizers of distinct planes have disjoint action images. -/
public theorem natural_centralizingFactor_images_disjoint {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    Disjoint (d.image (centralizingFactor X (d.plane i)))
      (d.image (centralizingFactor X (d.plane j))) := by
  let C := (centralizer (d.plane i : Set G)).subgroupOf M
  let D := (centralizer (d.plane j : Set G)).subgroupOf M
  have hk : d.actor.ker ≤ D := by
    rw [d.ker_actor]
    intro x hx
    exact centralizer_le (d.plane_le j) hx
  have hc : centralizer (d.plane i : Set G) ⊓ centralizer (d.plane j : Set G) ≤
      centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    exact (natural_planes_sup d hij).ge.trans
      (sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))
  have hcd : C ⊓ D ≤ d.actor.ker := by
    rw [d.ker_actor]
    exact fun x hx => hc hx
  have hz : C.map d.actor ⊓ D.map d.actor = ⊥ := by
    rw [← map_inf_of_ker_le d.actor C D hk]
    exact (Subgroup.map_eq_bot_iff _).mpr hcd
  rw [disjoint_iff]
  apply le_bot_iff.mp
  rw [← hz]
  exact inf_le_inf (map_mono (fun x hx => centralizingFactor_le X (d.plane i) hx))
    (map_mono (fun x hx => centralizingFactor_le X (d.plane j) hx))

/-- An order-three image in the source residual gives three-part three. -/
public theorem residual_subgroup_three_part_of_image [Finite G] {M Mc V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXY : X ≤ residualY M Mc)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9)
    (himage : Nat.card (d.image X) = 3) :
    3 ^ (Nat.card X).factorization 3 = 3 := by
  let f := d.actor.comp (inclusion
    (hXY.trans (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)))
  have hk : f.ker = (pCore 2 (residualY M Mc)).comap (inclusion hXY) := by
    rw [← residualY_actor_ker_eq_twoCore d h7 h9, MonoidHom.comap_ker]
    rfl
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective (inclusion hXY) (inclusion_injective hXY)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hr : Nat.card f.range = 3 := by rwa [natural_restricted_actor_range]
  have hc : Nat.card X = 2 ^ n * 3 := by
    rw [← f.ker.card_mul_index, index_ker, hn, hr]
  rw [hc, Nat.factorization_mul (pow_ne_zero n (by decide)) (by decide)]
  simp [Nat.factorization_pow, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2),
    Nat.Prime.factorization_self Nat.prime_three]

/-- The two residual centralizers generate Y once both images have order three. -/
public theorem residual_plane_generation_of_images [Finite G] {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V) {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9)
    (hi : Nat.card (d.image (centralizingFactor (residualY M Mc) (d.plane i))) = 3)
    (hj : Nat.card (d.image (centralizingFactor (residualY M Mc) (d.plane j))) = 3) :
    residualY M Mc = centralizingFactor (residualY M Mc) (d.plane i) ⊔
      centralizingFactor (residualY M Mc) (d.plane j) := by
  let Y := residualY M Mc
  have hYM : Y ≤ M := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  let f := d.actor.comp (inclusion hYM)
  let A := centralizingFactor Y (d.plane i)
  let B := centralizingFactor Y (d.plane j)
  have hAY : A ≤ Y := centralizingFactor_le_left _ _
  have hBY : B ≤ Y := centralizingFactor_le_left _ _
  have hp : IsPPerfect 2 Y := residualY_isPPerfect M Mc
  let : (A.subgroupOf Y).Normal := centralizingFactor_normal
    (perfect_normalizes_planes d hYM hp i)
  let : (B.subgroupOf Y).Normal := centralizingFactor_normal
    (perfect_normalizes_planes d hYM hp j)
  have hk : IsPGroup 2 f.ker := by
    rw [residualY_actor_ker_eq_twoCore d h7 h9]
    exact pCore_isPGroup
  have hr : Nat.card f.range = 9 := by
    rw [natural_restricted_actor_range, h7]
    exact orthogonal_twoResidual_card
  have ht : A.subgroupOf Y ⊔ B.subgroupOf Y = ⊤ := by
    apply perfect_generated_of_image f hp hk
    · rwa [natural_restricted_actor_map d hYM hAY]
    · rwa [natural_restricted_actor_map d hYM hBY]
    · exact hr
    · rw [natural_restricted_actor_map d hYM hAY,
        natural_restricted_actor_map d hYM hBY]
      exact natural_centralizingFactor_images_disjoint d hij
  have hm := congrArg (Subgroup.map Y.subtype) ht
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAY, map_subgroupOf_eq_of_le hBY,
    ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm.symm

end CFSG.Quasithin.Chapter15.Section03.RankTwo
