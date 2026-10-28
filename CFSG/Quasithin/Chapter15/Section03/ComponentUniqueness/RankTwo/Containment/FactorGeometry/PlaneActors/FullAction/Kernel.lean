module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import Theory.GroupTheory.WreathTwoOddCoreImageDichotomy
public import Theory.GroupTheory.PResidual.NormalComplement

/-!
# The kernel of the full residual plane action

The two-residual of the natural orthogonal actor has order nine: its odd
core has index eight, and the wreath group has order 72. For an actual
subgroup action with image of order nine, the two-core maps trivially.
If the two-core quotient also has order nine, equality of indices identifies
the kernel with that core. Compatibility then gives the literal centralizer.

This supplies the kernel step of the CaseOne construction; it does not yet
construct the two residual actors.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7 and
the plane construction, printed pp.1121–1122; the uses in 15.3.39–40,
printed pp.1137–1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo

/-- Compare the source residual notation with its prime-group quotient formulation. -/
theorem orthogonal_twoResidual_eq_pResidual :
    Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor) =
      pResidual 2 OrthogonalActor := by
  rw [Stellmacher.SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  apply le_antisymm
  · exact BenderSuzuki.External.hktPResidual_le _ inferInstance
      (isPGroup_quotient_pResidual 2)
  · exact sInf_le ⟨BenderSuzuki.External.hktPResidual_normal,
      BenderSuzuki.External.hktPResidual_quotient_isPGroup⟩

/-- Every cubic actor belongs to the full orthogonal two-residual. -/
theorem orthogonal_cubic_mem_twoResidual (a : OrthogonalActor) (ha : a ^ 3 = 1) :
    a ∈ Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor) := by
  rw [orthogonal_twoResidual_eq_pResidual]
  exact mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha))

/-- The full natural orthogonal actor has two-residual of order nine. -/
theorem orthogonal_twoResidual_card :
    Nat.card (Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) = 9 := by
  have hi : (pPrimeCore 2 OrthogonalActor).index = 8 :=
    Theory.GroupTheory.wreathTwo_oddCore_index_eight ⟨MulEquiv.refl _⟩
  have hp : IsPGroup 2 (OrthogonalActor ⧸ pPrimeCore 2 OrthogonalActor) :=
    IsPGroup.of_card (n := 3) (by rwa [← index_eq_card])
  have he : pResidual 2 OrthogonalActor = pPrimeCore 2 OrthogonalActor :=
    le_antisymm (sInf_le ⟨inferInstance, hp⟩) pPrimeCore_le_pResidual
  have hc : Nat.card OrthogonalActor = 72 := by
    rw [RegularWreathProduct.card]
    have hs : Nat.card OrthogonalPlaneActor = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hs]
    norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]
  have hm := (pPrimeCore 2 OrthogonalActor).card_mul_index
  rw [hi, hc] at hm
  rw [orthogonal_twoResidual_eq_pResidual, he]
  omega

variable {G : Type*} [Group G]

/-- Restriction to a subgroup gives exactly its specified action image. -/
theorem natural_restricted_actor_range {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) :
    (d.actor.comp (inclusion hXM)).range = d.image X := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨inclusion hXM x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The restricted actor kernel is the literal pointwise centralizer. -/
theorem natural_restricted_actor_ker {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M) :
    (d.actor.comp (inclusion hXM)).ker = (centralizer (V : Set G)).subgroupOf X := by
  rw [← MonoidHom.comap_ker, d.ker_actor]
  rfl

/-- Equal order-nine images and two-core quotients identify the kernel. -/
theorem natural_actor_ker_eq_twoCore_of_nine [Finite G] {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    (himage : Nat.card (d.image X) = 9)
    (h9 : Nat.card (X ⧸ pCore 2 X) = 9) :
    (d.actor.comp (inclusion hXM)).ker = pCore 2 X := by
  let f := d.actor.comp (inclusion hXM)
  have hr : Nat.card f.range = 9 := by rwa [natural_restricted_actor_range]
  have hle : pCore 2 X ≤ f.ker := by
    have hp := (pCore_isPGroup (p := 2) (G := X)).map f
    have hd : Nat.card ((pCore 2 X).map f) ∣ 9 :=
      hr ▸ card_dvd_of_le (map_le_range _ _)
    have hbot : (pCore 2 X).map f = ⊥ := by
      apply card_eq_one.mp
      rcases hp.card_eq_or_dvd with he | he
      · exact he
      · have : 2 ∣ 9 := he.trans hd
        norm_num at this
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  apply (eq_of_le_of_card_ge hle ?_).symm
  have hc := (pCore 2 X).card_mul_index
  have hk := f.ker.card_mul_index
  rw [index_eq_card, h9] at hc
  rw [index_ker, hr] at hk
  omega

/-- The genuine 15.3.7 image and order-nine quotient identify the kernel on Y. -/
theorem residualY_actor_ker_eq_twoCore [Finite G] {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9) :
    (d.actor.comp (inclusion (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))).ker =
      pCore 2 (residualY M Mc) :=
  natural_actor_ker_eq_twoCore_of_nine d _ (h7 ▸ orthogonal_twoResidual_card) h9

/-- In CaseOne, the actual centralizer of V inside Y is O₂(Y). -/
theorem residualY_centralizer_eq_twoCore [Finite G] {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9) :
    (centralizer (V : Set G)).subgroupOf (residualY M Mc) =
      pCore 2 (residualY M Mc) := by
  rw [← natural_restricted_actor_ker d
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)]
  exact residualY_actor_ker_eq_twoCore d h7 h9

end CFSG.Quasithin.Chapter15.Section03.RankTwo
