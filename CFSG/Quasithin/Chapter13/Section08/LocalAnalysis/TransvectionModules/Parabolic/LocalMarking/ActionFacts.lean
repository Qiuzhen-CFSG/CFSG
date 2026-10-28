module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.PlaneGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.LocalProduct
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceAction.Inputs
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The literal plane action for the local marking

The ordinary natural coordinates identify V₂ with a two-dimensional binary
space, while the earlier centralizer identity identifies the kernel of the
actual I₂-action on V₂. The natural plane residual supplies a fixed-point-free
actor on V, and hence also on V₂. These facts precede, and do not assume, an
S₃ quotient marking or compatible coordinates on V/V₂.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.3–4, printed p.916, and the local action in 13.8.6, printed p.948.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking

open EarlierCore RankDoubling.SourceAction
noncomputable section
variable {G : Type*} [Group G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (s : NaturalSetup T L V V₁ V₂ V₃)

include s

/-- Both factors of the source I₂ lie in the natural-action group LT. -/
theorem localI_le_LT : localI L V₁ V₂ ≤ L ⊔ (T : Subgroup G) :=
  sup_le (s.line_core_le_sylow.trans le_sup_right)
    ((localResidual_le L V₂).trans le_sup_left)

/-- The natural setup already makes I₂ normalize the entire literal V. -/
theorem localI_normalizes_V : localI L V₁ V₂ ≤ normalizer (V : Set G) :=
  (localI_le_LT s).trans s.normalizes_V

/-- Actual conjugation by I₂ on the order-four source plane. -/
def planeAction : localI L V₁ V₂ →* MulAut V₂ :=
  V₂.normalizerMonoidHom.comp (inclusion s.localI_le_plane_normalizer)

/-- Actual conjugation on the entire natural subgroup V. -/
def wholeAction : localI L V₁ V₂ →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion (localI_normalizes_V s))

/-- Restrict the given coordinates to the literal subgroup V₂. -/
def planeCoordinate : V₂ ≃* Multiplicative s.plane where
  toFun x := Multiplicative.ofAdd ⟨(s.coordinate
    ⟨x, (s.plane_le_seed.trans s.seed_le) x.property⟩).toAdd, by
      apply (mem_flagPreimage_iff s.coordinate s.plane _).mp
      rw [← s.plane_eq]
      exact x.property⟩
  invFun y := ⟨(s.coordinate.symm (Multiplicative.ofAdd y.toAdd.val)).val, by
    apply s.plane_eq.symm ▸ (mem_flagPreimage_iff s.coordinate s.plane _).mpr
    simpa only [s.coordinate.apply_symm_apply, toAdd_ofAdd] using y.toAdd.property⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun v : V => (v : G)) (s.coordinate.symm_apply_apply _)
  right_inv y := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (s.coordinate.apply_symm_apply _)
  map_mul' x y := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    apply Subtype.ext
    change (s.coordinate ((inclusion (s.plane_le_seed.trans s.seed_le) x) *
      (inclusion (s.plane_le_seed.trans s.seed_le) y))).toAdd =
      (s.coordinate (inclusion (s.plane_le_seed.trans s.seed_le) x)).toAdd +
      (s.coordinate (inclusion (s.plane_le_seed.trans s.seed_le) y)).toAdd
    exact congrArg Multiplicative.toAdd (s.coordinate.map_mul _ _)

/-- The literal V₂ has order four, independently of any local marking. -/
theorem plane_card : Nat.card V₂ = 4 := by
  rw [Nat.card_congr (planeCoordinate s).toEquiv]
  change Nat.card s.plane = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, s.plane_dim]
  rfl

variable {H : Subgroup G}
  (d : LocalData H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂))

include d in
/-- The kernel is the actual two-core, by the supplied earlier centralizer identity. -/
theorem planeAction_ker : (planeAction s).ker = pCore 2 (localI L V₁ V₂) := by
  apply map_injective (localI L V₁ V₂).subtype_injective
  change ((planeAction s).ker).map (localI L V₁ V₂).subtype = (localI L V₁ V₂).pCoreIn 2
  rw [← d.centralizer]
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.property, ?_⟩
    change inclusion s.localI_le_plane_normalizer i ∈ V₂.normalizerMonoidHom.ker at hi
    rw [normalizerMonoidHom_ker] at hi
    exact hi
  · rintro ⟨hi, hc⟩
    refine ⟨⟨x, hi⟩, ?_, rfl⟩
    change inclusion s.localI_le_plane_normalizer ⟨x, hi⟩ ∈ V₂.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hc


/-- The centralizer identity gives a genuine isomorphism with the actual
plane-action image, before proving that this image is all of S₃. -/
def planeRangeEquiv :
    (localI L V₁ V₂ ⧸ pCore 2 (localI L V₁ V₂)) ≃* (planeAction s).range :=
  (QuotientGroup.quotientMulEquivOfEq (planeAction_ker s d).symm).trans
    (QuotientGroup.quotientKerEquivRange (planeAction s))

variable [Finite G]

/-- Lift the natural-plane residual actor to an actual element of L₂.
It fixes no nonidentity element of the literal V. -/
theorem exists_fixedFree_actor : ∃ l : localResidual L V₂,
    ∀ v : V, wholeAction s (inclusion (show localResidual L V₂ ≤ localI L V₁ V₂
      from le_sup_right) l) v = v → v = 1 := by
  obtain ⟨Q, hQ⟩ := s.image_sylow
  have hP : (Q : Subgroup s.permutation.range).map s.permutation.range.subtype ≤
      Representation.BinaryOffender.subspaceStabilizer
        (BinaryPermutation.naturalRepresentation (Fin 6)) s.plane := by
    rw [hQ]
    exact s.sylow_plane_stable
  obtain ⟨c, hc, hf⟩ := PlaneGeometry.plane_residual_actor s.permutation.range
    s.alternating_le_range Q s.plane s.plane_dim hP
  rw [← s.two_image] at hc
  obtain ⟨g, hg, he⟩ := hc
  refine ⟨⟨g.val, hg⟩, ?_⟩
  intro v hv
  apply s.coordinate.injective
  rw [map_one]
  change (s.coordinate v).toAdd = 0
  apply hf
  rw [← he, ← s.conjugation g v]
  exact congrArg (fun w : V => (s.coordinate w).toAdd) hv

/-- The same actor fixes no nonidentity element of the source plane. -/
theorem exists_plane_fixedFree_actor : ∃ l : localResidual L V₂,
    ∀ v : V₂, planeAction s (inclusion (show localResidual L V₂ ≤ localI L V₁ V₂
      from le_sup_right) l) v = v → v = 1 := by
  obtain ⟨l, hl⟩ := exists_fixedFree_actor s
  refine ⟨l, ?_⟩
  intro v hv
  have h := hl (inclusion (s.plane_le_seed.trans s.seed_le) v)
  apply Subtype.ext
  exact congrArg (fun x : V => (x : G)) (h (Subtype.ext (congrArg (fun x : V₂ => (x : G)) hv)))


include d in
/-- The normal-closure identity forces the point core to move the source
plane: otherwise the entire I₂-action would be trivial. -/
theorem point_core_not_le_centralizer :
    ¬ (normalizer (V₁ : Set G)).pCoreIn 2 ≤ centralizer (V₂ : Set G) := by
  intro hc
  have hn : normalizer (V₂ : Set G) ≤ normalizer (centralizer (V₂ : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (V₂ : Set G))).mp
      inferInstance
  have hI : localI L V₁ V₂ ≤ centralizer (V₂ : Set G) := by
    rw [d.normalClosure]
    exact conjugateSpanBy_le hc hn
  obtain ⟨l, hl⟩ := exists_plane_fixedFree_actor s
  let i : localI L V₁ V₂ := inclusion le_sup_right l
  have hi : i ∈ (planeAction s).ker := by
    change inclusion s.localI_le_plane_normalizer i ∈ V₂.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hI i.property
  let : Nontrivial V₂ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [plane_card s]
    decide)
  obtain ⟨v, hv⟩ := exists_ne (1 : V₂)
  apply hv
  apply hl
  change planeAction s i v = v
  rw [MonoidHom.mem_ker.mp hi]
  rfl

variable [IsElementaryAbelian 2 V]

/-- The source plane is a Klein four-group, so its automorphism group is S₃. -/
theorem plane_isKleinFour : IsKleinFour V₂ := by
  let : IsElementaryAbelian 2 V₂ :=
    IsElementaryAbelian.of_le (s.plane_le_seed.trans s.seed_le)
  let : Nontrivial V₂ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [plane_card s]
    decide)
  exact ⟨plane_card s, IsElementaryAbelian.exponent_eq_prime (p := 2)⟩

/-- The quotient coordinate map before factoring out its exact kernel. -/
def quotientProjection : V →* Multiplicative (Natural ⧸ s.plane) :=
  s.plane.mkQ.toAddMonoidHom.toMultiplicative.comp s.coordinate.toMonoidHom

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- The kernel is the actual relative subgroup V₂ inside V. -/
theorem quotientProjection_ker : (quotientProjection s).ker = V₂.subgroupOf V := by
  ext v
  change s.plane.mkQ (s.coordinate v).toAdd = 0 ↔ (v : G) ∈ V₂
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_flagPreimage_iff s.coordinate s.plane v).symm.trans
    (by simp only [s.plane_eq])

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem quotientProjection_surjective : Function.Surjective (quotientProjection s) := by
  intro u
  obtain ⟨v, hv⟩ := s.plane.mkQ_surjective u.toAdd
  obtain ⟨x, hx⟩ := s.coordinate.surjective (Multiplicative.ofAdd v)
  refine ⟨x, ?_⟩
  change s.plane.mkQ (s.coordinate x).toAdd = u.toAdd
  rw [hx]
  exact hv

/-- Coordinates on the literal quotient V/V₂, with no module-action marking assumed. -/
def quotientCoordinate : Additive (SeedQuotient V V₂) ≃ₗ[RankDoubling.F]
    (Natural ⧸ s.plane) :=
  let e := (QuotientGroup.quotientMulEquivOfEq (quotientProjection_ker s).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quotientProjection s)
      (quotientProjection_surjective s))
  { e.toAdditiveLeft with map_smul' := ZMod.map_smul e.toAdditiveLeft }

omit [Finite G] in
theorem quotientCoordinate_mk (v : V) :
    quotientCoordinate s (seedClass V V₂ v) = s.plane.mkQ (s.coordinate v).toAdd := by
  rw [seedClass_eq_mk]
  change ((QuotientGroup.quotientKerEquivOfSurjective (quotientProjection s)
    (quotientProjection_surjective s))
    ((QuotientGroup.quotientMulEquivOfEq (quotientProjection_ker s).symm)
      (QuotientGroup.mk v))).toAdd = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

omit [Finite G] in
/-- The source quotient, rather than an unrelated carrier, is a binary plane. -/
theorem quotient_finrank : Module.finrank (ZMod 2) (Additive (SeedQuotient V V₂)) = 2 := by
  rw [(quotientCoordinate s).finrank_eq]
  have h := s.plane.finrank_quotient_add_finrank
  rw [s.plane_dim, BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at h
  norm_num at h
  change Module.finrank (ZMod 2) (Natural ⧸ s.plane) = 2
  omega


/-- Conjugation on the literal V/V₂, with its relative normality provided by
commutativity of V and both normalizer containments proved above. -/
def quotientAction : localI L V₁ V₂ →* MulAut (SeedQuotient V V₂) :=
  (exists_quotient_conjugation_action (localI L V₁ V₂) V V₂
    (localI_normalizes_V s) s.localI_le_plane_normalizer inferInstance).choose

omit [Finite G] in
theorem quotientAction_mk (i : localI L V₁ V₂) (v : V) :
    quotientAction s i (QuotientGroup.mk' (V₂.subgroupOf V) v) =
      QuotientGroup.mk' (V₂.subgroupOf V) (wholeAction s i v) :=
  (exists_quotient_conjugation_action (localI L V₁ V₂) V V₂
    (localI_normalizes_V s) s.localI_le_plane_normalizer inferInstance).choose_spec i v

/-- The binary representation induced by that actual quotient action. -/
def seedRepresentation : Representation (ZMod 2) (localI L V₁ V₂)
    (Additive (SeedQuotient V V₂)) where
  toFun i := (quotientAction s i).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext x
    change Additive.ofMul (quotientAction s 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' i j := by
    ext x
    change Additive.ofMul (quotientAction s (i * j) x.toMul) = _
    rw [map_mul]
    rfl

omit [Finite G] in
theorem seedRepresentation_mk (i : localI L V₁ V₂) (v : V) :
    seedRepresentation s i (seedClass V V₂ v) = seedClass V V₂ (wholeAction s i v) := by
  simp only [seedClass_eq_mk]
  exact congrArg Additive.ofMul (quotientAction_mk s i v)

/-- The fixed-point-free actor stays fixed-point-free on V/V₂. This uses
surjectivity of its displacement on V, not a prior natural-module marking. -/
theorem exists_seed_fixedFree_actor : ∃ l : localResidual L V₂,
    ∀ x : Additive (SeedQuotient V V₂),
      seedRepresentation s (inclusion (show localResidual L V₂ ≤ localI L V₁ V₂
        from le_sup_right) l) x = x → x = 0 := by
  obtain ⟨l, hl⟩ := exists_fixedFree_actor s
  let i : localI L V₁ V₂ := inclusion le_sup_right l
  let R : Additive V →ₗ[ZMod 2] Additive V :=
    (wholeAction s i).toMonoidHom.toAdditive.toZModLinearMap 2
  let q : Additive V →ₗ[ZMod 2] Additive (SeedQuotient V V₂) :=
    (QuotientGroup.mk' (V₂.subgroupOf V)).toAdditive.toZModLinearMap 2
  let D := R - LinearMap.id
  let Dq := seedRepresentation s i - LinearMap.id
  have hi : Function.Injective D := LinearMap.ker_eq_bot.mp (by
    apply eq_bot_iff.mpr
    intro x hx
    have he : R x = x := sub_eq_zero.mp hx
    exact congrArg Additive.ofMul (hl x.toMul (congrArg Additive.toMul he)))
  have hs := LinearMap.surjective_of_injective hi
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (V₂.subgroupOf V) y.toMul
    exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩
  have hD : ∀ x, Dq (q x) = q (D x) := by
    intro x
    change seedRepresentation s i (q x) - q x = q (R x - x)
    rw [map_sub]
    congr 1
    simpa [q, R, seedClass_eq_mk] using seedRepresentation_mk s i x.toMul
  have hDs : Function.Surjective Dq := by
    intro y
    obtain ⟨x, rfl⟩ := hq y
    obtain ⟨z, rfl⟩ := hs x
    exact ⟨q z, hD z⟩
  have hDi := LinearMap.injective_iff_surjective.mpr hDs
  refine ⟨l, ?_⟩
  intro x hx
  change seedRepresentation s i x = x at hx
  apply hDi
  change seedRepresentation s i x - x = Dq 0
  rw [hx, sub_self, map_zero]

end
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking
