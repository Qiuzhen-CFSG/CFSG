module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.InnerActors
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors

/-!
# The literal Sylow geometry in the orthogonal rank-one case

Conjugating the group marking and vector coordinates together identifies the
source intersection T∩L with the canonical root group. Its relative normalizer
then transports the fixed-field line partition and all remaining-actor fixed
spaces and ratios. In an even extension the same coordinates produce a field
involution normalizing T∩L, its actual layer and root centralizers, and the
quadratic actor X=R_t⟨t⟩. Its displacement is a nonsingular K-line.

No Sylow-coordinate, pure-lift or fixed-space premise remains in the two source
applications. They apply to the original representation, with actual subgroups
and the original relative normalizer in L.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.3.1.2,
printed p.454; D.2.1, printed p.178.
-/

open Representation Representation.BinaryOffender Subgroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
open scoped ENNReal
namespace CFSG.Quasithin.ChapterK.RankOne.OrthogonalModel
@[expose] public noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance orthogonalSylowAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance orthogonalSylowSpace : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
local notation "SL" => Matrix.SpecialLinearGroup (Fin 2) (Field s)
variable (M : OrthogonalModel s ρ L)

/-- Conjugate the marking and coordinates by the same model element. -/
private def sylowRebase (g : SL) : OrthogonalModel s ρ L where
  groupEquiv := M.groupEquiv.trans (MulAut.conj g⁻¹)
  coordinates := M.coordinates.trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((SL2.BinarySmall.hermitian s).asGroupHom g⁻¹))
  intertwines a v := by
    change SL2.BinarySmall.hermitian s g⁻¹ (M.coordinates (ρ a.val v)) =
      SL2.BinarySmall.hermitian s (g⁻¹ * M.groupEquiv a * (g⁻¹)⁻¹)
        (SL2.BinarySmall.hermitian s g⁻¹ (M.coordinates v))
    rw [M.intertwines]
    simp only [map_mul, Module.End.mul_apply, inv_inv,
      (SL2.BinarySmall.hermitian s).self_inv_apply]

private theorem sylowRebase_embedding (g a : SL) :
    (M.sylowRebase g).modelEmbedding a = M.modelEmbedding ((MulAut.conj g) a) := by
  simp [sylowRebase, modelEmbedding, MulAut.conj_apply]

private theorem sylowRebase_image (g : SL) (A : Subgroup SL) :
    (M.sylowRebase g).modelImage A =
      M.modelImage (A.map (MulAut.conj g).toMonoidHom) := by
  unfold modelImage
  rw [Subgroup.map_map]
  congr 1
  ext a
  exact M.sylowRebase_embedding g a

include M in
/-- Choose genuine Hermitian coordinates in which the given T∩L is the full root group. -/
theorem exists_sylow_coordinates [Finite G] [L.Normal] (T : Sylow 2 G) :
    ∃ P : OrthogonalModel s ρ L,
      P.modelImage (upperUnipotent (Field s)) = (T : Subgroup G) ⊓ L := by
  obtain ⟨g, hg⟩ := sylow_intersection_model M T
  exact ⟨M.sylowRebase g, (M.sylowRebase_image g _).trans hg.symm⟩

/-- The relative normalizer in the layer is the image of the literal model normalizer. -/
theorem modelImage_normalizer (A : Subgroup SL) :
    M.modelImage (Subgroup.normalizer (A : Set SL)) = (Subgroup.normalizer (M.modelImage A : Set G)) ⊓ L := by
  ext x
  constructor
  · intro hx
    exact ⟨Subgroup.le_normalizer_map M.modelEmbedding hx,
      M.modelImage_le_layer _ hx⟩
  · rintro ⟨hx, hxL⟩
    let a := M.groupEquiv ⟨x, hxL⟩
    have ha : M.modelEmbedding a = x := congrArg Subtype.val
      (M.groupEquiv.symm_apply_apply ⟨x, hxL⟩)
    refine ⟨a, ?_, ha⟩
    change ∀ b : SL, b ∈ A ↔ a * b * a⁻¹ ∈ A
    intro b
    have hb (c : SL) : M.modelEmbedding c ∈ M.modelImage A ↔ c ∈ A :=
      Subgroup.mem_map_iff_mem M.modelEmbedding_injective
    rw [← hb b, ← hb (a * b * a⁻¹)]
    have hx := hx (M.modelEmbedding b)
    change (M.modelEmbedding b ∈ M.modelImage A ↔
      x * M.modelEmbedding b * x⁻¹ ∈ M.modelImage A) at hx
    simpa only [map_mul, map_inv, ha] using hx

/-- Normalizer conjugates of the fixed-field root group partition the nonidentity roots. -/
theorem model_root_partition {a : G}
    (ha : a ∈ M.modelImage (upperUnipotent (Field s))) (hne : a ≠ 1) :
    ∃! R : Subgroup G,
      (∃ c ∈ (Subgroup.normalizer (M.modelImage (upperUnipotent (Field s)) : Set G)) ⊓ L,
        R = (M.modelImage (fixedRootGroup s)).map (MulAut.conj c).toMonoidHom) ∧ a ∈ R := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hb1 : b ≠ 1 := by intro he; exact hne (he ▸ M.modelEmbedding.map_one)
  obtain ⟨R, ⟨⟨g, hg, hR⟩, hbR⟩, huniq⟩ := root_partition s b hb hb1
  refine ⟨M.modelImage R, ⟨?_, Subgroup.mem_map_of_mem _ hbR⟩, ?_⟩
  · refine ⟨M.modelEmbedding g, ?_, ?_⟩
    · rw [← M.modelImage_normalizer]
      exact Subgroup.mem_map_of_mem _ hg
    · rw [hR, M.modelImage_conj]
  · rintro S ⟨⟨c, hc, rfl⟩, hbS⟩
    rw [← M.modelImage_normalizer] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    rw [← M.modelImage_conj] at hbS ⊢
    have hbK := (Subgroup.mem_map_iff_mem M.modelEmbedding_injective).mp hbS
    exact congrArg M.modelImage (huniq _ ⟨⟨k, hk, rfl⟩, hbK⟩)

/-- The image of a fixed space is the literal K-linear invariant space. -/
theorem modelImage_fixedModelSpace (A : Subgroup SL) :
    M.fixedModelSpace (M.modelImage A) =
      Representation.invariants ((action s).comp A.subtype) :=
  M.fixedModelSpace_eq_of_mem_iff _ _ (M.mem_modelImage_fixedSpace_iff A)

/-- The fixed K-line of the full root group, on the original representation. -/
theorem model_upper_fixed_Kfinrank :
    Module.finrank (fixedField s)
      (M.fixedModelSpace (M.modelImage (upperUnipotent (Field s)))) = 1 := by
  rw [M.modelImage_fixedModelSpace, (upperFixedEquivK s).finrank_eq, Module.finrank_self]

/-- Quadratic root actors are exactly the subgroups of the normalizer's
conjugates of the fixed-field root group. -/
theorem model_root_quadratic_iff (A : Subgroup G)
    (hAU : A ≤ M.modelImage (upperUnipotent (Field s))) (hne : A ≠ ⊥) :
    IsQuadratic ρ A ↔
      ∃ c ∈ Subgroup.normalizer (M.modelImage (upperUnipotent (Field s)) : Set G) ⊓ L,
        A ≤ (M.modelImage (fixedRootGroup s)).map (MulAut.conj c).toMonoidHom := by
  have hAL := hAU.trans (M.modelImage_le_layer _)
  have he := M.modelImage_innerActor A hAL
  have hBU : M.innerActor A ≤ upperUnipotent (Field s) := by
    apply (Subgroup.map_le_map_iff_of_injective M.modelEmbedding_injective).mp
    change M.modelImage _ ≤ M.modelImage _
    rwa [he]
  have hB := M.innerActor_elementary A hAL ((M.upper_calculation.1).of_le hAU hne)
  constructor
  · intro hq
    have hqB := (M.modelImage_quadratic_iff _).mp (he.symm ▸ hq)
    obtain ⟨u, hu, hBu⟩ := (quadratic_iff_le_rootLine s _ hBU hB.1).mp hqB
    obtain ⟨g, hg, hgu⟩ := rootLine_eq_normalizer_conjugate s hu
    refine ⟨M.modelEmbedding g, ?_, ?_⟩
    · rw [← M.modelImage_normalizer]
      exact Subgroup.mem_map_of_mem _ hg
    · rw [← M.modelImage_conj, ← hgu, ← he]
      exact Subgroup.map_mono hBu
  · rintro ⟨c, _, hc⟩
    have hq := (InnerTransport.quadratic_conj_iff ρ _ c).mpr M.fixedRoot_calculation.2.1
    intro a ha b hb v
    exact hq a (hc ha) b (hc hb) v

/-- Every remaining root actor is cubic but not quadratic, fixes the common
K-line, and attains the ratio 3/2 precisely when it is the whole root group. -/
theorem model_root_remaining_calculation (A : Subgroup G)
    (hAU : A ≤ M.modelImage (upperUnipotent (Field s))) (hne : A ≠ ⊥)
    (hout : ¬ ∃ c ∈
      Subgroup.normalizer (M.modelImage (upperUnipotent (Field s)) : Set G) ⊓ L,
      A ≤ (M.modelImage (fixedRootGroup s)).map (MulAut.conj c).toMonoidHom) :
    IsCubic ρ A ∧ ¬ IsQuadratic ρ A ∧
      fixedSpace ρ A = fixedSpace ρ (M.modelImage (upperUnipotent (Field s))) ∧
      Module.finrank (fixedField s) (M.fixedModelSpace A) = 1 ∧
      fixedCodim ρ A = 3 * s ∧ 3 / 2 ≤ actionRatio ρ A ∧
      (actionRatio ρ A = 3 / 2 ↔ A = M.modelImage (upperUnipotent (Field s))) := by
  have hAL := hAU.trans (M.modelImage_le_layer _)
  have hA := (M.upper_calculation.1).of_le hAU hne
  have hn := fun hq => hout ((M.model_root_quadratic_iff A hAU hne).mp hq)
  have he := M.modelImage_innerActor A hAL
  have hBU : M.innerActor A ≤ upperUnipotent (Field s) := by
    apply (Subgroup.map_le_map_iff_of_injective M.modelEmbedding_injective).mp
    change M.modelImage _ ≤ M.modelImage _
    rwa [he]
  have hnB : ¬ IsQuadratic (SL2.BinarySmall.hermitian s) (M.innerActor A) :=
    fun hq => hn (he ▸ (M.modelImage_quadratic_iff _).mpr hq)
  have hB := M.innerActor_elementary A hAL hA
  have hfixed : fixedSpace ρ A = fixedSpace ρ (M.modelImage (upperUnipotent (Field s))) := by
    rw [← he]
    ext v
    rw [M.mem_modelImage_fixedSpace_iff, M.mem_modelImage_fixedSpace_iff,
      fixedSpace_eq_upper_of_not_quadratic s _ hBU hnB]
  have hdim : Module.finrank (fixedField s) (M.fixedModelSpace A) = 1 := by
    have heq : M.fixedModelSpace A =
        M.fixedModelSpace (M.modelImage (upperUnipotent (Field s))) := by
      unfold fixedModelSpace
      rw [hfixed]
    rw [heq]
    exact M.model_upper_fixed_Kfinrank
  have hcalc := nonquadratic_root_calculation s _ hBU hB.1 hnB
  refine ⟨M.inner_cubic hAL hA, hn, hfixed, hdim,
    (M.inner_nonquadratic_calculation hAL hA hn).1,
    (M.inner_nonquadratic_calculation hAL hA hn).2, ?_⟩
  rw [← he, M.modelImage_actionRatio, hcalc.2.2.2]
  exact (Subgroup.map_injective M.modelEmbedding_injective).eq_iff.symm

/-- Adjoining an element outside the fixed-field line fixes just the common
K-line, retaining the literal join and original action. -/
theorem model_adjoin_outside_fixed_Kfinrank
    (g : SL) (hg : g ∈ upperUnipotent (Field s)) (hout : g ∉ fixedRootGroup s) :
    Module.finrank (fixedField s)
      (M.fixedModelSpace (M.modelImage (fixedRootGroup s) ⊔
        Subgroup.zpowers (M.modelEmbedding g))) = 1 := by
  have heq : M.fixedModelSpace (M.modelImage (fixedRootGroup s) ⊔
      Subgroup.zpowers (M.modelEmbedding g)) =
      M.fixedModelSpace (M.modelImage (upperUnipotent (Field s))) := by
    unfold fixedModelSpace
    rw [M.fixedSpace_adjoin_model_outside g hg hout]
  rw [heq]
  exact M.model_upper_fixed_Kfinrank


/-- The pure field lift normalizes the actual full root group. -/
theorem pure_lift_normalizes_model_root [Finite G] [L.Normal] {t : G}
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    t ∈ Subgroup.normalizer (M.modelImage (upperUnipotent (Field s)) : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    change t * M.modelEmbedding b * t⁻¹ ∈ M.modelImage (upperUnipotent (Field s))
    rw [M.conjugate_modelEmbedding ht]
    obtain ⟨u, rfl⟩ := (mem_upperUnipotent _ _).mp hb
    rw [Theory.PSL2.SemilinearCoverage.sl2FieldAut_uni]
    exact Subgroup.mem_map_of_mem _ ((mem_upperUnipotent _ _).mpr ⟨_, rfl⟩)
  · exact (Nat.card_congr ((M.modelImage (upperUnipotent (Field s))).equivMapOfInjective
      (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).toEquiv).le


end
end CFSG.Quasithin.ChapterK.RankOne.OrthogonalModel

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance orthogonalSylowSourceAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance orthogonalSylowSourceSpace : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The complete root partition and remaining-actor calculation on the
literal T∩L. The coordinate change is an actual layer action, and the
conjugating elements belong to the relative normalizer in L. -/
theorem SourceHypotheses.orthogonal_sylow_geometry (h : SourceHypotheses ρ L)
    (M : OrthogonalModel s ρ L) (T : Sylow 2 G) :
    ∃ P : OrthogonalModel s ρ L,
      P.modelImage (upperUnipotent (Field s)) = (T : Subgroup G) ⊓ L ∧
      (∀ a ∈ (T : Subgroup G) ⊓ L, a ≠ 1 →
        ∃! R : Subgroup G,
          (∃ c ∈ Subgroup.normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊓ L,
            R = (P.modelImage (fixedRootGroup s)).map (MulAut.conj c).toMonoidHom) ∧ a ∈ R) ∧
      (∀ A : Subgroup G, A ≤ (T : Subgroup G) ⊓ L → A ≠ ⊥ →
        (¬ ∃ c ∈ Subgroup.normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊓ L,
          A ≤ (P.modelImage (fixedRootGroup s)).map (MulAut.conj c).toMonoidHom) →
        IsCubic ρ A ∧ ¬ IsQuadratic ρ A ∧
          fixedSpace ρ A = fixedSpace ρ ((T : Subgroup G) ⊓ L) ∧
          Module.finrank (fixedField s) (P.fixedModelSpace A) = 1 ∧
          fixedCodim ρ A = 3 * s ∧ 3 / 2 ≤ actionRatio ρ A ∧
          (actionRatio ρ A = 3 / 2 ↔ A = (T : Subgroup G) ⊓ L)) ∧
      (∀ a ∈ (T : Subgroup G) ⊓ L, a ∉ P.modelImage (fixedRootGroup s) →
        fixedSpace ρ (P.modelImage (fixedRootGroup s) ⊔ Subgroup.zpowers a) =
          fixedSpace ρ ((T : Subgroup G) ⊓ L) ∧
        Module.finrank (fixedField s)
          (P.fixedModelSpace (P.modelImage (fixedRootGroup s) ⊔ Subgroup.zpowers a)) = 1) := by
  let : L.Normal := h.layer_normal
  obtain ⟨P, hP⟩ := M.exists_sylow_coordinates T
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · intro a ha hne
    rw [← hP] at ha ⊢
    exact P.model_root_partition ha hne
  · intro A hAT hne hout
    rw [← hP] at hAT hout ⊢
    exact P.model_root_remaining_calculation A hAT hne hout
  · intro a ha hout
    rw [← hP] at ha ⊢
    obtain ⟨g, hg, rfl⟩ := ha
    have hgout : g ∉ fixedRootGroup s :=
      fun hgR => hout (Subgroup.mem_map_of_mem _ hgR)
    exact ⟨P.fixedSpace_adjoin_model_outside g hg hgout,
      P.model_adjoin_outside_fixed_Kfinrank g hg hgout⟩

/-- Even extensions supply the same source t, R_t and X for any chosen T∩L.
The field transvection, its nonsingular moved line, the literal centralizers,
and all X calculations are asserted together on the original action. -/
theorem SourceHypotheses.orthogonal_sylow_outer_configuration
    (h : SourceHypotheses ρ L) (M : OrthogonalModel s ρ L)
    (T : Sylow 2 G) (heven : Even L.index) :
    ∃ (P : OrthogonalModel s ρ L) (t : G),
      P.modelImage (upperUnipotent (Field s)) = (T : Subgroup G) ⊓ L ∧
      t ^ 2 = 1 ∧ t ∉ L ∧
      t ∈ Subgroup.normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) (fixedField s) ≃*
        (Subgroup.centralizer ({t} : Set G) ⊓ L : Subgroup G)) ∧
      ((T : Subgroup G) ⊓ L) ⊓ Subgroup.centralizer ({t} : Set G) =
        P.modelImage (fixedRootGroup s) ∧
      P.outerActor t = (((T : Subgroup G) ⊓ L) ⊓
        Subgroup.centralizer ({t} : Set G)) ⊔ Subgroup.zpowers t ∧
      IsElementaryTwo (P.outerActor t) ∧ IsQuadratic ρ (P.outerActor t) ∧
      Module.finrank (fixedField s) (P.fixedModelSpace (P.outerActor t)) = 2 ∧
      rank (P.outerActor t) = s + 1 ∧
      actionRatio ρ (P.outerActor t) = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
      (∀ v, P.coordinates (ρ t v) =
        LinearEquiv.transvection (traceFunctional_movedVector s) (P.coordinates v)) ∧
      Set.range (fun v : V => P.coordinates (ρ t v - v)) =
        (Submodule.span (fixedField s) {movedVector s} : Set (Space s)) ∧
      ∀ X ∈ Set.range (fun v : V => P.coordinates (ρ t v - v)),
        X ≠ 0 → form s X ≠ 0 := by
  let : L.Normal := h.layer_normal
  obtain ⟨P, hP⟩ := M.exists_sylow_coordinates T
  obtain ⟨t, ht2, htL, ht⟩ := P.exists_outer_involution h heven
  have hreal := P.coordinates_pure_involution ht2 ht
  have hR : ((T : Subgroup G) ⊓ L) ⊓ Subgroup.centralizer ({t} : Set G) =
      P.modelImage (fixedRootGroup s) := by
    rw [← hP]
    exact P.root_centralizer_eq_modelImage ht
  have hn : t ∈ Subgroup.normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [← hP]
    exact P.pure_lift_normalizes_model_root ht
  refine ⟨P, t, hP, ht2, htL, hn, ⟨P.fixedFieldEquivLayerCentralizer ht⟩, hR,
    ?_, P.outerActor_elementary ht2 htL ht, P.outerActor_quadratic ht2 htL ht hreal,
    P.outerActor_fixed_Kfinrank ht2 htL ht hreal, P.outerActor_rank ht2 htL ht,
    P.outerActor_actionRatio ht2 htL ht hreal, P.coordinates_pure_involution_transvection ht2 ht,
    P.coordinates_pure_involution_moved_range ht2 ht, ?_⟩
  · rw [hR]
    rfl
  · exact fun _ hX hne => P.coordinates_pure_involution_moved_nonsingular ht2 ht hX hne


end CFSG.Quasithin.ChapterK.RankOne
