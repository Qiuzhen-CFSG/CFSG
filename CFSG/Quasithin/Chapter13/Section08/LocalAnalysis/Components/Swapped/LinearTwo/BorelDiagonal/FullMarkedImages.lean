module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.ProjectedImages
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
public import Theory.GroupTheory.PPerfectHom

/-!
# Full marked images under the source factor projection

Once L₁ = O²(B₀), it surjects onto the binary Borel, which is two-perfect.
The source marks are normal in L₁, so their full binary images are normal.
Their cubic quotients make the images nontrivial. Factor exchange and
two-perfectness then force both projected images to equal the first Borel.
The comparison with the original star map retains every surviving two-core.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

private theorem binary_twoPerfect (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (S : Sylow 2 (Q × Q)) : IsPPerfect 2 (BinaryBorel.borel S) := by
  let e := BinaryBorel.coordinates S
  have hp : IsPPerfect 2 (BinaryBorel.borel (BinaryBorel.firstSylow S) ×
      BinaryBorel.borel (BinaryBorel.secondSylow S)) := by
    intro N hN hQ
    let := hN
    let q := QuotientGroup.mk' N
    have h₁ := (BinaryBorel.factor_twoPerfect (n := 2) (by decide) hmodel
      (BinaryBorel.firstSylow S)).hom_eq_one_of_isPGroup hQ (q.comp (MonoidHom.inl _ _))
    have h₂ := (BinaryBorel.factor_twoPerfect (n := 2) (by decide) hmodel
      (BinaryBorel.secondSylow S)).hom_eq_one_of_isPGroup hQ (q.comp (MonoidHom.inr _ _))
    apply top_unique
    rintro ⟨a, b⟩ _
    apply (QuotientGroup.eq_one_iff _).mp
    have ha : q (a, 1) = 1 := DFunLike.congr_fun h₁ a
    have hb : q (1, b) = 1 := DFunLike.congr_fun h₂ b
    calc
      q (a, b) = q ((a, 1) * (1, b)) := by simp
      _ = 1 := by rw [map_mul, ha, hb, one_mul]
  exact hp.of_surjective e.symm.toMonoidHom e.symm.surjective

variable (H K₀ : Subgroup G) (hK : K₀ ≤ H)
  (e : Source.starImage H K₀ ≃* Q × Q)
  (S : Sylow 2 (Source.starImage H K₀))
local notation "B₀" => SourceTorus.chosenLift H K₀ hK S
local notation "S'" => SourceTorus.chosenSylow H K₀ e S
local notation "f" => SourceTorus.toBinary H K₀ hK e S

/-- The genuine residual covers the whole binary Borel at field order four. -/
theorem residual_binary_surjective (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (L₁ : Subgroup G) (hLB : L₁ ≤ B₀)
    (hres : L₁ = residual B₀) : Function.Surjective ((f).comp (inclusion hLB)) := by
  have hm : (pResidual 2 B₀).map f = ⊤ := by
    rw [map_pResidual_of_surjective 2 f (SourceTorus.toBinary_surjective H K₀ hK e S),
      (pResidual_eq_top_iff 2 _).mpr (binary_twoPerfect hmodel S')]
  intro y
  obtain ⟨b, hb, he⟩ := (show y ∈ (pResidual 2 B₀).map f by rw [hm]; trivial)
  have hbL : b.val ∈ L₁ := by rw [hres]; exact ⟨b, hb, rfl⟩
  exact ⟨⟨b.val, hbL⟩, he⟩

omit [Finite Q] in
private theorem image_via_overgroup (A X : Subgroup G) (hAB : A ≤ B₀) (hXA : X ≤ A) :
    (X.subgroupOf A).map ((f).comp (inclusion hAB)) = (X.subgroupOf B₀).map f := by
  rw [← map_map]
  congr 1
  apply map_injective (B₀).subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le (hXA.trans hAB)]
  change (X.subgroupOf A).map A.subtype = X
  exact map_subgroupOf_eq_of_le hXA

omit [Finite Q] in
private theorem image_twoPerfect (X : Subgroup G) (hXB : X ≤ B₀) (hp : IsPPerfect 2 X) :
    IsPPerfect 2 ((X.subgroupOf B₀).map f) := by
  have h := hp.of_surjective (subgroupOfEquivOfLe hXB).symm.toMonoidHom
    (subgroupOfEquivOfLe hXB).symm.surjective
  exact h.of_surjective ((f).subgroupMap _) ((f).subgroupMap_surjective _)

private theorem image_ne_bot (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (X : Subgroup G) (hXB : X ≤ B₀) (hc : Nat.card (X ⧸ pCore 2 X) = 3) :
    (X.subgroupOf B₀).map f ≠ ⊥ := by
  intro hz
  have hm : SourceActions.Markings.image B₀ X
      (SourceTorus.toCommonTori H K₀ hK e S (n := 2) (by decide) hmodel) = ⊥ := by
    change (X.subgroupOf B₀).map
      ((SourceActions.binaryToCommon H K₀ e S (n := 2) (by decide) hmodel).comp f) = ⊥
    rw [← map_map, hz, Subgroup.map_bot]
  have hc' := SourceActions.Markings.image_card B₀ X hXB
    (SourceTorus.toCommonTori H K₀ hK e S (n := 2) (by decide) hmodel)
    (by rw [SourceTorus.toCommonTori_ker]; exact pCore_isPGroup)
    (SourceActions.commonTori_odd H K₀ e S (n := 2) (by decide) hmodel)
  rw [hm, hc] at hc'
  norm_num only [card_bot] at hc'

omit [Finite Q] in
/-- The full binary image is exactly the image of the literal star subgroup
in the marked product coordinates. -/
theorem binary_image_eq_star_image (X : Subgroup G) (hXB : X ≤ B₀) :
    ((X.subgroupOf B₀).map f).map (BinaryBorel.borel S').subtype =
      ((Source.starImage H X).subgroupOf (Source.starImage H K₀)).map e.toMonoidHom := by
  have hXH := hXB.trans ((borelLift_le H K₀ hK _).trans hK)
  apply le_antisymm
  · rintro _ ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e.symm (f x), ?_, e.apply_symm_apply _⟩
    change (e.symm (f x) : Source.Hstar H) ∈ Source.starImage H X
    rw [SourceActions.toBinary_star H K₀ hK e S]
    exact ⟨⟨x.val, hXH hx⟩, hx, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, he⟩ := hz
    let b : B₀ := ⟨x.val, hXB hx⟩
    have hh : e.symm (f b) = z := by
      apply Subtype.ext
      rw [SourceActions.toBinary_star H K₀ hK e S]
      exact he
    have hh' : (f b : Q × Q) = e z := by rw [← hh, e.apply_symm_apply]
    exact ⟨f b, ⟨b, hx, rfl⟩, hh'⟩


/-- The literal first-factor projection on the orbit star group. -/
noncomputable def factorProjection : Source.starImage H K₀ →* Q :=
  (MonoidHom.fst Q Q).comp e.toMonoidHom

omit [Finite G] [Finite Q] in
/-- The actual factor projection is onto the first component. -/
theorem factorProjection_surjective : Function.Surjective (factorProjection H K₀ e) := by
  intro x
  exact ⟨e.symm (x, 1), by simp [factorProjection]⟩

omit [Finite G] [Finite Q] in
theorem factorProjection_apply (x : Source.starImage H K₀) :
    factorProjection H K₀ e x = (e x).1 := rfl

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion
variable {G : Type*} [Group G] [Finite G]
variable (H K T : Subgroup G) (hTH : T ≤ H) {t : G} (ht : t ∈ T)
  (hK : K ⊔ K.conjBy t ≤ H)
  (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
  (htn : t ∉ normalizer (K : Set G))
  (e : Source.starImage H (K ⊔ K.conjBy t) ≃*
    Source.starImage H K × Source.starImage H K)
  (he : ∀ a b, (e.symm (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
    (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩ * b *
      (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩)⁻¹))
  (S : Sylow 2 (Source.starImage H (K ⊔ K.conjBy t)))
local notation "K₀" => K ⊔ K.conjBy t
local notation "B₀" => SourceTorus.chosenLift H K₀ hK S
local notation "S'" => SourceTorus.chosenSylow H K₀ e S
local notation "f" => SourceTorus.toBinary H K₀ hK e S

include he hK in
omit [Finite G] in
/-- The projection kernel is exactly the other marked star component. -/
theorem factorProjection_kernel :
    (factorProjection H K₀ e).ker =
      (Source.starImage H (K.conjBy t)).subgroupOf (Source.starImage H K₀) := by
  have hc := SourceActions.coordinate_second_image H K (hTH ht) e he (le_sup_left.trans hK)
  ext x
  constructor
  · intro hx
    have hm := mem_map_of_mem (SourceActions.coordinateInclusion H K e)
      (show e x ∈ (MonoidHom.fst _ _).ker from hx)
    rw [hc] at hm
    change (e.symm (e x) : Source.Hstar H) ∈ Source.starImage H (K.conjBy t) at hm
    change (x : Source.Hstar H) ∈ Source.starImage H (K.conjBy t)
    simpa only [e.symm_apply_apply] using hm
  · intro hx
    obtain ⟨y, hy, heq⟩ := (show (x : Source.Hstar H) ∈
      (MonoidHom.fst _ _).ker.map (SourceActions.coordinateInclusion H K e) by rw [hc]; exact hx)
    have heq' : e.symm y = x := Subtype.ext heq
    change (e x).1 = 1
    rw [← heq', e.apply_symm_apply]
    exact hy

include hi htn he in
/-- Full marked images under the genuine factor projection coincide. This
instantiates the intrinsic projection theorem using source normality,
two-perfectness, cubic quotients and the constructed moving conjugation. -/
theorem marked_full_images
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 4)
    {L V V₁ V₃ : Subgroup G} (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hLB : one L T V₁ ≤ B₀) (hTB : T ≤ normalizer (B₀ : Set G))
    (hres : one L T V₁ = residual B₀) :
    ((Source.starImage H (zero L)).subgroupOf (Source.starImage H K₀)).map
        (factorProjection H K₀ e) =
      ((Source.starImage H (plus L T V₁)).subgroupOf (Source.starImage H K₀)).map
        (factorProjection H K₀ e) := by
  have hzL := LocalAction.zero_le_one_of_factorization L T V₁ hfactor
  have hpL := plus_le_one L T V₁ d.line_stable
  have hzB := hzL.trans hLB
  have hpB := hpL.trans hLB
  have hsurj := residual_binary_surjective H K₀ hK e S hmodel _ hLB hres
  have hnK := SourceActions.normalizes_orbit H K (le_sup_left.trans hK) hi (hTH ht) htn
  let τ := SourceActions.binaryAction H K₀ hK e S (hTH ht) (hnK (hTH ht)) (hTB ht)
  have hτ := (SourceActions.binary_moving_exchanges H K (hTH ht) hK hi htn e he S
    (hnK (hTH ht)) (hTB ht)).2
  let Z := ((zero L).subgroupOf B₀).map f
  let P := ((plus L T V₁).subgroupOf B₀).map f
  have hZn : ((zero L).subgroupOf (one L T V₁)).Normal :=
    normal_subgroupOf_of_le_normalizer (LocalAction.one_normalizes_zero L T V₁ d.normalizes_L)
  have hPn : ((plus L T V₁).subgroupOf (one L T V₁)).Normal :=
    normal_subgroupOf_of_le_normalizer (one_normalizes_plus L T V₁)
  let _ : Z.Normal := by
    dsimp only [Z]
    rw [← image_via_overgroup H K₀ hK e S (one L T V₁) (zero L) hLB hzL]
    exact hZn.map _ hsurj
  let _ : P.Normal := by
    dsimp only [P]
    rw [← image_via_overgroup H K₀ hK e S (one L T V₁) (plus L T V₁) hLB hpL]
    exact hPn.map _ hsurj
  have hZ := SourceActions.binary_image_invariant H K₀ hK e S (zero L)
    (hTH ht) (hnK (hTH ht)) (hTB ht)
    (normalizer_le_zero_normalizer L (d.normalizes_L ht))
  have hP := SourceActions.binary_image_invariant H K₀ hK e S (plus L T V₁)
    (hTH ht) (hnK (hTH ht)) (hTB ht)
    (T_normalizes_plus L T V₁ d.normalizes_L d.line_stable ht)
  have him := BorelProjections.marked_ambient_images_eq hmodel S' τ hτ Z P hZ hP
    (image_ne_bot H K₀ hK e S hmodel _ hzB d.zero_core_card)
    (image_ne_bot H K₀ hK e S hmodel _ hpB (d.plus_core_card hfactor))
    (image_twoPerfect H K₀ hK e S _ hzB (residual_isPPerfect _))
    (image_twoPerfect H K₀ hK e S _ hpB (residual_isPPerfect _))
  change (((zero L).subgroupOf B₀).map f |>.map (BinaryBorel.borel S').subtype).map _ =
    (((plus L T V₁).subgroupOf B₀).map f |>.map (BinaryBorel.borel S').subtype).map _ at him
  rw [binary_image_eq_star_image H K₀ hK e S _ hzB,
    binary_image_eq_star_image H K₀ hK e S _ hpB, map_map, map_map] at him
  exact him

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion
end
