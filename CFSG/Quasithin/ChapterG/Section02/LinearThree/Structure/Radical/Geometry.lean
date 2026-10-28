module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.Action
public import Theory.SpecificGroups.PSL3.PointRadicalGeneration
public import Theory.GroupTheory.SylowKernelCore
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Transport of the full point radical in G.2.5

The actual starred U is transported through the supplied model of L*. The full
setwise point parabolic normalizes this image. The source point-fixing and
displacement identities place it in the concrete transvection radical, and
U* ≠ 1 survives transport under the explicit linear-image premise.

Thus U* lies in the two-core of the full starred point normalizer. The remaining
core/minimality and frame-generation facts are displayed explicitly in the
conditional assembly lemmas. Those lemmas transport the core, construct actual
F² coordinates and its cardinality, and lift matrix generation for the original
g and h. They do not assert that the model prerequisites have been discharged.
The final lemmas also prove that these original marked lines form a direct frame.

Source: Aschbacher–Smith, G.2.5(1–2), printed pp.335–336, and the full-normalizer
argument of G.2.3, printed pp.333–334. The two G.2.2 inputs U≤T and Φ(U)≤V₁
remain explicit, as does U*≤L*; no residual convention is changed.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

/-- The image of the actual starred U in the supplied SL₃ model. -/
def pointRadicalImage : Subgroup SL(3,F) :=
  ((D.star D.U).subgroupOf (D.star D.L)).map d.model.toMonoidHom

include d

/-- Full relative normality before transport to the matrix model. -/
theorem star_pointNormalizer_normalizes_U :
    D.star (D.L ⊓ D.G₁) ≤ normalizer (D.star D.U : Set D.Star) := by
  have hn : (D.L ⊓ D.G₁).subgroupOf D.LT ≤
      normalizer (D.U.subgroupOf D.LT : Set D.LT) := by
    rw [le_normalizer_iff]
    intro x hx u hu
    exact (mem_normalizer_iff.mp (d.pointNormalizer_normalizes_U hx) (u : G)).mp hu
  exact (map_mono hn).trans ((D.U.subgroupOf D.LT).le_normalizer_map _)

/-- The whole setwise point parabolic normalizes the transported U*. -/
theorem pointRadicalImage_normalized :
    Matrix.PSL3.PointRadicalGeneration.parabolic d.point ≤
      normalizer (d.pointRadicalImage : Set SL(3,F)) := by
  change MulAction.stabilizer SL(3,F) (d.point : Set (Fin 3 → F)) ≤ _
  rw [← d.pointNormalizer_model]
  exact (map_mono ((comap_mono d.star_pointNormalizer_normalizes_U).trans
    ((D.star D.U).le_normalizer_comap (D.star D.L).subtype))).trans
      (((D.star D.U).subgroupOf (D.star D.L)).le_normalizer_map d.model.toMonoidHom)

/-- Both defining transvection conditions hold for the actual U-image. -/
theorem pointRadicalImage_le_radical (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    d.pointRadicalImage ≤ Matrix.PSL3.PointRadicalGeneration.radical d.point := by
  rintro _ ⟨u,hu,rfl⟩
  refine ⟨?_, ?_⟩
  · intro v hv
    change (d.model u).val *ᵥ v = v
    rw [← d.starAction_on_L u v]
    exact congrArg Multiplicative.toAdd (d.starAction_U_fixes_point u hu v hv)
  · intro v
    change (d.model u).val *ᵥ v - v ∈ d.point
    rw [← d.starAction_on_L u v]
    exact d.starAction_U_displacement hUT hf u hu v

/-- The additional linear-image premise ensures transport loses none of U*. -/
noncomputable def pointRadicalImageEquiv (hUL : D.star D.U ≤ D.star D.L) :
    D.star D.U ≃* d.pointRadicalImage :=
  (subgroupOfEquivOfLe hUL).symm.trans
    (Subgroup.equivMapOfInjective _ d.model.toMonoidHom d.model.injective)

theorem pointRadicalImage_ne_bot (hUL : D.star D.U ≤ D.star D.L) :
    d.pointRadicalImage ≠ ⊥ := by
  intro he
  have hz : (D.star D.U).subgroupOf (D.star D.L) = ⊥ :=
    (map_eq_bot_iff_of_injective _ d.model.injective).mp he
  have hm := congrArg (fun A : Subgroup (D.star D.L) => A.map (D.star D.L).subtype) hz
  rw [map_subgroupOf_eq_of_le hUL, Subgroup.map_bot] at hm
  exact d.star_U_ne_bot hm

theorem pointRadicalImage_normal (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    (d.pointRadicalImage.subgroupOf
      (Matrix.PSL3.PointRadicalGeneration.parabolic d.point)).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    ((d.pointRadicalImage_le_radical hUT hf).trans
      (Matrix.PSL3.PointRadicalGeneration.radical_le_parabolic d.point))).mpr
        d.pointRadicalImage_normalized

/-- U* lies inside the full starred point normalizer, with the literal quotient maps. -/
theorem star_U_le_pointNormalizer (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L) :
    D.star D.U ≤ D.star (D.L ⊓ D.G₁) := by
  have hle := (d.pointRadicalImage_le_radical hUT hf).trans
    (Matrix.PSL3.PointRadicalGeneration.radical_le_parabolic d.point)
  change d.pointRadicalImage ≤ MulAction.stabilizer SL(3,F) (d.point : Set (Fin 3 → F)) at hle
  rw [← d.pointNormalizer_model] at hle
  have hle' := (Subgroup.map_le_map_iff_of_injective d.model.injective).mp hle
  intro u hu
  exact hle' (show (⟨u,hUL hu⟩ : D.star D.L) ∈
    (D.star D.U).subgroupOf (D.star D.L) from hu)

/-- The source hypotheses already give the easy direction of the core equality. -/
theorem star_U_le_pointNormalizer_core (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L) :
    D.star D.U ≤ (D.star (D.L ⊓ D.G₁)).pCoreIn 2 := by
  let := d.star_U_elementary hUT hf
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (D.star D.U))
    (d.star_U_le_pointNormalizer hUT hf hUL) d.star_pointNormalizer_normalizes_U



/-- The source cardinality supplies the characteristic needed by the model core theorem. -/
theorem radical_field_char_two : CharP F 2 := by
  let := Fintype.ofFinite F
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, d.field_card]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt d.exponent_pos))

open Matrix.PSL3.PointRadicalGeneration

/-- Application of the concrete minimal-normal-subgroup theorem to the actual U-image.
The model theorem remains an explicit prerequisite, not a source assumption. -/
theorem pointRadicalImage_eq_of_minimality (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L)
    (hminimal : ∀ A : Subgroup SL(3,F), A ≤ radical d.point → A ≠ ⊥ →
      parabolic d.point ≤ normalizer (A : Set SL(3,F)) → A = radical d.point) :
    d.pointRadicalImage = radical d.point :=
  hminimal _ (d.pointRadicalImage_le_radical hUT hf) (d.pointRadicalImage_ne_bot hUL)
    d.pointRadicalImage_normalized

/-- Transport of the full-parabolic core calculation through the literal model.
Both outstanding concrete model facts are explicit in this assembly lemma. -/
theorem star_U_eq_core_of_point_model_facts (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L)
    (hminimal : ∀ A : Subgroup SL(3,F), A ≤ radical d.point → A ≠ ⊥ →
      parabolic d.point ≤ normalizer (A : Set SL(3,F)) → A = radical d.point)
    (hcore : (parabolic d.point).pCoreIn 2 = radical d.point) :
    D.star D.U = (D.star (D.L ⊓ D.G₁)).pCoreIn 2 := by
  have hNL : D.star (D.L ⊓ D.G₁) ≤ D.star D.L := map_mono (comap_mono inf_le_left)
  let N := (D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L)
  have hc := map_pCoreIn_of_injective 2 N (D.star D.L).subtype
    (D.star D.L).subtype_injective
  rw [map_subgroupOf_eq_of_le hNL] at hc
  have he : (D.star D.U).subgroupOf (D.star D.L) = N.pCoreIn 2 := by
    apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
    rw [map_pCoreIn_of_injective 2 N d.model.toMonoidHom d.model.injective]
    change d.pointRadicalImage = (N.map d.model.toMonoidHom).pCoreIn 2
    rw [show N.map d.model.toMonoidHom = parabolic d.point from d.pointNormalizer_model,
      hcore]
    exact d.pointRadicalImage_eq_of_minimality hUT hf hUL hminimal
  calc
    D.star D.U = ((D.star D.U).subgroupOf (D.star D.L)).map (D.star D.L).subtype :=
      (map_subgroupOf_eq_of_le hUL).symm
    _ = (N.pCoreIn 2).map (D.star D.L).subtype := congrArg (Subgroup.map _) he
    _ = (D.star (D.L ⊓ D.G₁)).pCoreIn 2 := hc

/-- Coordinates on the actual starred U, conditional only on the model minimality input
in addition to the permitted source premises. -/
noncomputable def starUEquivOfMinimality (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L)
    (hminimal : ∀ A : Subgroup SL(3,F), A ≤ radical d.point → A ≠ ⊥ →
      parabolic d.point ≤ normalizer (A : Set SL(3,F)) → A = radical d.point) :
    D.star D.U ≃* Multiplicative (Fin 2 → F) :=
  (d.pointRadicalImageEquiv hUL).trans
    ((MulEquiv.subgroupCongr (d.pointRadicalImage_eq_of_minimality hUT hf hUL hminimal)).trans
      (radicalEquiv d.point d.point_dimension))

theorem card_star_U_of_minimality (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L)
    (hminimal : ∀ A : Subgroup SL(3,F), A ≤ radical d.point → A ≠ ⊥ →
      parabolic d.point ≤ normalizer (A : Set SL(3,F)) → A = radical d.point) :
    Nat.card (D.star D.U) = 2 ^ (2 * n) := by
  rw [Nat.card_congr (d.starUEquivOfMinimality hUT hf hUL hminimal).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
    Nat.card_fun, Nat.card_fin, d.field_card, ← pow_mul, Nat.mul_comm n 2]



/-- The original marked conjugator carries the literal U-image to the image of Uˣ.
No replacement of x by an element of the generated group is made. -/
theorem pointRadicalImage_conjugate_le (x : D.L) :
    d.pointRadicalImage.map (MulAut.conj (d.model (starProjection D x))⁻¹).toMonoidHom ≤
      ((D.star (conjugate D.U (x : G))).subgroupOf (D.star D.L)).map d.model.toMonoidHom := by
  rintro _ ⟨_,⟨u,hu,rfl⟩,rfl⟩
  let q : D.star D.L := (starProjection D x)⁻¹ * u * starProjection D x
  refine ⟨q, ?_, ?_⟩
  · obtain ⟨y,hy,he⟩ := hu
    let z : D.LT := inclusion (show D.L ≤ D.LT from le_sup_left) x
    refine ⟨z⁻¹ * y * z, ?_, ?_⟩
    · change (x : G)⁻¹ * (y : G) * (x : G) ∈ conjugate D.U (x : G)
      exact ⟨(y : G),hy,by simp⟩
    · change QuotientGroup.mk' (pCore 2 D.LT) (z⁻¹ * y * z) = (q : D.Star)
      simp only [map_mul,map_inv,he]
      rfl
  · change d.model q = (MulAut.conj (d.model (starProjection D x))⁻¹) (d.model u)
    simp [q]

/-- Generation in the concrete matrix model lifts to the exact star quotient.
The two model prerequisites remain explicit until their independent producers finish. -/
theorem star_I_eq_star_L_of_point_model_generation (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L)
    (hminimal : ∀ A : Subgroup SL(3,F), A ≤ radical d.point → A ≠ ⊥ →
      parabolic d.point ≤ normalizer (A : Set SL(3,F)) → A = radical d.point)
    (hgen : (radical d.point ⊔
        radical (conjugatePoint d.point (d.model (starProjection D ⟨g,d.g_mem⟩)))) ⊔
        radical (conjugatePoint d.point (d.model (starProjection D ⟨h,d.h_mem⟩))) = ⊤) :
    D.star (I D g h) = D.star D.L := by
  have hupper : D.star (I D g h) ≤ D.star D.L := by
    have hs : D.star (D.L ⊔ D.U) = D.star D.L ⊔ D.star D.U := by
      rw [Setup.star, subgroupOf_sup (show D.L ≤ D.LT from le_sup_left)
        (hUT.trans le_sup_right), Subgroup.map_sup]
      rfl
    have hh : D.star (I D g h) ≤ D.star (D.L ⊔ D.U) :=
      map_mono (comap_mono d.I_le_LU)
    rwa [hs, sup_eq_left.mpr hUL] at hh
  let K : Subgroup SL(3,F) := ((D.star (I D g h)).subgroupOf (D.star D.L)).map d.model.toMonoidHom
  have hmono {A B : Subgroup G} (hAB : A ≤ B) :
      ((D.star A).subgroupOf (D.star D.L)).map d.model.toMonoidHom ≤
        ((D.star B).subgroupOf (D.star D.L)).map d.model.toMonoidHom :=
    map_mono (comap_mono (map_mono (comap_mono hAB)))
  have h0 : radical d.point ≤ K := by
    rw [← d.pointRadicalImage_eq_of_minimality hUT hf hUL hminimal]
    exact hmono (show D.U ≤ I D g h from le_sup_left.trans le_sup_left)
  have hc (x : D.L) (hx : conjugate D.U (x : G) ≤ I D g h) :
      radical (conjugatePoint d.point (d.model (starProjection D x))) ≤ K := by
    rw [← radical_conjugate, ← d.pointRadicalImage_eq_of_minimality hUT hf hUL hminimal]
    exact (d.pointRadicalImage_conjugate_le x).trans (hmono hx)
  have hK : K = ⊤ := top_unique (hgen ▸ sup_le (sup_le h0
    (hc ⟨g,d.g_mem⟩ (le_sup_right.trans le_sup_left))) (hc ⟨h,d.h_mem⟩ le_sup_right))
  apply le_antisymm hupper
  intro q hq
  have hm : d.model ⟨q,hq⟩ ∈ K := hK ▸ mem_top _
  obtain ⟨u,hu,he⟩ := hm
  have huq : u = ⟨q,hq⟩ := d.model.injective he
  rw [huq] at hu
  exact hu



/-- The inverse-matrix point is exactly the original right conjugate of V₁. -/
theorem model_conjugatePoint_mem (x : D.L) (v : D.V) :
    (d.coordinates v).toAdd ∈ conjugatePoint d.point (d.model (starProjection D x)) ↔
      (v : G) ∈ conjugate D.V₁ (x : G) := by
  rw [mem_conjugatePoint, ← d.equivariant x v, ← d.point_mem]
  rw [Setup.conjugate, mem_map_equiv]
  simp

/-- The first two actual marked lines are disjoint in natural coordinates. -/
theorem model_points_disjoint : Disjoint d.point
    (conjugatePoint d.point (d.model (starProjection D ⟨g,d.g_mem⟩))) := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro v hv
  let w := d.coordinates.symm (Multiplicative.ofAdd v)
  have h0 : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (by simpa [w] using hv.1)
  have h1 : (w : G) ∈ conjugate D.V₁ g :=
    (d.model_conjugatePoint_mem ⟨g,d.g_mem⟩ w).mp (by simpa [w] using hv.2)
  have hw : (w : G) = 1 := mem_bot.mp (d.points_disjoint.le_bot ⟨h0,h1⟩)
  have he : w = 1 := Subtype.ext hw
  have hh := congrArg d.coordinates he
  simpa [w] using hh

/-- The third original marked line is disjoint from the sum of the first two. -/
theorem model_third_disjoint : Disjoint
    (d.point ⊔ conjugatePoint d.point (d.model (starProjection D ⟨g,d.g_mem⟩)))
    (conjugatePoint d.point (d.model (starProjection D ⟨h,d.h_mem⟩))) := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hv.1
  let w := d.coordinates.symm (Multiplicative.ofAdd v)
  let wa := d.coordinates.symm (Multiplicative.ofAdd a)
  let wb := d.coordinates.symm (Multiplicative.ofAdd b)
  have hwa : (wa : G) ∈ D.V₁ := (d.point_mem wa).mpr (by simpa [wa] using ha)
  have hwb : (wb : G) ∈ conjugate D.V₁ g :=
    (d.model_conjugatePoint_mem ⟨g,d.g_mem⟩ wb).mp (by simpa [wb] using hb)
  have hwprod : wa * wb = w := by
    apply d.coordinates.injective
    simp only [map_mul,wa,wb,w,d.coordinates.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd hab
  have hwsum : (w : G) ∈ D.V₁ ⊔ conjugate D.V₁ g := by
    rw [← hwprod]
    exact (D.V₁ ⊔ conjugate D.V₁ g).mul_mem (mem_sup_left hwa) (mem_sup_right hwb)
  have hwlast : (w : G) ∈ conjugate D.V₁ h :=
    (d.model_conjugatePoint_mem ⟨h,d.h_mem⟩ w).mp (by simpa [w] using hv.2)
  have hw : (w : G) = 1 := mem_bot.mp (d.third_disjoint.le_bot ⟨hwsum,hwlast⟩)
  have he : w = 1 := Subtype.ext hw
  have hh := congrArg d.coordinates he
  simpa [w] using hh



/-- The three source lines form a full frame, with the original marked g and h. -/
theorem model_points_span :
    (d.point ⊔ conjugatePoint d.point (d.model (starProjection D ⟨g,d.g_mem⟩))) ⊔
      conjugatePoint d.point (d.model (starProjection D ⟨h,d.h_mem⟩)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h01 := Submodule.finrank_sup_add_finrank_inf_eq d.point
    (conjugatePoint d.point (d.model (starProjection D ⟨g,d.g_mem⟩)))
  have h012 := Submodule.finrank_sup_add_finrank_inf_eq
    (d.point ⊔ conjugatePoint d.point (d.model (starProjection D ⟨g,d.g_mem⟩)))
    (conjugatePoint d.point (d.model (starProjection D ⟨h,d.h_mem⟩)))
  rw [d.model_points_disjoint.eq_bot, finrank_bot, add_zero, conjugatePoint_finrank,
    d.point_dimension] at h01
  rw [d.model_third_disjoint.eq_bot, finrank_bot, add_zero, conjugatePoint_finrank,
    d.point_dimension, h01] at h012
  simpa using h012

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
