module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.RadicalImage.Point
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.RadicalImage.Transport

/-! The original radical comparison in Aschbacher--Smith 11.5.7, pp.781--782.
The actual outer action detects its image, and the Sylow intersection of its
kernel lies in O₂(LT). The solvable residual L₁ remains unchanged. -/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
open LocalGeometry Matrix.PSL3 Matrix.PSL3.PointRadicalGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
  (a : SL(3, E.input.field.Carrier))

/-- On subgroups of L, the projective action is the marked inner action. -/
theorem image_component (A : Subgroup G) (hA : A ≤ L) :
    image E m a A = ((componentImage E m A).map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj.comp (projection E.input.field.Carrier)) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨MulAut.conj a (componentMap E m ⟨x,hA hx⟩),
      ⟨componentMap E m ⟨x,hA hx⟩,⟨⟨x,hA hx⟩,hx,rfl⟩,rfl⟩,?_⟩
    exact (projectiveAction_component E m a ⟨x,hA hx⟩).symm
  · rintro ⟨y,⟨s,⟨l,hl,rfl⟩,rfl⟩,rfl⟩
    refine ⟨inclusion le_sup_left l,hl,?_⟩
    exact projectiveAction_component E m a l

/-- Rotating the genuine line sends the actual L₁ image to the standard inner local. -/
theorem image_residual
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (ha : conjugatePoint standardPoint a = P) :
    image E m a E.L₁ = (LinearThree.OuterExtensions.localFactor E.input.field.Carrier true).map MulAut.conj := by
  rw [image_component E m a E.L₁ E.L₁_le,
    componentImage_residual_conjugate E m P hpoint a ha]
  have he : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom =
      MonoidHom.id SL(3,E.input.field.Carrier) := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [Subgroup.map_map _ (MulAut.conj a).toMonoidHom,he,Subgroup.map_id,← Subgroup.map_map]
  rfl

private theorem image_sup (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    image E m a (A ⊔ B) = image E m a A ⊔ image E m a B := by
  unfold image
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

private theorem preserves_of_normalizes_inner
    (U : Subgroup PSL(3,E.input.field.Carrier))
    (b : MulAut PSL(3,E.input.field.Carrier))
    (hb : b ∈ normalizer (U.map MulAut.conj : Set _)) : U.map b.toMonoidHom = U := by
  rw [mem_normalizer_iff_map_conj_eq] at hb
  have he : (MulAut.conj b : MulAut PSL(3,E.input.field.Carrier) →* _).comp MulAut.conj =
      MulAut.conj.comp b.toMonoidHom := by
    ext x y
    simp
  rw [Subgroup.map_map,he,←Subgroup.map_map] at hb
  exact map_injective (Matrix.PSL3.ExtensionBorel.inner_injective E.input.field.Carrier) hb

/-- The native outer-extension core calculation now applies to the original R₁. -/
theorem radical_image_le_closure (n : NaturalPair E)
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (ha : conjugatePoint standardPoint a = P)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hKL : E.K = E.L₁)
    (hWK : E.W = E.K.pCoreIn 2) :
    image E m a E.R₁ ≤ image E m a E.W := by
  have hKL' : E.K ≤ L := hKL ▸ E.L₁_le
  have hlocal : image E m a E.K =
      (LinearThree.OuterExtensions.localFactor E.input.field.Carrier true).map MulAut.conj := by
    rw [hKL]; exact image_residual E m a P hpoint ha
  have hn := image_normalizes E m a E.K (T : Subgroup G) (hTG.trans E.G₁_normalizes_K)
  rw [hlocal] at hn
  have hc := LinearThree.OuterExtensions.AmbientLocalCores.local_join_core_in_aut
    E.input.field.Carrier E.input.field.degree_pos E.input.field.card_eq true
    (image E m a (T : Subgroup G)) (fun b hb => preserves_of_normalizes_inner E _ b (hn hb))
  rw [closure_image_core E m a n hKL' hWK,hlocal]
  have hr : E.R₁ = (E.K ⊔ (T : Subgroup G)).pCoreIn 2 := by rw [hKL]; rfl
  rw [hr]
  have hh := core_image_le E m a (E.K ⊔ (T : Subgroup G))
    (sup_le (hKL'.trans le_sup_left) le_sup_right)
  rw [image_sup E m a E.K (T : Subgroup G) (hKL'.trans le_sup_left) le_sup_right,
    hlocal,hc] at hh
  exact hh

/-- Lift the actual projective image comparison through the original quotient kernel. -/
theorem radical_le_closure_join_core (n : NaturalPair E)
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hKL : E.K = E.L₁)
    (hWK : E.W = E.K.pCoreIn 2) :
    E.R₁ ≤ E.W ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator P hdim
  have hi := radical_image_le_closure E m a n P hpoint ha hTG hKL hWK
  have hRT : E.R₁ ≤ (T : Subgroup G) := by
    simpa only [Geometry.R₁,Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWR : E.W ≤ E.R₁ := by
    rw [hWK,Geometry.R₁,←hKL]
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le E.K.le_normalizer (hTG.trans E.G₁_normalizes_K))
  intro r hr
  let r' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨r,mem_sup_right (hRT hr)⟩
  obtain ⟨w,hw,he⟩ := hi ⟨r',hr,rfl⟩
  have hk : r' * w⁻¹ ∈ (projectiveAction E m a).ker := by
    change projectiveAction E m a (r' * w⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hd : r * (w : G)⁻¹ ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sylow_inf_projective_kernel_le_core E m a
      ⟨(T : Subgroup G).mul_mem (hRT hr) ((T : Subgroup G).inv_mem (hRT (hWR hw))),
        r' * w⁻¹,hk,rfl⟩
  have hh := (E.W ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
    (mem_sup_right hd) (mem_sup_left hw)
  change r * (w : G)⁻¹ * (w : G) ∈ _ at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
