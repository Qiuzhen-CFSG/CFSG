module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.RootStep
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry.Basic
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.NaturalGeometry.RootAction

/-!
# Ambient lifts of the actual SL₃ frame

The kernel of the compatible star projection centralizes V, so the original
natural coordinates intertwine conjugation by every element of I. A model
point stabilizer therefore normalizes the corresponding original U-conjugate.
The first radical identification transports to every L-conjugate, and genuine
point transporters carry both those U-groups and their intersections with S.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1–4 and G.2.5, printed pp.327–328,335–336.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
open Subgroup Setup Projective
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d in
theorem I_le_LT (hUT : D.U ≤ D.T) : I D g h ≤ D.LT := by
  have hc (x : D.L) : conjugate D.U (x : G) ≤ D.LT := by
    rintro _ ⟨u, hu, rfl⟩
    change (x : G)⁻¹ * u * (x : G)⁻¹⁻¹ ∈ D.LT
    rw [inv_inv]
    exact D.LT.mul_mem (D.LT.mul_mem (D.LT.inv_mem (mem_sup_left x.property))
      (mem_sup_right (hUT hu))) (mem_sup_left x.property)
  exact sup_le (sup_le (hUT.trans le_sup_right) (hc ⟨g, d.g_mem⟩)) (hc ⟨h, d.h_mem⟩)

/-- Conjugation on V by an actor of I, in the original source subgroup. -/
def actVector (hUT : D.U ≤ D.T) (a : I D g h) (v : D.V) : D.V :=
  ⟨(a : G) * v * (a : G)⁻¹,
    (mem_normalizer_iff.mp (d.I_normalizes hUT a.property) v).mp v.property⟩

include d in
theorem projection_equivariant (hUT : D.U ≤ D.T) {hLI : D.L ≤ I D g h}
    (e : StarComparison D g h hLI) (a : I D g h) (v : D.V) :
    (d.coordinates (actVector d hUT a v)).toAdd =
      naturalAction d (e.projection a) (d.coordinates v).toAdd := by
  obtain ⟨l, hl⟩ := starProjection_surjective D (e.projection a)
  let b : I D g h := (inclusion hLI l)⁻¹ * a
  have hb : (b : G) ∈ S D g h := by
    change b ∈ (S D g h).subgroupOf (I D g h)
    rw [← e.projection_ker]
    change e.projection b = 1
    simp only [b, map_mul, map_inv, e.projection_on_L, hl, inv_mul_cancel]
  have hvb : (b : G) * v = (v : G) * b :=
    (d.central_first hUT hLI v.property).2 _ hb
  have he : actVector d hUT a v = actVector d hUT (inclusion hLI l) v := by
    apply Subtype.ext
    change (a : G) * v * (a : G)⁻¹ = (l : G) * v * (l : G)⁻¹
    have ha : (a : G) = (l : G) * b := by simp [b]
    rw [ha]
    calc
      (l : G) * b * v * ((l : G) * b)⁻¹ = (l : G) * ((b : G) * v) * ((b : G)⁻¹ * (l : G)⁻¹) := by group
      _ = (l : G) * v * (l : G)⁻¹ := by rw [hvb]; group
  rw [he, ← hl]
  exact d.equivariant l v

include d in
theorem conjugatePoint_normalizes (hUT : D.U ≤ D.T) {hLI : D.L ≤ I D g h}
    (e : StarComparison D g h hLI) (a : I D g h) (x : D.L)
    (ha : (conjugatePoint d x).val.map (naturalAction d (e.projection a)) =
      (conjugatePoint d x).val) :
    (a : G) ∈ normalizer (conjugate D.V₁ (x : G) : Set G) := by
  have hp : conjugate D.V₁ (x : G) ≤ D.V := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [conjugateVector] using (conjugateVector d x ⟨v, d.setup.point_le hv⟩).property
  apply mem_normalizer_iff.mpr
  intro v
  constructor
  · intro hv
    let v' : D.V := ⟨v, hp hv⟩
    apply (conjugatePoint_mem d x (actVector d hUT a v')).mpr
    rw [projection_equivariant d hUT e]
    rw [← ha]
    exact ⟨_, (conjugatePoint_mem d x v').mp hv, rfl⟩
  · intro hv
    have hvV : v ∈ D.V :=
      (mem_normalizer_iff.mp (d.I_normalizes hUT a.property) v).mpr (hp hv)
    let v' : D.V := ⟨v, hvV⟩
    apply (conjugatePoint_mem d x v').mpr
    have hc := (conjugatePoint_mem d x (actVector d hUT a v')).mp hv
    rw [projection_equivariant d hUT e, ← ha] at hc
    obtain ⟨w, hw, he⟩ := hc
    exact ((naturalAction d).apply_bijective _).injective he ▸ hw

/-- A root fixing a model point normalizes that point's original U-group. -/
theorem conjugatePoint_normalizes_U (hUT : D.U ≤ D.T) {hLI : D.L ≤ I D g h}
    (e : StarComparison D g h hLI) (a : I D g h) (x : D.L)
    (ha : (conjugatePoint d x).val.map (naturalAction d (e.projection a)) =
      (conjugatePoint d x).val) :
    (a : G) ∈ normalizer (conjugate D.U (x : G) : Set G) :=
  conjugatePointNormalizerLT_normalizes_U d x
    ⟨I_le_LT d hUT a.property, conjugatePoint_normalizes d hUT e a x ha⟩

/-- The three literal conjugators of the source frame. -/
def frameConjugator : Fin 3 → D.L := ![1, ⟨g, d.g_mem⟩, ⟨h, d.h_mem⟩]

def frameU (i : Fin 3) : Subgroup G := conjugate D.U (frameConjugator d i : G)

def frameW (i : Fin 3) : Subgroup G := frameU d i ⊓ S D g h

omit [Finite G] in
@[simp] theorem conjugate_one (A : Subgroup G) : conjugate A 1 = A := by
  change A.map (MulAut.conj (1 : G)⁻¹).toMonoidHom = A
  simp
  exact Subgroup.map_id A

@[simp] theorem conjugatePoint_one : conjugatePoint d 1 = naturalPoint d := by
  apply Subtype.ext
  change d.point.map (naturalAction d ((starProjection D 1)⁻¹)) = d.point
  simp
  exact Submodule.map_id d.point

theorem frame_point (i : Fin 3) :
    (ModelGeometry.frame d).point i = (conjugatePoint d (frameConjugator d i)).val := by
  fin_cases i
  · simp [ModelGeometry.frame, frameConjugator, naturalPoint]
  · rfl
  · rfl

theorem frameU_le_I (i : Fin 3) : frameU d i ≤ I D g h := by
  fin_cases i
  · simpa [frameU, frameConjugator] using (show D.U ≤ I D g h from le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem frameW_values (hLI : D.L ≤ I D g h) :
    frameW d 0 = W D g h ∧ frameW d 1 = conjugate (W D g h) g ∧
      frameW d 2 = conjugate (W D g h) h := by
  refine ⟨?_, ?_, ?_⟩
  · simp [frameW, frameU, frameConjugator, W]
  · exact (conjugate_W D g h g (hLI d.g_mem)).symm
  · exact (conjugate_W D g h h (hLI d.h_mem)).symm

/-- The radical identification at V₁ transports to every original L-conjugate. -/
theorem conjugate_radical_image {hLI : D.L ≤ I D g h}
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) (x : D.L) :
    ((conjugate D.U (x : G)).subgroupOf (I D g h)).map e.projection =
      rootGroup (naturalAction d) (conjugatePoint d x).val (conjugatePoint d x).val := by
  let t := starProjection D x
  have hforward : (conjugatePoint d x).val.map (naturalAction d t) = d.point := by
    change (d.point.map (naturalAction d t⁻¹)).map (naturalAction d t) = d.point
    rw [← Submodule.map_comp]
    have he : (naturalAction d t).comp (naturalAction d t⁻¹) = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact (naturalAction d).self_inv_apply t v
    rw [he, Submodule.map_id]
  have hback : d.point.map (naturalAction d t⁻¹) = (conjugatePoint d x).val := rfl
  have hUI : D.U ≤ I D g h := le_sup_left.trans le_sup_left
  apply le_antisymm
  · rintro a ⟨v, hv, rfl⟩
    obtain ⟨u, hu, he⟩ := hv
    let u' : I D g h := ⟨u, hUI hu⟩
    have hproj : e.projection v = t⁻¹ * e.projection u' * t := by
      have he' : v = (inclusion hLI x)⁻¹ * u' * inclusion hLI x := by
        apply Subtype.ext
        simpa using he.symm
      rw [he', map_mul, map_mul, map_inv, e.projection_on_L]
    have hu' : e.projection u' ∈ rootGroup (naturalAction d) d.point d.point := by
      rw [← hrad]
      exact ⟨u', hu, rfl⟩
    rw [hproj]
    exact root_conjugate_mem (naturalAction d) (conjugatePoint d x) (naturalPoint d)
      d.point t (e.projection u') hforward le_rfl hu'
  · intro a ha
    have hr := root_conjugate_mem (naturalAction d) (naturalPoint d) (conjugatePoint d x)
      (conjugatePoint d x).val t⁻¹ a hback le_rfl ha
    simp only [inv_inv] at hr
    change t * a * t⁻¹ ∈ rootGroup (naturalAction d) d.point d.point at hr
    rw [← hrad] at hr
    obtain ⟨u, hu, heu⟩ := hr
    let v : I D g h := (inclusion hLI x)⁻¹ * u * inclusion hLI x
    refine ⟨v, ?_, ?_⟩
    · exact ⟨u, hu, by simp [v]⟩
    · change e.projection ((inclusion hLI x)⁻¹ * u * inclusion hLI x) = a
      rw [map_mul, map_mul, map_inv, e.projection_on_L, heu]
      change t⁻¹ * (t * a * t⁻¹) * t = a
      group

theorem frame_radical_image {hLI : D.L ≤ I D g h}
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) (i : Fin 3) :
    ((frameU d i).subgroupOf (I D g h)).map e.projection =
      rootGroup (naturalAction d) ((ModelGeometry.frame d).point i) ((ModelGeometry.frame d).point i) := by
  rw [frame_point]
  exact conjugate_radical_image d e hrad (frameConjugator d i)


/-- Composition of represented subspace images, in left-action order. -/
theorem map_action_mul {R X K : Type*} [Semiring R] [AddCommMonoid X] [Module R X]
    [Group K] (σ : Representation R K X) (A : Submodule R X) (a b : K) :
    A.map (σ (a * b)) = (A.map (σ b)).map (σ a) := by
  rw [← Submodule.map_comp, map_mul]
  rfl

theorem map_action_inv {R X K : Type*} [Semiring R] [AddCommMonoid X] [Module R X]
    [Group K] (σ : Representation R K X) (A : Submodule R X) (a : K) :
    (A.map (σ a⁻¹)).map (σ a) = A := by
  rw [← map_action_mul, mul_inv_cancel, map_one]
  exact Submodule.map_id A

/-- A model transporter of two marked points transports their original U-groups. -/
theorem point_transports_U (l x y : D.L)
    (hl : (conjugatePoint d x).val.map (naturalAction d (starProjection D l)) =
      (conjugatePoint d y).val) :
    conjugate (conjugate D.U (x : G)) (l : G)⁻¹ = conjugate D.U (y : G) := by
  have hp : d.point.map (naturalAction d (starProjection D (y * l * x⁻¹))) = d.point := by
    rw [(starProjection D).map_mul, (starProjection D).map_mul, (starProjection D).map_inv]
    rw [map_action_mul, map_action_mul]
    change ((conjugatePoint d x).val.map (naturalAction d (starProjection D l))).map
      (naturalAction d (starProjection D y)) = d.point
    rw [hl]
    exact map_action_inv (naturalAction d) d.point (starProjection D y)
  have hn : ((y * l * x⁻¹ : D.L) : G) ∈ normalizer (D.U : Set G) :=
    pointNormalizer_normalizes_U d ⟨(y * l * x⁻¹).property,
      natural_stabilizer_mem_G₁ d _ hp⟩
  ext v
  have hm (A : Subgroup G) (a v : G) : v ∈ conjugate A a ↔ a * v * a⁻¹ ∈ A := by
    change v ∈ A.map (MulAut.conj a⁻¹).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp
  rw [hm, hm, hm]
  have hc := mem_normalizer_iff.mp hn ((x : G) * ((l : G)⁻¹ * v * (l : G)⁻¹⁻¹) * (x : G)⁻¹)
  have he : ((y * l * x⁻¹ : D.L) : G) *
      ((x : G) * ((l : G)⁻¹ * v * (l : G)⁻¹⁻¹) * (x : G)⁻¹) *
      (((y * l * x⁻¹ : D.L) : G))⁻¹ = (y : G) * v * (y : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he] at hc
  exact hc

/-- The same transporter acts on the intersections with the literal two-core. -/
theorem point_transports_W (hLI : D.L ≤ I D g h) (l x y : D.L)
    (hl : (conjugatePoint d x).val.map (naturalAction d (starProjection D l)) =
      (conjugatePoint d y).val) :
    conjugate ((conjugate D.U (x : G)) ⊓ S D g h) (l : G)⁻¹ =
      (conjugate D.U (y : G)) ⊓ S D g h := by
  change ((conjugate D.U (x : G) ⊓ S D g h).map (MulAut.conj (l : G)⁻¹⁻¹).toMonoidHom) = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (l : G)⁻¹⁻¹).injective]
  have hs : (S D g h).map (MulAut.conj (l : G)⁻¹⁻¹).toMonoidHom = S D g h := by
    rw [inv_inv]
    exact mem_normalizer_iff_map_conj_eq.mp (I_normalizes_core D g h (hLI l.property))
  rw [hs]
  exact congrArg (fun A => A ⊓ S D g h) (point_transports_U d l x y hl)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
