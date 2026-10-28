module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.Invariance
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry

/-!
# The actual dual point map for G.2.5

The two point radicals centralize the first pair image. The plane stabilizer
factors as their join times the common point stabilizer, which normalizes both
original U-groups. This makes the orbit extension of the first pair image
well-defined and equivariant. Actual point transport identifies all three
annihilator marks. The triple-intersection kernel gives disjointness, and
the definition of S₃ gives spanning, including the case of zero images.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1–4 and G.2.5, printed pp.327–328,335–336.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
open Subgroup Setup Projective
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

namespace PointMap
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI)
  (σ : Representation (ZMod 2) (D.star D.L) M)
  (s : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
    (σ.comp e.projection))

/-- The binary image of a pair of literal frame groups. -/
def mark (i j : Fin 3) : Submodule (ZMod 2) M :=
  SectionGeometry.image s (frameW d i ⊓ frameW d j)

private def stabilizer (Q : Submodule (ZMod 2) M) : Subgroup (D.star D.L) where
  carrier := {a | Q.map (σ a) = Q}
  one_mem' := by
    change Q.map (σ 1) = Q
    rw [map_one]
    exact Submodule.map_id Q
  mul_mem' := by
    intro a b ha hb
    change Q.map (σ (a * b)) = Q
    rw [map_action_mul, hb, ha]
  inv_mem' := by
    intro a ha
    have hh := congrArg (fun R : Submodule (ZMod 2) M => R.map (σ a⁻¹)) ha
    rw [← map_action_mul, inv_mul_cancel, map_one] at hh
    exact hh.symm.trans (Submodule.map_id Q)

omit [Finite G] in
private theorem map_eq_of_fixed (Q : Submodule (ZMod 2) M) (a : D.star D.L)
    (ha : ∀ v ∈ Q, σ a v = v) : Q.map (σ a) = Q := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [ha w hw]
  · intro hv
    exact ⟨v, hv, ha v hv⟩

/-- The two point radicals centralize their actual pair image, by the Frattini bound. -/
private theorem pair_radicals_stabilize (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hrad : UpperRadicalIdentification d e) (i j : Fin 3) :
    rootGroup (naturalAction d) ((ModelGeometry.frame d).point i) ((ModelGeometry.frame d).point i) ⊔
      rootGroup (naturalAction d) ((ModelGeometry.frame d).point j) ((ModelGeometry.frame d).point j) ≤
        stabilizer σ (mark d e σ s i j) := by
  have hi : ((frameU d i).subgroupOf (I D g h)).map e.projection ≤
      stabilizer σ (mark d e σ s i j) := by
    rintro a ⟨u, hu, rfl⟩
    apply map_eq_of_fixed
    intro v hv
    exact SectionGeometry.fixes_image s (frameU d i) (frameW d i ⊓ frameW d j)
      ((commutator_mono le_rfl (inf_le_left.trans inf_le_left)).trans
        (frame_derived d hUT hf i)) u hu v hv
  have hj : ((frameU d j).subgroupOf (I D g h)).map e.projection ≤
      stabilizer σ (mark d e σ s i j) := by
    rintro a ⟨u, hu, rfl⟩
    apply map_eq_of_fixed
    intro v hv
    exact SectionGeometry.fixes_image s (frameU d j) (frameW d i ⊓ frameW d j)
      ((commutator_mono le_rfl (inf_le_right.trans inf_le_left)).trans
        (frame_derived d hUT hf j)) u hu v hv
  rw [frame_radical_image d e hrad i] at hi
  rw [frame_radical_image d e hrad j] at hj
  exact sup_le hi hj

/-- Point transport in the model transports the literal lower pair images. -/
theorem transport (a : D.star D.L) (i j k m : Fin 3)
    (hi : ((ModelGeometry.frame d).point i).map (naturalAction d a) = (ModelGeometry.frame d).point k)
    (hj : ((ModelGeometry.frame d).point j).map (naturalAction d a) = (ModelGeometry.frame d).point m) :
    (mark d e σ s i j).map (σ a) = mark d e σ s k m := by
  obtain ⟨l, rfl⟩ := starProjection_surjective D a
  have hi' := point_transports_W d hLI l (frameConjugator d i) (frameConjugator d k)
    (by simpa only [← frame_point] using hi)
  have hj' := point_transports_W d hLI l (frameConjugator d j) (frameConjugator d m)
    (by simpa only [← frame_point] using hj)
  have hp : conjugate (frameW d i ⊓ frameW d j) (l : G)⁻¹ = frameW d k ⊓ frameW d m := by
    change ((frameW d i ⊓ frameW d j).map (MulAut.conj (l : G)⁻¹⁻¹).toMonoidHom) = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (l : G)⁻¹⁻¹).injective]
    exact congrArg₂ (fun A B : Subgroup G => A ⊓ B) hi' hj'
  have he := SectionGeometry.image_conjugate s (frameW d i ⊓ frameW d j) (inclusion hLI l)
  simpa only [mark, MonoidHom.comp_apply, e.projection_on_L, Subgroup.coe_inclusion, hp] using he.symm

/-- The plane stabilizer fixes the chosen binary mark. Its two-radical factor
acts trivially, and its common-point factor normalizes both original groups. -/
theorem stabilizer_invariant (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hrad : UpperRadicalIdentification d e) (a : D.star D.L)
    (ha : (dualPoint d).val.map (dualAction d a) = (dualPoint d).val) :
    (mark d e σ s 0 1).map (σ a) = mark d e σ s 0 1 := by
  obtain ⟨r, hr, t, ht₀, ht₁, rfl⟩ := ModelGeometry.dualPoint_stabilizer_decomposition d a ha
  rw [map_action_mul, transport d e σ s t 0 1 0 1 ht₀ ht₁]
  exact pair_radicals_stabilize d e σ s hUT hf hrad 0 1 hr

/-- Extend the literal first pair image along the genuine dual projective orbit. -/
noncomputable def map : Point F (Module.Dual F (Fin 3 → F)) → Submodule (ZMod 2) M :=
  orbitMap (dualAction d) σ (dualPoint d) (mark d e σ s 0 1)

theorem mark_eq (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e) :
    map d e σ s (dualPoint d) = mark d e σ s 0 1 :=
  orbitMap_mark (dualAction d) σ (dualPoint d) _ (stabilizer_invariant d e σ s hUT hf hrad)

theorem equivariant (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e)
    (a : D.star D.L) (A B : Point F (Module.Dual F (Fin 3 → F)))
    (hAB : B.val = A.val.map (dualAction d a)) :
    map d e σ s B = (map d e σ s A).map (σ a) :=
  orbitMap_equivariant (dualAction d) σ (dualPoint d) _
    (ModelGeometry.dual_exists_point_map d (dualPoint d))
    (stabilizer_invariant d e σ s hUT hf hrad) a A B hAB

private theorem frame_distinct (i j : Fin 3) (hij : i ≠ j) :
    (⟨(ModelGeometry.frame d).point i, (ModelGeometry.frame d).dimension i⟩ : Point F (Fin 3 → F)) ≠
      ⟨(ModelGeometry.frame d).point j, (ModelGeometry.frame d).dimension j⟩ := by
  have hd : Disjoint ((ModelGeometry.frame d).point i) ((ModelGeometry.frame d).point j) := by
    fin_cases i <;> fin_cases j <;> simp_all
    · exact natural_points_disjoint d
    · exact (natural_third_disjoint d).mono_left le_sup_left
    · exact (natural_points_disjoint d).symm
    · exact (natural_third_disjoint d).mono_left le_sup_right
    · exact ((natural_third_disjoint d).mono_left le_sup_left).symm
    · exact ((natural_third_disjoint d).mono_left le_sup_right).symm
  intro he
  have he' := congrArg Subtype.val he
  change (ModelGeometry.frame d).point i = (ModelGeometry.frame d).point j at he'
  rw [he'] at hd
  have hz := disjoint_self.mp hd
  have hh := (ModelGeometry.frame d).dimension j
  rw [hz] at hh
  simp at hh

/-- Every pair in the marked frame has exactly its prescribed annihilator value. -/
theorem pair_mark (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e)
    (i j : Fin 3) (hij : i ≠ j) (P : Point F (Module.Dual F (Fin 3 → F)))
    (hP : P.val = ((ModelGeometry.frame d).point i ⊔ (ModelGeometry.frame d).point j).dualAnnihilator) :
    map d e σ s P = mark d e σ s i j := by
  obtain ⟨a, ha₀, ha₁⟩ := ModelGeometry.natural_exists_point_pair_map d
    (naturalPoint d) (conjugatePoint d ⟨g, d.g_mem⟩)
    ⟨(ModelGeometry.frame d).point i, (ModelGeometry.frame d).dimension i⟩
    ⟨(ModelGeometry.frame d).point j, (ModelGeometry.frame d).dimension j⟩
    (naturalPoint_ne_conjugate_g d) (frame_distinct d i j hij)
  have hp : P.val = (dualPoint d).val.map (dualAction d a) := by
    change P.val = (pairPlane d).dualAnnihilator.map (dualAction d a)
    rw [← dualAnnihilator_map, pairPlane, Submodule.map_sup, hP]
    rw [show d.point.map (naturalAction d a) = (ModelGeometry.frame d).point i from ha₀, ha₁]
  rw [equivariant d e σ s hUT hf hrad a _ P hp, mark_eq d e σ s hUT hf hrad]
  exact transport d e σ s a 0 1 i j ha₀ ha₁

/-- Disjointness at the first two marks follows from the literal triple-intersection kernel. -/
theorem marked_disjoint (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    Disjoint (mark d e σ s 0 1) (mark d e σ s 0 2) := by
  apply Submodule.disjoint_def.mpr
  intro v hv₁ hv₂
  obtain ⟨a, ha, hav⟩ := (SectionGeometry.mem_image s _ _).mp hv₁
  obtain ⟨b, hb, hbv⟩ := (SectionGeometry.mem_image s _ _).mp hv₂
  have hab : (a : G) * (b : G)⁻¹ ∈ S₂ D g h := by
    apply (s.coordinates_eq_one_iff (a * b⁻¹)).mp
    rw [map_mul, map_inv, show s.coordinates a = s.coordinates b from hav.trans hbv.symm,
      mul_inv_cancel]
  have ha₂ : (a : G) ∈ frameW d 0 ⊓ frameW d 2 := by
    have he := ((frameW d 0) ⊓ frameW d 2).mul_mem
      (le_inf (denominator_le_frameW d hUT hf hLI 0)
        (denominator_le_frameW d hUT hf hLI 2) hab) hb
    simpa only [inv_mul_cancel_right] using he
  have haE : (a : G) ∈ S₂ D g h := by
    rw [d.S₂_eq_triple_W hUT hf hLI]
    obtain ⟨h₀, h₁, h₂⟩ := frameW_values d hLI
    exact ⟨⟨h₀ ▸ ha.1, h₁ ▸ ha.2⟩, h₂ ▸ ha₂.2⟩
  exact hav.symm.trans ((s.coordinates_eq_one_iff a).mpr haE)

theorem disjoint (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e)
    (A B : Point F (Module.Dual F (Fin 3 → F))) (hAB : A ≠ B) :
    Disjoint (map d e σ s A) (map d e σ s B) := by
  have hne : dualPoint d ≠ dualPointH d := by
    intro he
    have hz := disjoint_self.mp ((congrArg Subtype.val he) ▸ dual_points_disjoint d)
    have hh := (dualPointH d).property
    rw [hz] at hh
    simp at hh
  obtain ⟨a, ha, hb⟩ := ModelGeometry.dual_exists_point_pair_map d
    (dualPoint d) (dualPointH d) A B hne hAB
  rw [equivariant d e σ s hUT hf hrad a _ A ha.symm,
    equivariant d e σ s hUT hf hrad a _ B hb.symm,
    mark_eq d e σ s hUT hf hrad,
    pair_mark d e σ s hUT hf hrad 0 2 (by decide) (dualPointH d) rfl]
  exact Submodule.disjoint_map (σ.apply_bijective a).injective (marked_disjoint d e σ s hUT hf)

theorem spanning (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hrad : UpperRadicalIdentification d e) :
    (⨆ A, map d e σ s A) = ⊤ := by
  have hjoin := frame_pair_join d hLI 0 1 2 (by decide) (by decide) (by decide)
  have h₀ : frameW d 0 ⊓ frameW d 1 ≤ S₃ D g h := by rw [← hjoin]; exact le_sup_left.trans le_sup_left
  have h₁ : frameW d 0 ⊓ frameW d 2 ≤ S₃ D g h := by rw [← hjoin]; exact le_sup_right.trans le_sup_left
  have h₂ : frameW d 1 ⊓ frameW d 2 ≤ S₃ D g h := by rw [← hjoin]; exact le_sup_right
  have hs := congrArg (SectionGeometry.image s) hjoin
  rw [SectionGeometry.image_sup s _ _ (sup_le h₀ h₁) h₂,
    SectionGeometry.image_sup s _ _ h₀ h₁, SectionGeometry.image_self] at hs
  apply top_unique
  rw [← hs]
  apply sup_le (sup_le ?_ ?_) ?_
  · change mark d e σ s 0 1 ≤ _
    rw [← mark_eq d e σ s hUT hf hrad]
    exact le_iSup (map d e σ s) (dualPoint d)
  · change mark d e σ s 0 2 ≤ _
    rw [← pair_mark d e σ s hUT hf hrad 0 2 (by decide) (dualPointH d) rfl]
    exact le_iSup (map d e σ s) (dualPointH d)
  · change mark d e σ s 1 2 ≤ _
    rw [← pair_mark d e σ s hUT hf hrad 1 2 (by decide) (dualPointGH d) rfl]
    exact le_iSup (map d e σ s) (dualPointGH d)

end PointMap

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
