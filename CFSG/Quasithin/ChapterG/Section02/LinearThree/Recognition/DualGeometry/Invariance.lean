module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.FrameLifts
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.ModelGeometry.RootGeneration

/-!
# Full I-invariance of the third G.2.5 layer

A root in Uᵢ fixing the j-th point normalizes Uⱼ. Its displacement on each
pair intersection lies in Wᵢ∩Wⱼ; the other two intersections are fixed modulo
S₂ by the Frattini bound. Thus every frame root has a lift normalizing S₃.
The six roots generate L*, while the projection kernel S already normalizes
S₃. Lifting generation through that kernel proves I≤N_G(S₃) without assuming
an action on the lower quotient or a recognition conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1–4 and G.2.5, printed pp.327–328,335–336.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
open Subgroup Setup Projective
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

omit [Finite G] in
private theorem three_pair_root_step (C E U₀ U₁ U₂ R : Subgroup G)
    (h₀ : C ≤ normalizer (U₀ : Set G)) (h₁ : C ≤ normalizer (U₁ : Set G))
    (hRC : R ≤ normalizer (C : Set G)) (hRU : R ≤ U₀)
    (hR₁ : R ≤ normalizer (U₁ : Set G))
    (hder : ⁅U₀, U₀⁆ ≤ E) (hE : E ≤ (U₀ ⊓ C) ⊓ (U₁ ⊓ C)) :
    let A := (U₀ ⊓ C) ⊓ (U₁ ⊓ C)
    let B := (U₀ ⊓ C) ⊓ (U₂ ⊓ C)
    let Z := (U₁ ⊓ C) ⊓ (U₂ ⊓ C)
    R ≤ normalizer (((A ⊔ B) ⊔ Z : Subgroup G) : Set G) ∧
      ⁅(A ⊔ B) ⊔ Z, R⁆ ≤ A := by
  let A := (U₀ ⊓ C) ⊓ (U₁ ⊓ C)
  let B := (U₀ ⊓ C) ⊓ (U₂ ⊓ C)
  let Z := (U₁ ⊓ C) ⊓ (U₂ ⊓ C)
  have hAN : C ≤ normalizer (A : Set G) :=
    (le_inf ((le_inf h₀ C.le_normalizer).trans inf_normalizer_le_normalizer_inf)
      ((le_inf h₁ C.le_normalizer).trans inf_normalizer_le_normalizer_inf)).trans
        inf_normalizer_le_normalizer_inf
  have hA : ⁅A, R⁆ ≤ A :=
    ((commutator_mono (inf_le_left.trans inf_le_left) hRU).trans hder).trans hE
  have hB : ⁅B, R⁆ ≤ A :=
    ((commutator_mono (inf_le_left.trans inf_le_left) hRU).trans hder).trans hE
  have hZC : Z ≤ C := inf_le_left.trans inf_le_right
  have hZ₀ : ⁅Z, R⁆ ≤ U₀ ⊓ C := by
    refine le_inf ?_ ?_
    · rw [commutator_comm]
      exact (commutator_mono hRU hZC).trans
        (le_normalizer_iff_commutator_le_left.mp h₀)
    · exact (commutator_mono hZC le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hRC)
  have hZ₁ : ⁅Z, R⁆ ≤ U₁ :=
    (commutator_mono (inf_le_left.trans inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hR₁)
  have hZ : ⁅Z, R⁆ ≤ A := le_inf hZ₀ (le_inf hZ₁ (hZ₀.trans inf_le_right))
  have hp : (A ⊔ B) ⊔ Z ≤ commutatorPreimage C R A :=
    sup_le (sup_le
      (le_commutatorPreimage (inf_le_left.trans inf_le_right) hA)
      (le_commutatorPreimage (inf_le_left.trans inf_le_right) hB))
      (le_commutatorPreimage hZC hZ)
  have hm : ⁅(A ⊔ B) ⊔ Z, R⁆ ≤ A :=
    (commutator_mono hp le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hAN)
  exact ⟨le_normalizer_iff_commutator_le_left.mpr
    (hm.trans (le_sup_left.trans le_sup_left)), hm⟩

theorem frame_pair_join (hLI : D.L ≤ I D g h) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((frameW d i ⊓ frameW d j) ⊔ (frameW d i ⊓ frameW d k)) ⊔
      (frameW d j ⊓ frameW d k) = S₃ D g h := by
  unfold S₃
  rw [conjugate_W D g h g (hLI d.g_mem), conjugate_W D g h h (hLI d.h_mem)]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [frameW, frameU, frameConjugator, W,
      inf_comm, sup_comm, sup_left_comm, sup_assoc]

theorem denominator_le_frameW (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) (i : Fin 3) :
    S₂ D g h ≤ frameW d i := by
  obtain ⟨h₀, h₁, h₂⟩ := frameW_values d hLI
  rw [d.S₂_eq_triple_W hUT hf hLI]
  fin_cases i
  · change _ ≤ frameW d 0
    rw [h₀]; exact inf_le_left.trans inf_le_left
  · change _ ≤ frameW d 1
    rw [h₁]; exact inf_le_left.trans inf_le_right
  · change _ ≤ frameW d 2
    rw [h₂]; exact inf_le_right

theorem frame_derived (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (i : Fin 3) :
    ⁅frameU d i, frameU d i⁆ ≤ S₂ D g h := by
  have hVE := (d.intersection hUT hf).1
  fin_cases i
  · simpa [frameU, frameConjugator] using
      (((derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans d.setup.point_le).trans hVE)
  · exact (conjugate_derived_le d hUT hf g d.g_mem).trans hVE
  · exact (conjugate_derived_le d hUT hf h d.h_mem).trans hVE

/-- Every one of the six source frame-root lifts preserves S₃. -/
theorem frame_root_step (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (i j : Fin 3) (hij : i ≠ j) :
    frameU d i ⊓ normalizer (frameU d j : Set G) ≤ normalizer (S₃ D g h : Set G) ∧
      ⁅S₃ D g h, frameU d i ⊓ normalizer (frameU d j : Set G)⁆ ≤
        frameW d i ⊓ frameW d j := by
  have hn (k : Fin 3) : S D g h ≤ normalizer (frameU d k : Set G) := by
    fin_cases k
    · simpa [frameU, frameConjugator] using hU
    · exact hUg
    · exact hUh
  obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j <;> simp_all <;> decide
  have hr := three_pair_root_step (S D g h) (S₂ D g h)
    (frameU d i) (frameU d j) (frameU d k)
    (frameU d i ⊓ normalizer (frameU d j : Set G)) (hn i) (hn j)
    ((inf_le_left.trans (frameU_le_I d i)).trans (I_normalizes_core D g h))
    inf_le_left inf_le_right (frame_derived d hUT hf i)
    (le_inf (denominator_le_frameW d hUT hf hLI i) (denominator_le_frameW d hUT hf hLI j))
  change (frameU d i ⊓ normalizer (frameU d j : Set G) ≤ normalizer
    ((((frameW d i ⊓ frameW d j) ⊔ (frameW d i ⊓ frameW d k)) ⊔
      (frameW d j ⊓ frameW d k) : Subgroup G) : Set G)) ∧
    ⁅((frameW d i ⊓ frameW d j) ⊔ (frameW d i ⊓ frameW d k)) ⊔
      (frameW d j ⊓ frameW d k), _⁆ ≤ frameW d i ⊓ frameW d j at hr
  simpa only [frame_pair_join d hLI i j k hij hik hjk] using hr

/-- The root-generation argument proves the full source I-invariance, before
constructing either quotient representation or a projective point map. -/
theorem I_normalizes_third (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (e : StarComparison D g h hLI) (hrad : UpperRadicalIdentification d e) :
    I D g h ≤ normalizer (S₃ D g h : Set G) := by
  let N := (normalizer (S₃ D g h : Set G)).subgroupOf (I D g h)
  have hroots (i j : Fin 3) (hij : i ≠ j) :
      rootGroup (naturalAction d) ((ModelGeometry.frame d).point i)
        ((ModelGeometry.frame d).point i ⊔ (ModelGeometry.frame d).point j) ≤ N.map e.projection := by
    intro a ha
    have hrad' : a ∈ rootGroup (naturalAction d) ((ModelGeometry.frame d).point i)
        ((ModelGeometry.frame d).point i) := ⟨ha.1, fun v hv => ha.2 v (Submodule.mem_sup_left hv)⟩
    rw [← frame_radical_image d e hrad i] at hrad'
    obtain ⟨u, hu, rfl⟩ := hrad'
    have hj : (conjugatePoint d (frameConjugator d j)).val.map
        (naturalAction d (e.projection u)) = (conjugatePoint d (frameConjugator d j)).val := by
      rw [← frame_point]
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [ha.2 w (Submodule.mem_sup_right hw)]
        exact hw
      · intro hv
        exact ⟨v, hv, ha.2 v (Submodule.mem_sup_right hv)⟩
    have hnorm := conjugatePoint_normalizes_U d hUT e u (frameConjugator d j) hj
    exact ⟨u, (frame_root_step d hUT hf hLI hU hUg hUh i j hij).1 ⟨hu, hnorm⟩, rfl⟩
  have hN : N.map e.projection = ⊤ := by
    apply top_unique
    rw [← ModelGeometry.frame_roots_generate d]
    exact iSup_le fun i => iSup_le fun j => iSup_le (hroots i j)
  intro a ha
  obtain ⟨b, hb, he⟩ := (show e.projection ⟨a, ha⟩ ∈ N.map e.projection by rw [hN]; trivial)
  have hk : ((⟨a, ha⟩ : I D g h) * b⁻¹ : I D g h) ∈ e.projection.ker := by
    change e.projection (⟨a, ha⟩ * b⁻¹) = 1
    rw [map_mul, map_inv]
    rw [he, mul_inv_cancel]
  rw [e.projection_ker] at hk
  have hc := core_normalizes_third d hLI hU hUg hUh hk
  have hm := (normalizer (S₃ D g h : Set G)).mul_mem hc hb
  change a * (b : G)⁻¹ * (b : G) ∈ normalizer (S₃ D g h : Set G) at hm
  simpa only [inv_mul_cancel_right] using hm

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
