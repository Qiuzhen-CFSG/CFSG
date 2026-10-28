module

public import Theory.GroupTheory.Commutator.ConjugateGeneration
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Algebra for the MS93 local normalizer arguments

The first calculation removes the nested commutator supplement in a nilpotent
subgroup Q. For W = A[A,B]C, the given bound implies W ≤ AC[W,Q]; nilpotent
saturation gives W = AC. This proves both normalizer conclusions without
assuming that the ambient group is finite or that AC is normal in W.

The second calculation generates a specified subgroup F using only conjugates
of Z escaping K, together with T. The escaping span is normalized by K and by
itself, hence by the entire relative conjugate span. The product F = F₀T then
places every conjugate in the escaping span joined with T. Applying this to a
local normalizer gives simultaneous escape for two T-normal subgroups.

All conjugations are right conjugations and all spans are relative to F.
Since F normalizes its conjugate span, the join generation hypothesis is
equivalent to the source product hypothesis.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.10), p.854, and (2.1)(vi--vii), pp.855--856. The citation to (1.9)
in the printed proof of (2.1)(vii) refers to the generation lemma (1.10).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
variable {G : Type*} [Group G]

private lemma normalizes_commutator (A B C : Subgroup G)
    (hAB : A ≤ normalizer B) (hAC : A ≤ normalizer C) :
    A ≤ normalizer (⁅B,C⁆ : Subgroup G) := by
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hAB ha),
    mem_normalizer_iff_map_conj_eq.mp (hAC ha)]

private lemma normalizes_sup (A B C : Subgroup G)
    (hAB : A ≤ normalizer B) (hAC : A ≤ normalizer C) :
    A ≤ normalizer (B ⊔ C : Subgroup G) :=
  (le_inf hAB hAC).trans (normalizer_inf_normalizer_le_normalizer_sup B C)

private lemma normalizes_sup_commutator (A B : Subgroup G) :
    B ≤ normalizer (A ⊔ ⁅A,B⁆ : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hmap : A.map (MulAut.conj b).toMonoidHom ≤ A ⊔ ⁅A,B⁆ := by
    rintro _ ⟨a,ha,rfl⟩
    have hc : ⁅b,a⁆ ∈ ⁅A,B⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hb ha
    have hh := (A ⊔ ⁅A,B⁆).mul_mem (mem_sup_right hc) (mem_sup_left ha)
    simpa [commutatorElement_def, mul_assoc] using hh
  have hm : (A ⊔ ⁅A,B⁆).map (MulAut.conj b).toMonoidHom ≤ A ⊔ ⁅A,B⁆ := by
    rw [Subgroup.map_sup]
    exact sup_le hmap ((mem_normalizer_iff_map_conj_eq.mp
      (normalizer_commutator_ge_right A B hb)).le.trans le_sup_right)
  exact hm (mem_map_of_mem (MulAut.conj b).toMonoidHom hx)

private lemma commutator_sup_of_centralizes (A C Q : Subgroup G)
    (hAQ : A ≤ Q) (hCQ : C ≤ Q) (hc : ⁅C,Q⁆ = ⊥) :
    ⁅A ⊔ C,Q⁆ = ⁅A,Q⁆ := by
  let f : Bool → Subgroup G := fun b => if b then A else C
  have hf : (⨆ b, f b) = A ⊔ C := by simp [iSup_bool_eq, f]
  have h := commutator_iSup_of_le f Q (by intro b; cases b <;> assumption)
  rw [hf] at h
  simpa [iSup_bool_eq, f, hc] using h

/-- The nested commutator hypothesis removes its own supplement by nilpotence. -/
theorem nilpotent_normalization (A B C Q : Subgroup G)
    (hQ : Group.IsNilpotent Q) (hAQ : A ≤ Q) (hCQ : C ≤ Q)
    (hQA : Q ≤ normalizer A) (hBQ : B ≤ normalizer Q)
    (hBC : B ≤ normalizer C) (hC : ⁅C,Q⁆ = ⊥)
    (hcomm : ⁅A,B⁆ ≤ ⁅⁅A,Q⁆,B⁆ ⊔ C) :
    B ≤ normalizer (A ⊔ C : Subgroup G) ∧
    B ≤ normalizer (⁅A,Q⁆ ⊔ C : Subgroup G) := by
  let W := (A ⊔ ⁅A,B⁆) ⊔ C
  have hAW : A ≤ W := le_sup_left.trans le_sup_left
  have hCW : C ≤ W := le_sup_right
  have hBW : B ≤ normalizer W :=
    normalizes_sup _ _ _ (normalizes_sup_commutator A B) hBC
  have hWQ : W ≤ Q := sup_le (sup_le hAQ
    ((commutator_mono hAQ le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hBQ))) hCQ
  have hBN : B ≤ normalizer (⁅W,Q⁆ : Subgroup G) :=
    normalizes_commutator _ _ _ hBW hBQ
  have hsmall : ⁅⁅A,Q⁆,B⁆ ≤ ⁅W,Q⁆ :=
    (commutator_mono (commutator_mono hAW le_rfl) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hBN)
  have hQC : Q ≤ normalizer C :=
    le_normalizer_iff_commutator_le_left.mpr (by rw [hC]; exact bot_le)
  have hWH : W ≤ A ⊔ C := le_of_le_sup_commutator_of_isNilpotent Q W (A ⊔ C) Q
    hQ hWQ (sup_le hAQ hCQ) le_rfl (normalizes_sup _ _ _ hQA hQC)
    (sup_le (sup_le (le_sup_left.trans le_sup_left)
      (hcomm.trans (sup_le (hsmall.trans le_sup_right) (le_sup_right.trans le_sup_left))))
      (le_sup_right.trans le_sup_left))
  have hEq : W = A ⊔ C := le_antisymm hWH (sup_le hAW hCW)
  have hBH : B ≤ normalizer (A ⊔ C : Subgroup G) := hEq ▸ hBW
  refine ⟨hBH, ?_⟩
  have hn := normalizes_commutator _ _ _ hBH hBQ
  rw [commutator_sup_of_centralizes A C Q hAQ hCQ hC] at hn
  exact normalizes_sup _ _ _ hn hBC
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
variable {G : Type*} [Group G]

/-- Right conjugation, in the convention of the source. -/
def rightConjugate (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

private lemma rightConjugate_one (A : Subgroup G) : rightConjugate A 1 = A := by
  unfold rightConjugate
  have he : (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [he, map_id]

private lemma rightConjugate_mul (A : Subgroup G) (g h : G) :
    rightConjugate (rightConjugate A g) h = rightConjugate A (g*h) := by
  rw [rightConjugate, rightConjugate, map_map, rightConjugate]
  congr 1
  ext a
  simp [mul_assoc]

private lemma rightConjugate_eq (A : Subgroup G) {g : G} (hg : g ∈ normalizer A) :
    rightConjugate A g = A :=
  mem_normalizer_iff_map_conj_eq.mp (inv_mem hg)

private lemma normalizes_of_rightConjugate_le (A B : Subgroup G)
    (h : ∀ b ∈ B, rightConjugate A b ≤ A) : B ≤ normalizer A := by
  apply le_normalizer_iff.mpr
  intro b hb a ha
  have ht := h b⁻¹ (B.inv_mem hb) (mem_map_of_mem (MulAut.conj (b⁻¹)⁻¹).toMonoidHom ha)
  simpa [MulAut.conj_apply] using ht

/-- Conjugate generation only by elements of the specified overgroup. -/
noncomputable def conjugatesIn (Z F : Subgroup G) : Subgroup G :=
  ⨆ g : F, rightConjugate Z g

/-- The subfamily whose conjugates are not contained in K. -/
noncomputable def escapingConjugates (Z F K : Subgroup G) : Subgroup G :=
  ⨆ g : F, ⨆ (_ : ¬ rightConjugate Z g ≤ K), rightConjugate Z g

private lemma conjugate_le_conjugatesIn (Z F : Subgroup G) (g : F) :
    rightConjugate Z g ≤ conjugatesIn Z F := le_iSup (fun g : F => rightConjugate Z g) g

private lemma conjugate_le_escaping (Z F K : Subgroup G) (g : F)
    (hg : ¬ rightConjugate Z g ≤ K) : rightConjugate Z g ≤ escapingConjugates Z F K :=
  le_iSup_of_le g (le_iSup_of_le hg le_rfl)

theorem conjugatesIn_le (Z F : Subgroup G) (hZF : Z ≤ F) : conjugatesIn Z F ≤ F := by
  apply iSup_le
  intro g
  exact (map_mono hZF).trans (rightConjugate_eq F (F.le_normalizer g.property)).le

theorem conjugatesIn_normalized (Z F : Subgroup G) : F ≤ normalizer (conjugatesIn Z F) := by
  apply normalizes_of_rightConjugate_le
  intro f hf
  simp only [conjugatesIn, rightConjugate, Subgroup.map_iSup]
  apply iSup_le
  intro g
  change rightConjugate (rightConjugate Z g) f ≤ conjugatesIn Z F
  rw [rightConjugate_mul]
  exact le_iSup_of_le (⟨g*f, F.mul_mem g.property hf⟩ : F) le_rfl

private lemma escapingConjugates_le (Z F K : Subgroup G) :
    escapingConjugates Z F K ≤ conjugatesIn Z F := by
  exact iSup_le fun g => iSup_le fun _ => conjugate_le_conjugatesIn Z F g

private lemma escapingConjugates_normalized (Z F K : Subgroup G) (hKF : K ≤ F) :
    K ≤ normalizer (escapingConjugates Z F K) := by
  apply normalizes_of_rightConjugate_le
  intro k hk
  simp only [escapingConjugates, rightConjugate, Subgroup.map_iSup]
  apply iSup_le
  intro g
  apply iSup_le
  intro hg
  change rightConjugate (rightConjugate Z g) k ≤ escapingConjugates Z F K
  rw [rightConjugate_mul]
  have hescape : ¬ rightConjugate Z (g*k) ≤ K := by
    intro hn
    have hh := map_mono (f := (MulAut.conj k).toMonoidHom) hn
    have hh : rightConjugate (rightConjugate Z (g*k)) k⁻¹ ≤
        rightConjugate K k⁻¹ := by simpa only [rightConjugate, inv_inv] using hh
    rw [rightConjugate_mul, mul_inv_cancel_right,
      rightConjugate_eq K (K.le_normalizer (K.inv_mem hk))] at hh
    exact hg hh
  exact le_iSup_of_le (⟨g*k, F.mul_mem g.property (hKF hk)⟩ : F)
    (le_iSup_of_le hescape le_rfl)

/-- Source (1.10): retaining only the conjugates escaping K still generates
F together with T. The generation and normality are relative to F. -/
theorem escapingConjugates_sup (Z F K T : Subgroup G)
    (hKF : K ≤ F) (hTF : T ≤ F)
    (hgen : conjugatesIn Z F ⊔ T = F) (hnot : ¬ conjugatesIn Z F ≤ K) :
    escapingConjugates Z F K ⊔ T = F := by
  classical
  let F₀ := conjugatesIn Z F
  let F₁ := escapingConjugates Z F K
  have h₀₁ : F₀ ≤ F₁ ⊔ K := by
    apply iSup_le
    intro g
    by_cases hg : rightConjugate Z g ≤ K
    · exact hg.trans le_sup_right
    · exact (conjugate_le_escaping Z F K g hg).trans le_sup_left
  have hn : F₀ ≤ normalizer F₁ := h₀₁.trans
    (sup_le F₁.le_normalizer (escapingConjugates_normalized Z F K hKF))
  have hex : ∃ g : F, ¬ rightConjugate Z g ≤ K := by
    by_contra h
    apply hnot
    exact iSup_le fun g => not_not.mp fun hg => h ⟨g,hg⟩
  obtain ⟨g,hg⟩ := hex
  have hg₁ : rightConjugate Z g ≤ F₁ := conjugate_le_escaping Z F K g hg
  have h₀ : F₀ ≤ F₁ ⊔ T := by
    apply iSup_le
    intro h
    have hgh : (g:G)⁻¹ * h ∈ F₀ ⊔ T := by
      rw [hgen]
      exact F.mul_mem (F.inv_mem g.property) h.property
    have hprod : (g:G)⁻¹ * h ∈ (F₀ : Set G) * (T : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left F₀ T
        (hTF.trans (conjugatesIn_normalized Z F))]
      exact hgh
    obtain ⟨f,hf,t,ht,heq⟩ := hprod
    have h_eq : (h:G) = g * f * t := by
      have hh := congrArg (fun x : G => g*x) heq
      simpa [mul_assoc] using hh.symm
    rw [h_eq, ← rightConjugate_mul, ← rightConjugate_mul]
    have hf₁ : rightConjugate (rightConjugate Z g) f ≤ F₁ :=
      (map_mono hg₁).trans (rightConjugate_eq F₁ (hn hf)).le
    exact (map_mono (hf₁.trans le_sup_left)).trans
      (rightConjugate_eq (F₁ ⊔ T) ((F₁ ⊔ T).le_normalizer (mem_sup_right ht))).le
  apply le_antisymm
  · exact sup_le ((escapingConjugates_le Z F K).trans
      ((show F₀ ≤ F₀ ⊔ T from le_sup_left).trans hgen.le)) hTF
  · exact hgen.ge.trans (sup_le h₀ le_sup_right)

/-- The same actor can escape the normalizers of two T-normal subgroups. -/
theorem simultaneous_escape (Z F T X₁ X₂ : Subgroup G)
    (hTF : T ≤ F) (hX₁ : X₁ ≤ T) (hX₂ : X₂ ≤ T)
    (hN₁ : (X₁.subgroupOf T).Normal) (hN₂ : (X₂.subgroupOf T).Normal)
    (hnot₁ : ¬ (X₁.subgroupOf F).Normal) (hnot₂ : ¬ (X₂.subgroupOf F).Normal)
    (hgen : conjugatesIn Z F ⊔ T = F) :
    ∃ g ∈ F, ¬ Z ≤ normalizer (rightConjugate X₁ g) ∧
      ¬ Z ≤ normalizer (rightConjugate X₂ g) := by
  have ht₁ := (normal_subgroupOf_iff_le_normalizer hX₁).mp hN₁
  have ht₂ := (normal_subgroupOf_iff_le_normalizer hX₂).mp hN₂
  let K := F ⊓ normalizer X₁
  have hnot : ¬ conjugatesIn Z F ≤ K := by
    intro h
    apply hnot₁
    apply (normal_subgroupOf_iff_le_normalizer (hX₁.trans hTF)).mpr
    exact hgen.ge.trans (sup_le (h.trans inf_le_right) ht₁)
  have hescape := escapingConjugates_sup Z F K T inf_le_left hTF hgen hnot
  have hex : ∃ g : F, ¬ rightConjugate Z g ≤ K ∧
      ¬ rightConjugate Z g ≤ normalizer X₂ := by
    classical
    by_contra h
    apply hnot₂
    apply (normal_subgroupOf_iff_le_normalizer (hX₂.trans hTF)).mpr
    apply hescape.ge.trans
    refine sup_le (iSup_le fun g => iSup_le fun hg => ?_) ht₂
    exact not_not.mp fun hn => h ⟨g,hg,hn⟩
  obtain ⟨g,hg₁,hg₂⟩ := hex
  have hZF : Z ≤ F := by
    have hZ : Z ≤ conjugatesIn Z F := by
      simpa only [OneMemClass.coe_one, rightConjugate_one] using
        conjugate_le_conjugatesIn Z F (1 : F)
    exact hZ.trans ((show conjugatesIn Z F ≤ conjugatesIn Z F ⊔ T from le_sup_left).trans hgen.le)
  have hn₁ : ¬ rightConjugate Z g ≤ normalizer X₁ := by
    intro h
    exact hg₁ (le_inf ((conjugate_le_conjugatesIn Z F g).trans (conjugatesIn_le Z F hZF)) h)
  have transport (X : Subgroup G) (hn : ¬ rightConjugate Z g ≤ normalizer X) :
      ¬ Z ≤ normalizer (rightConjugate X (g:G)⁻¹) := by
    intro h
    apply hn
    have hh := (map_mono (f := (MulAut.conj (g:G)⁻¹).toMonoidHom) h).trans
      ((rightConjugate X (g:G)⁻¹).le_normalizer_map (MulAut.conj (g:G)⁻¹).toMonoidHom)
    change rightConjugate Z g ≤ normalizer (rightConjugate (rightConjugate X (g:G)⁻¹) g) at hh
    simpa only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] using hh
  exact ⟨(g:G)⁻¹, F.inv_mem g.property, transport X₁ hn₁, transport X₂ hg₂⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
