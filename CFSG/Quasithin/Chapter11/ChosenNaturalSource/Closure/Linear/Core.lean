module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Setup
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.ThreeSubgroups

/-!
# Core containment from the two SL₃ generation identities

The kernel defining Y really centralizes K modulo O₂(K). Relative normality
puts O₂(K) and O₂(Y) inside O₂(G₁). The three-subgroups lemma transfers this
centralization to [S,L₁]; the opposite pair supplies the rest of S.
The second generation identity and 11.5.6(5) similarly handle K. Finally
S O₂(G₁) is a two-group normalized by K, Y and M₁, so lies in O₂(G₁).

The application uses the original three-conjugate core. Its two generation
identities and the Cartan action on the opposite pair remain explicit:
these are intermediate source obligations, not the conclusion of 11.5.7.
Source: Aschbacher--Smith, 11.5.7, printed pp.781--782.
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

omit [Finite G] in
private theorem normalizes_join_modulo (A B Q : Subgroup G)
    (hAQ : A ≤ normalizer (Q : Set G)) (hAB : ⁅A,B⁆ ≤ Q) :
    A ≤ normalizer ((B ⊔ Q : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha b hb
  let f := (MulAut.conj a).toMonoidHom
  have hB : B.map f ≤ B ⊔ Q := by
    rintro _ ⟨v, hv, rfl⟩
    have hc := hAB (commutator_mem_commutator ha hv)
    have he : f v = ⁅a,v⁆ * v := by
      simp [f, commutatorElement_def, mul_assoc]
    rw [he]
    exact (B ⊔ Q).mul_mem (mem_sup_right hc) (mem_sup_left hv)
  have hQ : Q.map f ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact le_normalizer_iff.mp hAQ a ha q hq
  have hm : (B ⊔ Q).map f ≤ B ⊔ Q := by
    rw [Subgroup.map_sup]
    exact sup_le hB (hQ.trans le_sup_right)
  exact hm (mem_map_of_mem f hb)

/-- Interpret the actual quotient-action kernel, retaining its representatives. -/
theorem commutator_Y_K_le : ⁅E.Y,E.K⁆ ≤ E.K.pCoreIn 2 := by
  apply commutator_le.mpr
  intro y hy k hk
  obtain ⟨a, ha, rfl⟩ := hy.2
  let b : E.K := ⟨k, hk⟩
  have he : QuotientGroup.mk' (pCore 2 E.K) (E.K.normalizerMonoidHom a b) =
      QuotientGroup.mk' (pCore 2 E.K) b := by
    rw [← coreQuotientAction_apply_mk]
    rw [MonoidHom.mem_ker.mp ha]
    rfl
  let c : E.K := E.K.normalizerMonoidHom a b * b⁻¹
  have hc : c ∈ pCore 2 E.K := by
    apply (QuotientGroup.eq_one_iff c).mp
    change QuotientGroup.mk' (pCore 2 E.K) c = 1
    simp only [c, map_mul, map_inv, he, mul_inv_cancel]
  exact ⟨c, hc, rfl⟩

theorem K_core_le_G₁_core : E.K.pCoreIn 2 ≤ E.G₁.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes E.K_le_G₁ E.G₁_normalizes_K

theorem Y_core_le_G₁_core : E.Y.pCoreIn 2 ≤ E.G₁.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes E.Y_le_G₁ (G₁_normalizes_Y E)

private theorem G₁_normalizes_core : E.G₁ ≤ normalizer (E.G₁.pCoreIn 2 : Set G) :=
  E.G₁.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E.G₁ (pCore 2 E.G₁))

/-- Normality is required only inside the literal point normalizer. -/
theorem le_core_of_centralizes_factors (S : Subgroup G)
    (hp : IsPGroup 2 S) (hSG : S ≤ E.G₁)
    (hSK : ⁅S,E.K⁆ ≤ E.G₁.pCoreIn 2)
    (hSY : ⁅S,E.Y⁆ ≤ E.G₁.pCoreIn 2)
    (hMS : E.M₁ ≤ normalizer (S : Set G))
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) : S ≤ E.G₁.pCoreIn 2 := by
  let Q := E.G₁.pCoreIn 2
  have hGQ : E.G₁ ≤ normalizer (Q : Set G) := G₁_normalizes_core E
  have hJp : IsPGroup 2 (S ⊔ Q : Subgroup G) :=
    hp.to_sup_of_normal_right' (isPGroup_pCoreIn 2 E.G₁) (hSG.trans hGQ)
  have hK : E.K ≤ normalizer ((S ⊔ Q : Subgroup G) : Set G) :=
    normalizes_join_modulo E.K S Q (E.K_le_G₁.trans hGQ)
      (by simpa only [commutator_comm E.K S] using hSK)
  have hY : E.Y ≤ normalizer ((S ⊔ Q : Subgroup G) : Set G) :=
    normalizes_join_modulo E.Y S Q (E.Y_le_G₁.trans hGQ)
      (by simpa only [commutator_comm E.Y S] using hSY)
  have hM : E.M₁ ≤ normalizer ((S ⊔ Q : Subgroup G) : Set G) :=
    (le_inf hMS (inf_le_right.trans hGQ)).trans
      (normalizer_inf_normalizer_le_normalizer_sup S Q)
  exact (show S ≤ S ⊔ Q from le_sup_left).trans
    (le_pCoreIn_of_normalizes hJp (sup_le hSG (pCoreIn_le 2 E.G₁))
      (hgen.trans (sup_le (sup_le hK hY) hM)))

/-- The two layer-generation calculations, together with 11.5.6, force
the literal three-conjugate core into O₂(G₁). -/
theorem threeCore_le_point_core {x y : G}
    (d : ChapterG.Section02.LinearThree.Hypothesis (setup E)
      E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hUQ : E.W ≤ E.G₁.pCoreIn 2)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hSL : threeCore E x y = ⁅threeCore E x y,E.L₁⁆ ⊔ oppositePair E x y)
    (hSX : threeCore E x y ≤ ⁅threeCore E x y,E.X⁆ ⊔
      (threeCore E x y ⊓ E.W))
    (hEY : ⁅oppositePair E x y,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hcoreX : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    threeCore E x y ≤ E.G₁.pCoreIn 2 := by
  let S := threeCore E x y
  let Q := E.G₁.pCoreIn 2
  have hSQ : S ≤ E.G₁ := threeCore_le_G₁ d hUT hf
  have hGQ : E.G₁ ≤ normalizer (Q : Set G) := G₁_normalizes_core E
  have hLQ : E.L₁ ≤ E.G₁ := pointResidual_le_G₁ E
  have hLY : ⁅E.L₁,E.Y⁆ ≤ Q := by
    rw [commutator_comm]
    exact ((commutator_mono le_rfl (pointResidual_le_K E)).trans
      (commutator_Y_K_le E)).trans (K_core_le_G₁_core E)
  have hSLY : ⁅⁅S,E.L₁⁆,E.Y⁆ ≤ Q := by
    apply commutator_commutator_le_of_rotate_of_le_normalizer
      (hSQ.trans hGQ) (hLQ.trans hGQ) (E.Y_le_G₁.trans hGQ)
    · exact (commutator_mono hLY le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hSQ.trans hGQ))
    · have hYS : ⁅E.Y,S⁆ ≤ E.Y :=
        le_normalizer_iff_commutator_le_left.mp (hSQ.trans (G₁_normalizes_Y E))
      exact (commutator_mono hYS le_rfl).trans (by rwa [commutator_comm])
  have hSY : ⁅S,E.Y⁆ ≤ Q := by
    have hpair : oppositePair E x y ≤ S := by
      exact (le_sup_right : oppositePair E x y ≤ ⁅S,E.L₁⁆ ⊔ oppositePair E x y).trans hSL.ge
    exact (commutator_mono hSL.le le_rfl).trans
      (commutator_sup_le_of_relative_normal E.G₁ ⁅S,E.L₁⁆
        (oppositePair E x y) E.Y Q hGQ
        ((commutator_le_sup S E.L₁).trans (sup_le hSQ hLQ))
        (hpair.trans hSQ) hSLY (hEY.trans (Y_core_le_G₁_core E)))
  have hKT : E.K ⊔ (T : Subgroup G) ≤ E.G₁ := sup_le E.K_le_G₁ hTG
  have hKTK : E.K ⊔ (T : Subgroup G) ≤ normalizer (E.K : Set G) :=
    hKT.trans E.G₁_normalizes_K
  have hKTcore : E.K ⊔ (T : Subgroup G) ≤
      normalizer ((E.K ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (E.K ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hKcore : ⁅(E.K ⊔ (T : Subgroup G)).pCoreIn 2,E.K⁆ ≤ Q := by
    apply le_trans _ ((inf_pCoreIn_le_of_le 2 (show E.K ≤ E.K ⊔ (T : Subgroup G)
      from le_sup_left)).trans (K_core_le_G₁_core E))
    exact le_inf
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 _).trans hKTK))
      (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hKTcore))
  have hSXK : ⁅⁅S,E.X⁆,E.K⁆ ≤ Q :=
    (commutator_mono ((commutator_mono (threeCore_le_LT_core d hUT hf) le_rfl).trans
      hcoreX) le_rfl).trans hKcore
  have hSUK : ⁅S ⊓ E.W,E.K⁆ ≤ Q :=
    (commutator_mono (inf_le_right.trans hUQ) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (E.K_le_G₁.trans hGQ))
  have hSK : ⁅S,E.K⁆ ≤ Q := (commutator_mono hSX le_rfl).trans
    (commutator_sup_le_of_relative_normal E.G₁ ⁅S,E.X⁆ (S ⊓ E.W) E.K Q hGQ
      ((commutator_le_sup S E.X).trans (sup_le hSQ hXG))
      (inf_le_left.trans hSQ) hSXK hSUK)
  exact le_core_of_centralizes_factors E S (isPGroup_pCoreIn 2 _) hSQ hSK hSY
    (M₁_normalizes_threeCore d hUT hf) hgen

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
