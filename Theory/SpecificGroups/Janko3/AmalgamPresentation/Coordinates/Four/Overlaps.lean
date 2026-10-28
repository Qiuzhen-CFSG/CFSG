module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Orientation
public import Theory.SpecificGroups.Janko3.SourceRecognition.BaumeisterParabolics.Point
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The literal second-local overlap subgroups

The original order-480 words generate precisely the existing Singer affine
embedding. The original order-180 words generate precisely the pure linear
complement. All generation witnesses are short words in the original two
overlap elements, and every coordinate identity is kernel checked.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates
open Subgroup Subgroup.CosetWordCertificate Matrix
open Representation.SL2FourNatural hiding Plane
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition

private def fieldElement : Fin 4 → F
  | 0 => 0
  | 1 => 1
  | 2 => ⟨0,1⟩
  | _ => ⟨1,1⟩
private theorem fieldElement_surjective : Function.Surjective fieldElement := by decide +kernel
private def vectorElement (i : Fin 16) : Plane :=
  Multiplicative.ofAdd ![fieldElement ⟨i.val / 4,by omega⟩,
    fieldElement ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩]
private theorem vectorElement_surjective : Function.Surjective vectorElement := by decide +kernel

private theorem word_mem {G : Type*} [Group G] (a b : G) (w : Word Bool) :
    eval (fun t : Bool => if t then b else a) w ∈ closure ({a,b} : Set G) := by
  have hg (t : Bool) : (if t then b else a) ∈ closure ({a,b} : Set G) := by
    cases t <;> apply Subgroup.subset_closure <;> simp
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [eval_cons]
    apply Subgroup.mul_mem _ _ ih
    split
    · exact hg x.1
    · exact Subgroup.inv_mem _ (hg x.1)

private theorem computation_ext {x y : Affine}
    (hv : ∀ i, x.left.toAdd i = y.left.toAdd i)
    (hm : ∀ i j, x.right.val i j = y.right.val i j) : x = y := by
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd (funext hv)
  · exact Units.ext (funext fun i => funext (hm i))

private def singerGen (b : Bool) : Affine := if b then singerSecond else singerFirst
private def linearGen (b : Bool) : Affine := if b then linearSecond else linearFirst

private def singertranslationsWord : Fin 16 → Word Bool
  | 0 => []
  | 1 => [(false, true), (true, false), (false, true), (true, true)]
  | 2 => [(false, false), (true, true), (false, false), (true, false)]
  | 3 => [(true, true), (false, false), (true, true), (false, false), (true, false), (true, false)]
  | 4 => [(false, true), (true, true), (true, true), (false, false), (true, false), (true, false)]
  | 5 => [(false, true), (true, true), (false, true), (false, true), (true, false), (false, true)]
  | 6 => [(false, false), (false, false), (true, true), (false, false), (false, false), (true, false)]
  | 7 => [(false, true), (true, true), (false, true), (true, false)]
  | 8 => [(false, true), (true, false), (true, false), (false, false), (true, true), (true, true)]
  | 9 => [(false, false), (false, false), (true, false), (false, false), (false, false), (true, true)]
  | 10 => [(false, false), (true, true), (true, true), (false, true), (true, false), (true, false)]
  | 11 => [(false, true), (false, true), (true, true), (false, true), (true, false), (false, false)]
  | 12 => [(false, false), (true, false), (false, false), (true, true)]
  | 13 => [(false, true), (true, false), (false, true), (false, true), (true, true), (false, true)]
  | 14 => [(false, true), (false, true), (true, false), (false, true), (true, true), (false, false)]
  | _ => [(false, true), (false, true), (true, false), (false, true), (false, true), (true, true)]

private def linearupperWord : Fin 4 → Word Bool
  | 0 => []
  | 1 => [(true, false), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true)]
  | 2 => [(true, true), (false, true), (true, false)]
  | _ => [(false, true), (true, true), (true, true), (false, true), (true, false), (true, false), (false, true)]

private def linearlowerWord : Fin 4 → Word Bool
  | 0 => []
  | 1 => [(true, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, false), (true, false)]
  | 2 => [(false, true)]
  | _ => [(true, true), (false, true), (true, false), (true, false), (false, true), (true, true), (true, true), (false, true), (true, false)]

private def linearscalarWord : Fin 3 → Word Bool
  | 0 => []
  | 1 => [(true, true), (true, true), (true, true), (true, true), (true, true)]
  | _ => [(true, false), (true, false), (true, false), (true, false), (true, false)]

private def singerAlphaWord : Word Bool := [(false, false), (true, true), (true, true), (false, true), (false, true)]
private def singerFrobeniusWord : Word Bool := [(false, false), (true, true), (true, true), (true, true), (false, true)]

private def alphaMatrix : LinearGroup :=
  ⟨!![0,⟨0,1⟩;1,1],!![⟨1,1⟩,1;⟨1,1⟩,0],by decide +kernel,by decide +kernel⟩
private def frobeniusMatrix : LinearGroup :=
  ⟨!![1,1;0,1],!![1,1;0,1],by decide +kernel,by decide +kernel⟩

private theorem translations_cert (i : Fin 16) : eval singerGen (singertranslationsWord i) =
    SemidirectProduct.inl (vectorElement i) := by
  apply computation_ext
  · intro j; fin_cases j <;> revert i <;> decide +kernel
  · intro j k; fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private theorem alpha_cert : eval singerGen singerAlphaWord = SemidirectProduct.inr alphaMatrix := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

private theorem frobenius_cert : eval singerGen singerFrobeniusWord = SemidirectProduct.inr frobeniusMatrix := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

private theorem singer_root_mem (v : Plane) : (SemidirectProduct.inl v : Affine) ∈ singerWords := by
  obtain ⟨i,rfl⟩ := vectorElement_surjective v
  rw [←translations_cert]
  exact word_mem _ _ _

private theorem embedding_alpha : SingerField.affineEmbedding
    (SingerField.scalar BaumeisterParabolics.alpha) = SemidirectProduct.inr alphaMatrix := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

private theorem embedding_frobenius : SingerField.affineEmbedding SingerField.fieldElement =
    SemidirectProduct.inr frobeniusMatrix := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

private theorem alpha_generates : zpowers BaumeisterParabolics.alpha = ⊤ := by
  have ho : orderOf BaumeisterParabolics.alpha = 15 := by
    apply (orderOf_eq_iff (by decide : 0 < 15)).mpr
    refine ⟨by decide +kernel,?_⟩
    intro m hm hp
    interval_cases m <;> decide +kernel
  apply eq_top_of_card_eq
  rw [Nat.card_zpowers,ho,Nat.card_units,Nat.card_eq_fintype_card,SingerField.field_card]

private theorem singerFirst_mem : singerFirst ∈ SingerField.affineEmbedding.range := by
  refine ⟨SingerField.root (Multiplicative.ofAdd (⟨⟨0,1⟩,0⟩ : SingerField.K)) *
    SingerField.scalar (BaumeisterParabolics.alpha ^ 6),?_⟩
  rw [map_mul,SingerField.affineEmbedding_root,map_pow,map_pow,embedding_alpha]
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

private theorem singerSecond_mem : singerSecond ∈ SingerField.affineEmbedding.range := by
  refine ⟨SingerField.root (Multiplicative.ofAdd (⟨1,1⟩ : SingerField.K)) *
    SingerField.scalar (BaumeisterParabolics.alpha ^ 2) * SingerField.fieldElement,?_⟩
  rw [map_mul,map_mul,SingerField.affineEmbedding_root,map_pow,map_pow,
    embedding_alpha,embedding_frobenius]
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

/-- The exact order-480 word subgroup is the existing Singer affine embedding. -/
theorem singerWords_eq : singerWords = SingerField.affineEmbedding.range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact singerFirst_mem
    · exact singerSecond_mem
  · rintro _ ⟨x,rfl⟩
    have halpha : SingerField.affineEmbedding (SingerField.scalar BaumeisterParabolics.alpha) ∈
        singerWords := by
      rw [embedding_alpha,←alpha_cert]
      exact word_mem _ _ _
    have hfrob : SingerField.affineEmbedding SingerField.fieldElement ∈ singerWords := by
      rw [embedding_frobenius,←frobenius_cert]
      exact word_mem _ _ _
    have hs (u : SingerField.Kˣ) : SingerField.affineEmbedding (SingerField.scalar u) ∈ singerWords := by
      have hu : u ∈ zpowers BaumeisterParabolics.alpha := alpha_generates.symm ▸ mem_top u
      obtain ⟨k,rfl⟩ := hu
      rw [map_zpow,map_zpow]
      exact singerWords.zpow_mem halpha _
    let ψ : (SingerField.K ≃ₗ[F] SingerField.K) →* Affine :=
      (SemidirectProduct.inr : LinearGroup →* Affine).comp SingerField.matrixEquiv.toMonoidHom
    have hnormalizer : SingerField.normalizer ≤ singerWords.comap ψ := by
      apply sup_le
      · rintro _ ⟨u,rfl⟩
        have he : SingerField.affineEmbedding (SingerField.scalar u) =
            ψ (SingerField.multiplication u) :=
          SemidirectProduct.map_inr _ _ _ _
        change ψ (SingerField.multiplication u) ∈ singerWords
        rw [←he]
        exact hs u
      · apply zpowers_le.mpr
        have he : SingerField.affineEmbedding SingerField.fieldElement =
            ψ SingerField.frobenius := SemidirectProduct.map_inr _ _ _ _
        change ψ SingerField.frobenius ∈ singerWords
        rw [←he]
        exact hfrob
    have hn (n : SingerField.normalizer) : SingerField.affineEmbedding
        (SemidirectProduct.inr n) ∈ singerWords := by
      have he : SingerField.affineEmbedding (SemidirectProduct.inr n) = ψ n.val :=
        SemidirectProduct.map_inr _ _ _ _
      rw [he]
      exact hnormalizer n.property
    have hx : x = SingerField.root x.left * SemidirectProduct.inr x.right :=
      (SemidirectProduct.inl_left_mul_inr_right x).symm
    rw [hx,map_mul,SingerField.affineEmbedding_root]
    exact singerWords.mul_mem (singer_root_mem _) (hn _)

private theorem upper_cert (i : Fin 4) : eval linearGen (linearupperWord i) =
    SemidirectProduct.inr (SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (fieldElement i))) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext j
    fin_cases j <;> revert i <;> decide +kernel
  · apply Units.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private theorem lower_cert (i : Fin 4) : eval linearGen (linearlowerWord i) =
    SemidirectProduct.inr (SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (fieldElement i))) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext j
    fin_cases j <;> revert i <;> decide +kernel
  · apply Units.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private def scalarElement (i : Fin 3) : Fˣ :=
  match i with
  | 0 => 1
  | 1 => ⟨⟨0,1⟩,⟨1,1⟩,by decide +kernel,by decide +kernel⟩
  | _ => ⟨⟨1,1⟩,⟨0,1⟩,by decide +kernel,by decide +kernel⟩
private theorem scalarElement_surjective : Function.Surjective scalarElement := by decide +kernel

private theorem scalar_cert (i : Fin 3) : eval linearGen (linearscalarWord i) =
    SemidirectProduct.inr (GeneralLinearGroup.scalar (Fin 2) (scalarElement i)) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext j
    fin_cases j <;> revert i <;> decide +kernel
  · apply Units.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

/-- The exact order-180 word subgroup is the literal pure linear complement. -/
theorem linearWords_eq : linearWords =
    (SemidirectProduct.inr : LinearGroup →* Affine).range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨linearFirst.right,SemidirectProduct.ext (by decide +kernel) rfl⟩
    · exact ⟨linearSecond.right,SemidirectProduct.ext (by decide +kernel) rfl⟩
  · rintro _ ⟨x,rfl⟩
    have hs (g : SL) : (SemidirectProduct.inr (SpecialLinearGroup.toGL g) : Affine) ∈ linearWords := by
      refine SL2.transvection_induction
        (fun g => (SemidirectProduct.inr (SpecialLinearGroup.toGL g) : Affine) ∈ linearWords) ?_ ?_ g
      · intro i j hij c
        obtain ⟨k,rfl⟩ := fieldElement_surjective c
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · rw [←upper_cert]; exact word_mem _ _ _
        · rw [←lower_cert]; exact word_mem _ _ _
        · exact (hij rfl).elim
      · intro a b ha hb
        rw [map_mul,map_mul]
        exact linearWords.mul_mem ha hb
    have hc (u : Fˣ) : (SemidirectProduct.inr (GeneralLinearGroup.scalar (Fin 2) u) : Affine) ∈ linearWords := by
      obtain ⟨i,rfl⟩ := scalarElement_surjective u
      rw [←scalar_cert]
      exact word_mem _ _ _
    obtain ⟨⟨u,g⟩,he⟩ := SemilinearNormalizer.scalarSpecialEquiv.surjective x
    rw [SemilinearNormalizer.scalarSpecialEquiv_apply] at he
    rw [←he,map_mul]
    exact linearWords.mul_mem (hc _) (hs _)

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates
