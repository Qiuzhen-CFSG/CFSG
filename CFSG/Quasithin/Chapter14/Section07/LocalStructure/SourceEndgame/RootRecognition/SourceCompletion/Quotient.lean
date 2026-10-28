module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion

/-!
# The literal six-dimensional root quotient and its fixed space

Construct the K/P action on the actual elementary quotient P/U and descend
the already recognized natural P/E coordinates. The kernel E/U is fixed,
and the proved group commutator generation makes this natural projection
a cover. Its kernel has order four; hence the original quotient has binary
dimension six and is the indecomposable universal natural cover. Both the
quotient formula and natural projection are retained.

The final two applications consume the actual72 record, construct all73
data, and feed RuTwo once the later74 core identity is supplied. Universal
G.1.3 remains the named earlier-source dependency qt-g-01.
Source: Aschbacher–Smith 14.7.73(3) and75, printed pp.1076–1078.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

section Coordinates
variable [(F.U.subgroupOf ((K F).pCoreIn 2)).Normal]
  [IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2))]

abbrev QuotientSpace := Additive ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2))

structure QuotientCoordinates (k : K F) where
  action : Representation (ZMod 2) SL2FourNatural.SL (QuotientSpace (F := F))
  conjugation : BinaryConjugationSection (K F) ((K F).pCoreIn 2) F.U (action.comp (qK d))
  quotient_formula : ∀ x : (K F).pCoreIn 2, (conjugation.coordinates x).toAdd =
    Additive.ofMul (QuotientGroup.mk' (F.U.subgroupOf ((K F).pCoreIn 2)) x)
  dimension : Module.finrank (ZMod 2) (QuotientSpace (F := F)) = 6
  indecomposable : ∀ A B : Submodule (ZMod 2) (QuotientSpace (F := F)),
    (∀ g v, v ∈ A → action g v ∈ A) →
    (∀ g v, v ∈ B → action g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥
  invariants : action.invariants = conjugation.imageSpace (E L F k)
  fixed_card : Nat.card action.invariants = 4
  projection : ∃ p : action.IntertwiningMap SL2FourNatural.naturalRepresentation,
    IsCover p ∧ p.toLinearMap.ker = conjugation.imageSpace (E L F k) ∧
      ∃ e : SL2FourCentralCover.binaryAction.Equiv action,
        ∀ w, p (e w) = SL2FourCentralCover.projection w
end Coordinates

theorem quotient_coordinates (k : K F) (h : Conclusion73 d k)
    (hd : ⁅S L F,S L F⁆ ≤ F.U) :
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    letI := h.elementary
    Nonempty (QuotientCoordinates d k) := by
  let : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
  let := h.elementary
  obtain ⟨n⟩ := h.natural
  have hNU := (K_le_H F).trans d.conjugationSection.normalized
  have hNP : K F ≤ normalizer ((K F).pCoreIn 2) :=
    (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)
  obtain ⟨σ,c,hc⟩ := BinaryConjugationSection.exists_canonical (K F) ((K F).pCoreIn 2) F.U
    (pCoreIn_le 2 _) ((U_le_E d k).trans n.kernel_le) hNP hNU
    (qK d) (qK_surjective d) (qK_ker d)
  obtain ⟨p,hp,hpn,hpk⟩ := BinaryConjugationSection.exists_projection
    (K F) (K F) ((K F).pCoreIn 2) F.U (E L F k) le_rfl (U_le_E d k)
    (qK d) (qK d) (qK_surjective d) (MonoidHom.id _) (fun _ => rfl)
    σ SL2FourNatural.naturalRepresentation c n
  change σ.IntertwiningMap SL2FourNatural.naturalRepresentation at p
  have hEC : ⁅K F,E L F k⁆ ≤ F.U := by
    rw [commutator_comm]
    exact E_commutator_le_U d k h.generation hd
  have hfix : p.toLinearMap.ker ≤ fixed σ := by
    intro w hw g
    obtain ⟨x,rfl⟩ := qK_surjective d g
    have hwe : w ∈ c.imageSpace (E L F k) := hpk ▸ hw
    exact c.fixed_on_imageSpace_of_commutator_le (K F) (E L F k) hEC x x.property w hwe
  have hgen : Coinvariants.ker σ = ⊤ :=
    c.coinvariants_eq_top_of_group_generation (K F) le_rfl σ (qK d) (fun _ _ => rfl)
      (by rw [commutator_comm]; exact h.commutator_generation)
  have hcover : IsCover p := ⟨hp,hfix,hgen⟩
  have hcard : Nat.card p.toLinearMap.ker = 4 := by
    rw [hpk]
    change Nat.card (((E L F k).subgroupOf ((K F).pCoreIn 2)).map c.coordinates) = 4
    rw [← relIndex_ker, c.kernel_eq, relIndex_subgroupOf n.kernel_le]
    exact h.kernel_index
  have hdimk : Module.finrank (ZMod 2) p.toLinearMap.ker = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := p.toLinearMap.ker)
    rw [Nat.card_zmod,hcard] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm
  have hdim : Module.finrank (ZMod 2) (QuotientSpace (F := F)) = 6 := by
    have he := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp,finrank_top,SL2FourNatural.finrank_vector,hdimk] at he
    exact he.symm
  have hinv := SL2FourCentralCover.invariants_eq_kernel p hfix
  obtain ⟨eqv,heqv⟩ := SL2FourCentralCover.exists_equiv_of_six_dimensional_cover p hcover hdim
  exact ⟨{
    action := σ
    conjugation := c
    quotient_formula := hc
    dimension := hdim
    indecomposable := SL2FourCentralCover.indecomposable_of_natural_cover p hcover
    invariants := hinv.trans hpk
    fixed_card := by rw [hinv]; exact hcard
    projection := ⟨p,hcover,hpk,eqv,heqv⟩ }⟩

open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation

/-- All root conclusions, together with the actual six-dimensional
indecomposable quotient, constructed from the original72 record. -/
theorem finish_roots_with_quotient
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d)
    (recognition : Geometry.NaturalRecognition.{u}) (k : K F)
    (hk : (k : G) ∉ F.Li L 1 ⊔ (T : Subgroup G)) :
    ∃ h : Conclusion73 d k,
      letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
        normal_subgroupOf_of_le_normalizer
          ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
      letI := h.elementary
      Nonempty (QuotientCoordinates d k) := by
  let h := finish_roots d structural c e mark hcomm h72 recognition k hk
  exact ⟨h,quotient_coordinates d k h (h72.derived_eq.le.trans (Data.V_le_U F))⟩

/-- Feed the literal RuTwo consumer after74, constructing the conjugator
and all natural-section, generation, Sylow and cardinality data here. -/
theorem ruTwo_of_source72
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c) (mark : UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h72 : SourceAssembly.Conclusion72 d) (recognition : Geometry.NaturalRecognition.{u})
    (hz : ChapterJ.sylowCenter T = F.Vi 1)
    (hcore : F.H.pCoreIn 2 = (K F).pCoreIn 2) : Nonempty (ChapterJ.RuTwo V T) := by
  obtain ⟨k,hk,h⟩ := exists_roots d structural c e mark hcomm h72 recognition
  exact ruTwo_of_roots d k h h72.core h72.frattini_eq
    (d.natural.sylow_normalizes structural) h72.fixed_kernel hz hcore

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
