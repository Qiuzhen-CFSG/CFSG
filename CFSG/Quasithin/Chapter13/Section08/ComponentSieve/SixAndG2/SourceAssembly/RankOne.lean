module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import CFSG.Quasithin.ChapterG.Section06.Chapter13Bridge
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.G64Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.SixExtension

/-!
# Full G.6.4 at the Chapter 13 recognition boundary

Transport the proved source classification to the Chapter 13 interface.
Both internal factors retain their relative normality, literal displacement
spaces, mutual centralizers, and involution exchanging the factors.
The central-Sylow alternatives use the same actor and module equivalences.
This supplies the appendix input of the rank-one A₆ recognition branch;
no source classification conclusion is assumed.
Source: Aschbacher–Smith, G.6.4, and the use in 13.8.5–26.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.RecognitionStep
namespace RankOneSource
open ChapterG.Section06
universe u
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

private theorem factor_transfer (ρ : Representation (ZMod 2) A E) (K : Subgroup A)
    (W : Submodule (ZMod 2) E) (h : FactorModel ρ K W) :
    G64FactorAlternativeAt ρ K W := by
  rcases h with ⟨n, hn, hb, e, f, hs, he⟩ | ⟨n, hn, hb, e, f, hs, he⟩ | ⟨n, hn, e, f, hs, he⟩
  · exact ⟨hs, Or.inl ⟨n, hn, hb, e, f, he⟩⟩
  · exact ⟨hs, Or.inr (Or.inl ⟨n, hn, hb, e, f, he⟩)⟩
  · exact ⟨hs, Or.inr (Or.inr ⟨n, hn, e, f, he⟩)⟩

private theorem small_transfer (ρ : Representation (ZMod 2) A E) (K : Subgroup A)
    (W : Submodule (ZMod 2) E) (h : SmallFactorModel ρ K W) :
    G64FactorAlternativeAt ρ K W ∧ G64SmallFactor K := by
  rcases h with ⟨e, f, hs, he⟩ | ⟨e, f, hs, he⟩ | ⟨e, f, hs, he⟩
  · exact ⟨⟨hs, Or.inl ⟨2, by decide, by decide, e, f, he⟩⟩, Or.inl ⟨e⟩⟩
  · exact ⟨⟨hs, Or.inl ⟨3, by decide, by decide, e, f, he⟩⟩, Or.inr (Or.inl ⟨e⟩)⟩
  · exact ⟨⟨hs, Or.inr (Or.inl ⟨5, by decide, by decide, e, f, he⟩)⟩,
      Or.inr (Or.inr ⟨e⟩)⟩

private theorem whole_transfer {B F : Type*} [Group B] [AddCommGroup F] [Module (ZMod 2) F]
    (ρ : Representation (ZMod 2) A E) (σ : Representation (ZMod 2) B F)
    (h : HasModelOn ρ ⊤ ⊤ σ) : HasActionModel ρ σ := by
  obtain ⟨e, f, hs, he⟩ := h
  let e' := (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).symm.trans e
  let f' := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) E) ≃ₗ[ZMod 2] E).symm.trans f
  exact ⟨e', f', fun a v => he ⟨a, mem_top _⟩ ⟨v, by trivial⟩⟩

private theorem central_transfer (ρ : Representation (ZMod 2) A E)
    (h : CentralModel ρ) : G64CentralAlternative ρ := by
  rcases h with ⟨n, hn, hb, hm⟩ | hm | hm | hm
  · exact Or.inl ⟨n, hn, hb, whole_transfer ρ _ hm⟩
  · exact Or.inr (Or.inl (whole_transfer ρ _ hm))
  · exact Or.inr (Or.inr (Or.inl (whole_transfer ρ _ hm)))
  · exact Or.inr (Or.inr (Or.inr (whole_transfer ρ _ hm)))

private theorem two_transfer (ρ : Representation (ZMod 2) A E) (a : A)
    (d : TwoFactors ρ a) : Nonempty (G64SourceTwo ρ a) := by
  have hfirst := small_transfer ρ _ _ d.first_model
  have hsecond := small_transfer ρ _ _ d.second_model
  have hn1 : normalClosure ({a} : Set A) ≤ normalizer (d.first : Set A) := by
    rw [← d.join_eq]
    refine sup_le d.first.le_normalizer ?_
    exact (commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm d.second d.first).trans d.commute)).trans (Subgroup.centralizer_le_normalizer _)
  have hn2 : normalClosure ({a} : Set A) ≤ normalizer (d.second : Set A) := by
    rw [← d.join_eq]
    exact sup_le ((commutator_eq_bot_iff_le_centralizer.mp d.commute).trans
      (Subgroup.centralizer_le_normalizer _)) d.second.le_normalizer
  refine ⟨{
    K1 := d.first
    K2 := d.second
    K1_le := le_sup_left.trans_eq d.join_eq
    K2_le := le_sup_right.trans_eq d.join_eq
    direct_product := d.join_eq
    trivial_intersection := d.disjoint
    commuting_factors := d.commute
    K1_normal_in_closure := fun x hx g hg => le_normalizer_iff.mp hn1 g hg x hx
    K2_normal_in_closure := fun x hx g hg => le_normalizer_iff.mp hn2 g hg x hx
    transvection_in_first := d.marked
    second_nontrivial := d.second_nontrivial
    factor_one_model := ⟨_, hfirst.1⟩
    factor_two_model := ⟨_, hsecond.1⟩
    factor_one_small := hfirst.2
    factor_two_small := hsecond.2
    extension := ?_
    module_sum := d.space_sum
    first_module := hfirst.1
    second_module := hsecond.1
    first_centralizes_second := d.cross_first
    second_centralizes_first := d.cross_second
    permutes_factors := d.permutation }⟩
  obtain ⟨t, _, ht, hj, he⟩ := d.extension
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using ht)
  refine ⟨t, ht, hj, ?_, ?_⟩
  · intro x hx
    exact he ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hx
  · intro x hx
    have hx' : x ∈ d.first.map (MulAut.conj t).toMonoidHom := he.symm ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    change t * (t * y * t⁻¹) * t⁻¹ ∈ d.first
    rw [htinv]
    have htt : t * t = 1 := by simpa [pow_two] using ht
    have heq : t * (t * y * t) * t = y := by
      calc
        t * (t * y * t) * t = (t * t) * y * (t * t) := by simp only [mul_assoc]
        _ = y := by rw [htt, one_mul, mul_one]
    rwa [heq]

/-- The proved four-clause G.6.4 theorem supplies the exact Chapter 13
interface, preserving both internal factors, module spaces and the exchanger. -/
theorem source_theorem : G64SourceTheorem.{u} KnownSimple.IsKnownSimple := by
  intro A E Cover _ _ _ _ _ _ _ ρ a q hcover hq hcore hf ha ha1 hr hgen ht
  let h : Hypotheses KnownSimple.IsKnownSimple ρ a q := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := hcover
    quotient_surjective := hq
    twoCore := hcore
    faithful := hf
    involution := ha
    nonidentity := ha1
    displacement_rank := hr
    generated := (chapter13_displacementOrbit_eq ρ a).symm.trans hgen }
  obtain ⟨hc, hz⟩ := lemma_G_6_4 h (transvection_displacement_rank ht)
  refine ⟨?_, fun S hs => ⟨(hz S hs).1, central_transfer ρ (hz S hs).2⟩⟩
  rcases hc with hc | hd
  · obtain ⟨hk, hm, hw⟩ := hc
    refine Or.inl ⟨{
      K := ⊤
      W := subspaceCommutator ρ ⊤ ⊤
      K_eq := hk.symm
      W_eq := hw
      model := factor_transfer ρ _ _ hm
      whole_actor := rfl
      commutator_module := rfl }⟩
  · obtain ⟨d⟩ := hd
    exact Or.inr (two_transfer ρ a d)

end RankOneSource
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
