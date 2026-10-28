module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.PrimeExtensions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Embeddings
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionSigned

/-!
# The nonquasisimple point quotient in an odd ternary overcomponent

The full-Sylow-normalized local component in a signed odd ternary carrier
has an elementary-plane Fitting kernel and an SL₂(p) quotient. Its Fitting
kernel has odd order, so its two-core is trivial. Restriction to the actual
containing two-core quotient then transports this extension back to the
original point-component quotient; the special covering group is retained.

For the original chosen flag, the shared PSL₂ seed forces p = 5, and the
signed extension theorem excludes the unitary sign. This constructs the
literal elementary-linear ProperEmbedding row, with containing
quasisimplicity supplied by the full-catalogue comparison. The branch
assumes a nonquasisimple point quotient, not a nonquasisimple container.
The remaining quasisimple point branch and other proper pairs stay with
qt-d-1222-shadow-component-comparison. Earlier geometry and the common
seed marking retain final discharge by qt-d-1222-shadow-components.

Source: Aschbacher--Smith A.3.12(9--10), A.3.21, printed pp.47--48,55--56,
and the proper-overcomponent comparison of 11.4.2, printed p.776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels

private theorem elementary_fitting_twoCore {A : Type*} [Group A] [Finite A]
    {p : ℕ} (ho : Odd p) (hm : ElementaryModel p 2 (fittingSubgroup A)) : pCore 2 A = ⊥ := by
  have hf : Odd (Nat.card (fittingSubgroup A)) := by
    rw [Nat.card_congr hm.some.toEquiv]
    change Odd (Nat.card (Fin 2 → ZMod p))
    rw [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
    exact ho.pow
  rcases (pCore_isPGroup (p := 2) (G := A)).card_eq_or_dvd with he | hd
  · exact (eq_bot_iff_card _).mpr he
  · exact (hf.not_two_dvd_nat (hd.trans (card_dvd_of_le (pCore_le_fitting A 2)))).elim

private theorem elementary_sl_extension_transport
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) {p : ℕ}
    (h : HasExtension B (ElementaryModel p 2) (fun Q _ => IsSL Q 2 p)) :
    HasExtension A (ElementaryModel p 2) (fun Q _ => IsSL Q 2 p) := by
  obtain ⟨N,hN,⟨a⟩,F,_,_,hF,⟨b⟩⟩ := h
  let N' := N.map e.symm.toMonoidHom
  let f := e.symm.subgroupMap N
  let : N'.Normal := Subgroup.Normal.map hN e.symm.toMonoidHom e.symm.surjective
  exact ⟨N',inferInstance,⟨f.symm.trans a⟩,F,inferInstance,inferInstance,hF,
    ⟨(QuotientGroup.congr N N' e.symm rfl).symm.trans b⟩⟩

/-- The literal two-core quotient of a nonquasisimple local component in
an odd signed ternary carrier is an elementary-plane extension. -/
theorem odd_ternary_local_core_extension
    {A : Type*} [Group A] [Finite A]
    (hA : IsSQTK KnownSimple.IsKnownSimple A)
    (P : Sylow 2 A) (C : Subgroup A) (hC : C ∈ localCComponents P)
    (hPC : (P : Subgroup A) ≤ normalizer (C : Set A))
    (hn : ¬ IsQuasisimple (C ⧸ pCore 2 C))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign A u 3 p ∨ IsSLSign A u 3 p) :
    5 ≤ p ∧ u = false ∧ pCore 2 C = ⊥ ∧
      HasExtension (C ⧸ pCore 2 C) (ElementaryModel p 2) (fun Q _ => IsSL Q 2 p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hl,hu,hF,he⟩ := odd_three_local_signed_extension hA ho P hC hPC hn u hm
  have hz := elementary_fitting_twoCore ho hF
  have hb : 5 ≤ p := by
    have hodd := Nat.odd_iff.mp ho
    omega
  exact ⟨hb,hu,hz,elementary_sl_extension_transport
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot) he⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Restriction and the original two-core projection preserve the signed
ternary elementary-extension pair, including the special covering group. -/
theorem odd_ternary_quotient_extension
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {B J : Subgroup G} (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hBJ : B < J)
    (hn : ¬ IsQuasisimple (B ⧸ pCore 2 B))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    5 ≤ p ∧ u = false ∧
      HasExtension (B ⧸ pCore 2 B) (ElementaryModel p 2) (fun Q _ => IsSL Q 2 p) := by
  have hl := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup hG T hl
  have hs : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left))).mp
      (hsq.subgroup (J.subgroupOf (J ⊔ (T : Subgroup G))))
  have hq := ChapterE.Structure.sqtk_two_quotient hs (pCore 2 J) pCore_isPGroup
  obtain ⟨P,C,hC,_,hPC,⟨a⟩,_⟩ := proper_local_model_image hB hJ hTJ hTB hBJ
    (MulEquiv.refl (J ⧸ pCore 2 J))
  have hnC : ¬ IsQuasisimple (C ⧸ pCore 2 C) := fun hc =>
    hn (let := hc; IsQuasisimple.of_mulEquiv a.symm)
  obtain ⟨hb,hu,_,he⟩ := odd_ternary_local_core_extension hq P C hC hPC hnC hp ho u hm
  exact ⟨hb,hu,elementary_sl_extension_transport a he⟩

variable {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The actual chosen-flag application discharges containing
quasisimplicity and both normalization conditions. -/
theorem ofFlag_properEmbedding_of_nonquasisimple_odd_ternary
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign (J ⧸ pCore 2 J) u 3 p ∨ IsSLSign (J ⧸ pCore 2 J) u 3 p) :
    p = 5 ∧ u = false ∧
      HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
        (ElementaryModel 5 2) (fun Q _ => IsSL Q 2 5) ∧
      ProperEmbedding (ofFlag S f X z H).Kz J := by
  obtain ⟨hb,hu,he⟩ := odd_ternary_quotient_extension S.source.simpleQTKE h.point_mem_local_family
    hJ.1 (sylow_normalizes_overcomponent h hJ.1 hlt.le) (sylow_normalizes_point h)
    hlt hn hp ho u hm
  have hs : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) (J ⊔ (T : Subgroup G)) :=
    ⟨T.subtype le_sup_right,by
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]⟩
  have hp5 := (LocalGeometry.Components.Embedding.relative_odd_ternary_parameters hP
    (LocalGeometry.Components.flag_mem_local_of_model D S f 0 hs)
    (show Source.ComponentIn (J ⊔ (T : Subgroup G)) J from ⟨le_sup_left,hJ.1.1⟩)
    ((le_conjugateSpanBy _ _).trans hlt.le) (f.sylow_normalizes_Li 0)
    S.nonbinary hs hp ho u hm).2
  subst p
  subst u
  exact ⟨rfl,rfl,he,.quasisimple (.elementaryLinear 5 hp hb he hm)
    (ofFlag_proper_overcomponent_quasisimple S f X z H h hne hlinear h1132 e hcent hJ hlt)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
