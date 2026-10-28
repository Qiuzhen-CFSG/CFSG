module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.OrbitTransport
public import Theory.Representation.SylowNormalizerIntertwiner

/-!
# Changing the coordinates of a marked natural constituent

Sylow conjugacy aligns an independently supplied constituent identification
with the source overlap. The same group element acts on the linear coordinates.
A geometric comparison of the two parabolic classes transports the actual
T-induced diagram action to the resulting marking, retaining its inducing
element. This is the interface needed by `Single.orbitPairIdentification`.

Source: Aschbacher–Smith, E.2.2(2)(b), printed pp.215–216, and the natural
and diagram pair in 15.3.65, printed p.1152. Module recognition and existence
of the source diagram action remain inputs to this transport result.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
variable {D E E' V X : Type*} [Group D] [Group E] [Group E']
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

private theorem map_trans (R : Subgroup E) (e : E ≃* E') (a : MulAut E') :
    R.map (e.trans a).toMonoidHom = (R.map e.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]; rfl

private theorem map_congr (R : Subgroup E) (e : E ≃* E') (a : MulAut E) :
    (R.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom =
      (R.map a.toMonoidHom).map e.toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr]

private def Conjugate (P Q : Subgroup E) : Prop :=
  ∃ x : E, P = Q.map (MulAut.conj x).toMonoidHom

private theorem conjugate_symm {P Q : Subgroup E} (h : Conjugate P Q) : Conjugate Q P := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨x⁻¹, ?_⟩
  rw [Subgroup.map_map]
  have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
      MonoidHom.id E := by ext y; simp [mul_assoc]
  change Q = Q.map ((MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom)
  rw [he, Subgroup.map_id]

private theorem conjugate_trans {P Q R : Subgroup E}
    (h : Conjugate P Q) (k : Conjugate Q R) : Conjugate P R := by
  obtain ⟨x, rfl⟩ := h
  obtain ⟨y, rfl⟩ := k
  refine ⟨x * y, ?_⟩
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

private theorem conjugate_map {P Q : Subgroup E} (h : Conjugate P Q) (e : E ≃* E') :
    Conjugate (P.map e.toMonoidHom) (Q.map e.toMonoidHom) := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨e x, ?_⟩
  simp only [Subgroup.map_map]
  congr 1
  ext z
  simp

/-- A change of group coordinates preserving the two parabolic classes as a
pair preserves genuine movement of that pair. It may interchange the types. -/
theorem movesParabolicClasses_transport (e : E ≃* E') (a : MulAut E)
    (P Q : Subgroup E) (P' Q' : Subgroup E')
    (hclasses : ∀ R : Subgroup E, R = P ∨ R = Q →
      ∃ S : Subgroup E', (S = P' ∨ S = Q') ∧
        ∃ x : E', R.map e.toMonoidHom = S.map (MulAut.conj x).toMonoidHom)
    (ha : MovesParabolicClasses a P Q) :
    MovesParabolicClasses (MulAut.congr e a) P' Q' := by
  intro hfix
  have step (R : Subgroup E) (hR : R = P ∨ R = Q) :
      Conjugate (R.map a.toMonoidHom) R := by
    obtain ⟨S, hS, hc⟩ := hclasses R hR
    have hs : Conjugate (S.map (MulAut.congr e a).toMonoidHom) S := by
      rcases hS with rfl | rfl
      · exact hfix.1
      · exact hfix.2
    have hm := conjugate_trans (conjugate_map hc (MulAut.congr e a))
      (conjugate_trans hs (conjugate_symm hc))
    rw [map_congr] at hm
    have hp := conjugate_map hm e.symm
    have cancel (S : Subgroup E) : (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
      rw [Subgroup.map_map]
      have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id E := by
        ext x; exact e.symm_apply_apply x
      rw [he, Subgroup.map_id]
    simpa only [cancel] using hp
  exact ha ⟨step P (Or.inl rfl), step Q (Or.inr rfl)⟩

/-- Transport the same inducing element of T, its Borel, and its genuine
parabolic movement through compatible group coordinates. -/
def transportDiagram {K T : Subgroup D} {φ : K ≃* E}
    {B P Q : Subgroup E} (d : InducedDiagramAction K T φ B P Q)
    (e : E ≃* E') (B' P' Q' : Subgroup E')
    (hB : B.map e.toMonoidHom = B')
    (hclasses : ∀ R : Subgroup E, R = P ∨ R = Q →
      ∃ S : Subgroup E', (S = P' ∨ S = Q') ∧
        ∃ x : E', R.map e.toMonoidHom = S.map (MulAut.conj x).toMonoidHom) :
    InducedDiagramAction K T (φ.trans e) B' P' Q' where
  element := d.element
  mem_T := d.mem_T
  normalizes := d.normalizes
  automorphism := MulAut.congr e d.automorphism
  induced := by
    rw [d.induced]
    ext x
    rfl
  borel := by rw [← hB, map_congr, d.borel]
  moves := movesParabolicClasses_transport e _ P Q P' Q' hclasses d.moves

@[simp] theorem transportDiagram_element {K T : Subgroup D} {φ : K ≃* E}
    {B P Q : Subgroup E} (d : InducedDiagramAction K T φ B P Q)
    (e : E ≃* E') (B' P' Q' : Subgroup E') (hB : B.map e.toMonoidHom = B')
    (hclasses : ∀ R : Subgroup E, R = P ∨ R = Q →
      ∃ S : Subgroup E', (S = P' ∨ S = Q') ∧
        ∃ x : E', R.map e.toMonoidHom = S.map (MulAut.conj x).toMonoidHom) :
    (transportDiagram d e B' P' Q' hB hclasses).element = d.element := rfl

/-- The comparison of two markings of the same overlap preserves the Borel. -/
theorem comparison_borel (s : D ≃* E) (e : D ≃* E')
    (B : Subgroup D) (B₀ : Subgroup E) (B₁ : Subgroup E')
    (hs : B.map s.toMonoidHom = B₀) (he : B.map e.toMonoidHom = B₁) :
    B₀.map (s.symm.trans e).toMonoidHom = B₁ := by
  change B₀.map (e.toMonoidHom.comp s.symm.toMonoidHom) = B₁
  have hs' : B₀.map s.symm.toMonoidHom = B := (Subgroup.map_symm_eq_iff_map_eq B).mpr hs
  rw [← Subgroup.map_map, hs', he]

/-- Change an already marked diagram witness to an independently supplied
marking. The parabolic compatibility is an explicit geometric obligation. -/
def remarkDiagram {K T : Subgroup D} {φ : K ≃* E}
    {B P Q : Subgroup E} (d : InducedDiagramAction K T φ B P Q)
    (ψ : K ≃* E') (B' P' Q' : Subgroup E')
    (hB : B.map (φ.symm.trans ψ).toMonoidHom = B')
    (hclasses : ∀ R : Subgroup E, R = P ∨ R = Q →
      ∃ S : Subgroup E', (S = P' ∨ S = Q') ∧
        ∃ x : E', R.map (φ.symm.trans ψ).toMonoidHom = S.map (MulAut.conj x).toMonoidHom) :
    InducedDiagramAction K T ψ B' P' Q' := by
  let a := transportDiagram d (φ.symm.trans ψ) B' P' Q' hB hclasses
  have he : MulAut.congr (φ.symm.trans ψ) d.automorphism =
      MulAut.congr ψ (K.normalizerMonoidHom ⟨d.element, d.normalizes⟩) := by
    rw [d.induced]
    ext x
    simp [MulAut.congr]
  exact {
    element := d.element
    mem_T := d.mem_T
    normalizes := d.normalizes
    automorphism := MulAut.congr ψ (K.normalizerMonoidHom ⟨d.element, d.normalizes⟩)
    induced := rfl
    borel := he ▸ a.borel
    moves := he ▸ a.moves }

@[simp] theorem remarkDiagram_element {K T : Subgroup D} {φ : K ≃* E}
    {B P Q : Subgroup E} (d : InducedDiagramAction K T φ B P Q)
    (ψ : K ≃* E') (B' P' Q' : Subgroup E')
    (hB : B.map (φ.symm.trans ψ).toMonoidHom = B')
    (hclasses : ∀ R : Subgroup E, R = P ∨ R = Q →
      ∃ S : Subgroup E', (S = P' ∨ S = Q') ∧
        ∃ x : E', R.map (φ.symm.trans ψ).toMonoidHom = S.map (MulAut.conj x).toMonoidHom) :
    (remarkDiagram d ψ B' P' Q' hB hclasses).element = d.element := rfl

/-- Conjugate the actor marking and translate the linear coordinates by
exactly the same model element. -/
def innerIdentification {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    {I : Submodule (ZMod 2) V} {hI : K ≤ subspaceStabilizer ρ I}
    {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hI σ) (g : E) :
    CentralQuotientIdentification ρ K I hI σ where
  groupEquiv := d.groupEquiv.trans (MulAut.conj g)
  linearEquiv := d.linearEquiv.trans (innerIntertwiner σ g)
  equivariant := innerIntertwiner_equivariant (centralQuotientRepresentation ρ K I hI)
    σ d.groupEquiv.toMonoidHom d.linearEquiv d.equivariant g

/-- The conjugating element is supplied by Sylow conjugacy; no compatibility
between the independent source and module markings is assumed. -/
theorem exists_innerIdentification {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    {I : Submodule (ZMod 2) V} {hI : K ≤ subspaceStabilizer ρ I}
    {σ : Representation (ZMod 2) E X} [Finite E] [Finite E']
    (d : CentralQuotientIdentification ρ K I hI σ)
    (s : K ≃* E') (B : Subgroup K) (B₀ : Subgroup E') (B₁ : Subgroup E)
    (hs : B.map s.toMonoidHom = B₀)
    (h₀ : ∃ P : Sylow 2 E', normalizer (P : Set E') = B₀)
    (h₁ : ∃ P : Sylow 2 E, normalizer (P : Set E) = B₁) :
    ∃ g : E, B.map (innerIdentification d g).groupEquiv.toMonoidHom = B₁ := by
  let : Finite K := Finite.of_equiv E d.groupEquiv.symm.toEquiv
  obtain ⟨g, hg, _⟩ := exists_innerIntertwiner_sylowNormalizer B B₁
    (exists_sylow_normalizer_of_equiv s B B₀ hs h₀) h₁
    (centralQuotientRepresentation ρ K I hI) σ d.groupEquiv d.linearEquiv d.equivariant
  exact ⟨g, hg⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
