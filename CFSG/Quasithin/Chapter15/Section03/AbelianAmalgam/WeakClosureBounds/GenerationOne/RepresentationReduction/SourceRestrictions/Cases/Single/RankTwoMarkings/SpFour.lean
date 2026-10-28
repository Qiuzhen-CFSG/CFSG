module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.Transport
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RankTwo
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Compatible Sp₄ natural and diagram markings

Sylow conjugacy aligns the natural constituent's group map with the source
Borel, while the same element adjusts its linear coordinates. The established
intrinsic two-local geometry shows that an arbitrary comparison of group
markings preserves the pair of point and plane parabolic conjugacy classes.
This transfers the diagram witness with its actual inducing element of T.

Sylow orders q⁴ recover the target field size from the actual group
equivalence. A finite-field isomorphism and the checked symplectic flag
transport then handle distinct source and module field carriers. No automorphism
classification or additional Borel fixed-space calculation is used.

Source: Aschbacher–Smith, E.2.2(2)(b), printed pp.215–216, and the Sp₄ natural
and diagram pair in 15.3.65, printed p.1152. The constituent identification
and source diagram witness are inputs; branch selection belongs to the caller.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
variable {F F₀ : Type*} [Field F] [Finite F] [Field F₀] [Finite F₀]

/-- The literal symplectic flag Borel is a Sylow-two normalizer. -/
theorem spFour_borel_normalizer {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) :
    ∃ P : Sylow 2 (Sp F), normalizer (P : Set (Sp F)) = borel := by
  exact ⟨unipotentSylow hF hf, borel_eq_normalizer_unipotent.symm⟩

/-- Isomorphic binary Sp₄ carriers have the same defining field order,
as seen from the q⁴ orders of their actual Sylow two-subgroups. -/
theorem spFour_field_card_of_equiv [CharP F 2] {f : ℕ}
    (hF₀ : Nat.card F₀ = 2 ^ f) (hf : 1 ≤ f) (e : Sp F₀ ≃* Sp F) :
    Nat.card F = 2 ^ f := by
  let := Fintype.ofFinite F
  obtain ⟨⟨n, hn⟩, _, hc⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card, PNat.mk_coe] using hc
  let P := unipotentSylow hF₀ hf
  let Q := unipotentSylow hF hn
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card P = Nat.card Q :=
    Nat.card_congr ((e.subgroupMap (P : Subgroup (Sp F₀))).trans (P'.equiv Q)).toEquiv
  change Nat.card (P : Subgroup (Sp F₀)) = Nat.card (Q : Subgroup (Sp F)) at hcard
  dsimp only [P, Q] at hcard
  rw [coe_unipotentSylow, coe_unipotentSylow, card_unipotent, card_unipotent] at hcard
  exact (Nat.pow_left_injective (by decide : 4 ≠ 0) hcard).symm.trans hF₀

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {K T : Subgroup D}
  {I : Submodule (ZMod 2) V} {hI : K ≤ subspaceStabilizer ρ I}
  [Algebra (ZMod 2) F]

/-- Align the natural Sp₄ constituent with the independent source Borel and
diagram marking. Two-local flag geometry proves that the comparison of the
markings preserves the pair of standard parabolic conjugacy classes. -/
theorem spFour_alignment {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (d : CentralQuotientIdentification ρ K I hI
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)))
    (s : K ≃* Sp F) (B : Subgroup K) (hs : B.map s.toMonoidHom = borel)
    (a : InducedDiagramAction K T s borel pointParabolic planeParabolic) :
    ∃ g : Sp F, B.map (innerIdentification d g).groupEquiv.toMonoidHom = borel ∧
      ∃ a' : InducedDiagramAction K T (innerIdentification d g).groupEquiv
        borel pointParabolic planeParabolic, a'.element = a.element := by
  let : CharP F 2 := (Algebra.charP_iff (ZMod 2) F 2).mp inferInstance
  obtain ⟨g, hg⟩ := exists_innerIdentification d s B _ _ hs
    (spFour_borel_normalizer hF (by omega)) (spFour_borel_normalizer hF (by omega))
  have hb := comparison_borel s (innerIdentification d g).groupEquiv B _ _ hs hg
  exact ⟨g, hg, remarkDiagram a _ _ _ _ hb
    (DiagramAutomorphisms.map_parabolic_eq_conjugate (field_card_gt_two hF hf) _), rfl⟩

/-- The same construction for distinct concrete fields of the source order.
Entrywise field transport identifies both literal parabolics and the Borel;
the subsequent comparison is allowed to permute their conjugacy classes. -/
theorem spFour_alignment_fields {f : ℕ}
    (hF₀ : Nat.card F₀ = 2 ^ f) (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (d : CentralQuotientIdentification ρ K I hI
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)))
    (s : K ≃* Sp F₀) (B : Subgroup K) (hs : B.map s.toMonoidHom = borel)
    (a : InducedDiagramAction K T s borel pointParabolic planeParabolic) :
    ∃ g : Sp F, B.map (innerIdentification d g).groupEquiv.toMonoidHom = borel ∧
      ∃ a' : InducedDiagramAction K T (innerIdentification d g).groupEquiv
        borel pointParabolic planeParabolic, a'.element = a.element := by
  let := Fintype.ofFinite F₀
  let := Fintype.ofFinite F
  let c : F₀ ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hF₀.trans hF.symm)
  let e := Binary.fieldEquivSp c
  have hc : ∀ R : Subgroup (Sp F₀), R = pointParabolic ∨ R = planeParabolic →
      ∃ S : Subgroup (Sp F), (S = pointParabolic ∨ S = planeParabolic) ∧
        ∃ x : Sp F, R.map e.toMonoidHom = S.map (MulAut.conj x).toMonoidHom := by
    intro R hR
    rcases hR with rfl | rfl
    · refine ⟨_, Or.inl rfl, 1, ?_⟩
      rw [map_one]
      change _ = (pointParabolic (F := F)).map (MonoidHom.id _)
      rw [Subgroup.map_id]
      exact Binary.map_pointParabolic c
    · refine ⟨_, Or.inr rfl, 1, ?_⟩
      rw [map_one]
      change _ = (planeParabolic (F := F)).map (MonoidHom.id _)
      rw [Subgroup.map_id]
      exact Binary.map_planeParabolic c
  let a₁ := transportDiagram a e _ _ _ (Binary.map_borel c) hc
  have hs₁ : B.map (s.trans e).toMonoidHom = borel := by
    change B.map (e.toMonoidHom.comp s.toMonoidHom) = _
    rw [← Subgroup.map_map, hs]
    exact Binary.map_borel c
  obtain ⟨g, hg, a', he⟩ := spFour_alignment hF hf d (s.trans e) B hs₁ a₁
  exact ⟨g, hg, a', he⟩

/-- Complete compatibility of the independently supplied source and natural
Sp₄ markings, including the target field parameter and the original T element. -/
theorem spFour_compatible_markings {f : ℕ}
    (hF₀ : Nat.card F₀ = 2 ^ f) (hf : 1 < f)
    (d : CentralQuotientIdentification ρ K I hI
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)))
    (s : K ≃* Sp F₀) (B : Subgroup K) (hs : B.map s.toMonoidHom = borel)
    (a : InducedDiagramAction K T s borel pointParabolic planeParabolic) :
    Nat.card F = 2 ^ f ∧
    ∃ g : Sp F, B.map (innerIdentification d g).groupEquiv.toMonoidHom = borel ∧
      ∃ a' : InducedDiagramAction K T (innerIdentification d g).groupEquiv
        borel pointParabolic planeParabolic, a'.element = a.element := by
  let : CharP F 2 := (Algebra.charP_iff (ZMod 2) F 2).mp inferInstance
  have hF := spFour_field_card_of_equiv hF₀ (by omega) (s.symm.trans d.groupEquiv)
  exact ⟨hF, spFour_alignment_fields hF₀ hF hf d s B hs a⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
