module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Alternatives
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Mathlib.LinearAlgebra.Pi

/-!
# Transport of the complete intrinsic MS module alternatives

The intrinsic C.1.34 contract and the original ambient section contract
refer to the same subgroup Q=[O₂(J),L] when L and R generate J. We transport
all five cases, retaining the same quotient marking and the literal
conjugation on each section. Single and double representation copies are
identified by their coordinate equivalences. The central direct sum and the
index-seven point stabilizer are transported without extra hypotheses.

Source: Aschbacher–Smith, C.1.34(1)–(5), printed pp.136–137.
-/

@[expose] public section
open Subgroup Representation Stellmacher CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve
variable {D : Type*} [Group D]

private theorem section_model_transport {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {L A B : Subgroup D}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F}
    {ρ : Representation F (Matrix.SpecialLinearGroup (Fin 3) F) V}
    {σ : Representation F (Matrix.SpecialLinearGroup (Fin 3) F) W}
    (h : SourceInterface.HasSectionModel L A B (SourceInterface.linearThreeActor e) ρ)
    (f : V ≃+ W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) :
    Nonempty (LayerModel L A B e σ) := by
  obtain ⟨hBA, hLA, _, hn, φ, hφ⟩ := h
  let := hn
  refine ⟨{
    lower_le := hBA
    normalized := hLA
    lower_normal := hn
    quotientIso := φ.trans f.toMultiplicative
    intertwining := ?_ }⟩
  intro l a
  change f (Multiplicative.toAdd (φ (QuotientGroup.mk' _ (layerConjugate L A hLA l a)))) = _
  rw [hφ l a (layerConjugate L A hLA l a) rfl]
  exact hf _ _

private theorem section_model_one {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] {L A B : Subgroup D}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F}
    {ρ : Representation F (Matrix.SpecialLinearGroup (Fin 3) F) V}
    (h : SourceInterface.HasSectionModel L A B (SourceInterface.linearThreeActor e) ρ) :
    Nonempty (LayerModel L A B e (moduleCopies ρ 1)) :=
  section_model_transport h (AddEquiv.piUnique (fun _ : Fin 1 => V)).symm (by
    intro g v
    rfl)

private theorem section_model_two {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] {L A B : Subgroup D}
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F}
    {ρ : Representation F (Matrix.SpecialLinearGroup (Fin 3) F) V}
    (h : SourceInterface.HasSectionModel L A B (SourceInterface.linearThreeActor e) (ρ.prod ρ)) :
    Nonempty (LayerModel L A B e (moduleCopies ρ 2)) :=
  section_model_transport h (LinearEquiv.finTwoArrow F V).symm.toAddEquiv (by
    intro g v
    ext i
    fin_cases i <;> rfl)

private theorem ambient_center_top : SourceInterface.centerIn (⊤ : Subgroup D) = center D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_center_iff.mpr fun y => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, mem_top y⟩)
  · intro hx
    exact ⟨⟨x, mem_top x⟩, mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y)), rfl⟩

private theorem central_complement {Z C U : Subgroup D}
    (hCZ : C ≤ Z) (hUZ : U ≤ Z) (hC : C ≤ center D)
    (hZ : Z = C ⊔ U) (hdis : C ⊓ U = ⊥) :
    (U.subgroupOf Z).IsComplement' (C.subgroupOf Z) := by
  have : C.Normal := ⟨by
    intro c hc g
    have he := mem_center_iff.mp (hC hc) g
    simpa only [he, mul_inv_cancel_right] using hc⟩
  refine ⟨mul_injective_of_disjoint ?_, ?_⟩
  · apply disjoint_iff_inf_le.mpr
    intro z hz
    have hz' : (z : D) ∈ C ⊓ U := ⟨hz.2, hz.1⟩
    have he : (z : D) = 1 := by simpa only [hdis, mem_bot] using hz'
    exact Subtype.ext he
  · intro z
    have hz : (z : D) ∈ U ⊔ C := by simpa only [hZ, sup_comm] using z.property
    obtain ⟨u, hu, c, hc, he⟩ := mem_sup_of_normal_right.mp hz
    exact ⟨(⟨⟨u, hUZ hu⟩, hu⟩, ⟨⟨c, hCZ hc⟩, hc⟩), Subtype.ext he⟩

/-- The full intrinsic C.1.34 alternatives imply their original ambient
section formulation whenever the displayed MS pair generates the ambient group. -/
theorem alternatives_of_MSModuleAlternatives {L R : Subgroup D}
    (hgen : L ⊔ R = ⊤) (S : Sylow 2 D) (n : ℕ) (F : Type) [Field F]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (h : SourceInterface.MSModuleAlternatives L R (S : Subgroup D) n F e) :
    Alternatives F n L R S e := by
  have hcore : (⊤ : Subgroup D).pCoreIn 2 = pCore 2 D := pCore_map_iso 2 topEquiv
  have hQ : SourceInterface.msQ L R = sourceQ L := by rw [SourceInterface.msQ, hgen, hcore]
  have hcenter : SourceInterface.centerIn (L ⊔ R) = center D := by rw [hgen, ambient_center_top]
  have hineq (h : SourceInterface.MSNotCentralizerCore L R (S : Subgroup D)) :
      RadicalInequality R S := by
    unfold SourceInterface.MSNotCentralizerCore at h
    rw [hgen, top_inf_eq] at h
    exact h
  dsimp only [SourceInterface.MSModuleAlternatives] at h
  rw [hQ] at h
  rcases h with h | h | h | h | h
  · exact .one h.2.1 (section_model_one h.2.2)
  · exact .two (section_model_two h.1) (hineq h.2)
  · exact .three (section_model_one h.1) (section_model_two h.2.1) (hineq h.2.2)
  · obtain ⟨hel, hcard, hc, hsum, hdis, hnat, hphi, hcen, hupp, hrad⟩ := h
    change sourceFixed L ≤ SourceInterface.centerIn (L ⊔ R) at hc
    rw [hcenter] at hc
    change sourceCenter L = sourceFixed L ⊔ sourceNatural L at hsum
    change sourceFixed L ⊓ sourceNatural L = ⊥ at hdis
    have hCZ : sourceFixed L ≤ sourceCenter L := hsum ▸ le_sup_left
    have hUZ : sourceNatural L ≤ sourceCenter L := hsum ▸ le_sup_right
    exact .four hel hcard hc hCZ hUZ (central_complement hCZ hUZ hc hsum hdis)
      (section_model_one hnat) (section_model_one hphi)
      (section_model_two hcen) (section_model_two hupp) (hineq hrad)
  · obtain ⟨⟨eb⟩, ⟨ec⟩, hnat, homega, hpoint⟩ := h
    refine .five ⟨eb.trans Matrix.PSL3Two.equiv.symm⟩ ?_ (section_model_one hnat) ?_ ?_
    · exact (Nat.card_congr ec.toEquiv).trans (by simp)
    · simpa only [hcenter, SourceInterface.omegaCenterIn, omegaOneCenterAmbient] using homega
    · unfold SourceInterface.MSPointStabilizer at hpoint
      rw [hQ] at hpoint
      obtain ⟨G₁, q, hq, _, hSG, hidx, hrad, hpoint⟩ := hpoint
      rw [hgen] at hidx
      refine ⟨G₁, ?_, hSG, hrad, ?_⟩
      · exact (relIndex_top_right G₁).symm.trans hidx
      · exact ⟨q, hq, fun g => hpoint g (hgen ▸ mem_top g)⟩

/-- Apply an intrinsic full MS description to the original Sylow subgroup,
keeping its chosen quotient marking in every section. -/
theorem alternatives_of_MSDescription {κ : GroupClass} {L R : Subgroup D}
    (hgen : L ⊔ R = ⊤) (S : Sylow 2 D) (hRS : R ≤ (S : Subgroup D))
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (h : SourceInterface.MSDescription κ L R n F) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      Alternatives F n L R S e := by
  have hSylow : Chapter1.IsSylowIn 2 (S : Subgroup D) (L ⊔ R) := by
    rw [hgen]
    exact Chapter1.isSylowIn_iff.mpr
      ⟨S.isPGroup', le_top, fun U hU hSU _ => S.is_maximal' hU hSU⟩
  obtain ⟨e, he⟩ := h.2 (S : Subgroup D) hSylow hRS
  exact ⟨e, alternatives_of_MSModuleAlternatives hgen S n F e he⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
