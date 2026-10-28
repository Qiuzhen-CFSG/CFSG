module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineRankOne
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension

/-!
# Irreducibility removes the six-letter core from the original central list

The exact canonical action is faithful and irreducible. A marked six-letter
augmentation core would supply a nonzero globally fixed vector, the all-one
vector, contradicting those original properties. The remaining alternatives
retain their native actor isomorphism and intertwining linear equivalence.
No full-numerator kernel is discarded and no remaining natural row is excluded.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u

private theorem not_six_core_model_of_faithful_irreducible
    {J X : Type*} [Group J] [AddCommGroup X] [Module (ZMod 2) X]
    (τ : Representation (ZMod 2) J X) (hf : Function.Injective τ)
    (hi : IsIrreducible τ) :
    ¬ ChapterG.Section06.HasModelOn τ ⊤ ⊤
      (BinaryPermutation.coreRepresentation (Fin 6)) := by
  rintro ⟨e,E,stable,hE⟩
  let eg : J ≃* Equiv.Perm (Fin 6) := topEquiv.symm.trans e
  let ev : X ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6) := Submodule.topEquiv.symm.trans E
  let : Nontrivial J := eg.symm.injective.nontrivial
  have hzero := invariants_eq_bot_of_faithful_irreducible τ hf hi
  let z : BinaryPermutation.core (Fin 6) := ⟨BinaryPermutation.allOne (Fin 6),by
    change (∑ _i : Fin 6, (1 : ZMod 2)) = 0
    decide⟩
  have hz : z ≠ 0 := by
    intro he
    have hh := congrArg (fun x : BinaryPermutation.core (Fin 6) => x.val 0) he
    exact one_ne_zero hh
  let v := ev.symm z
  have hv : v ∈ τ.invariants := by
    intro g
    apply ev.injective
    have he := hE ⟨g,mem_top g⟩ ⟨v,Submodule.mem_top⟩
    change ev (τ g v) = BinaryPermutation.coreRepresentation (Fin 6) (eg g) (ev v) at he
    rw [he,show ev v = z from ev.apply_symm_apply z]
    apply Subtype.ext
    exact BinaryPermutation.permute_allOne (Fin 6) (eg g)
  have hv0 : v = 0 := by simpa only [hzero,Submodule.mem_bot] using hv
  apply hz
  rw [←show ev v = z from ev.apply_symm_apply z,hv0,map_zero]

variable {G : Type u} [Group G] [Finite G]

/-- The same irreducible rank-one canonical action has one of the three
remaining native central models, and its original V-image normally generates. -/
theorem PreparedChosenModule.decomposable_five_partner_two_line_rank_one_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (_dF : BinaryConjugationSection Mc F D ρ),
          Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          rank A = 1 →
          normalClosure (A : Set (actionImage ρ)) = ⊤ ∧
            ((∃ n : ℕ, 2 ≤ n ∧ n ≤ 5 ∧ ChapterG.Section06.HasModelOn σ ⊤ ⊤
                (ChapterG.Section06.binaryLinearAction n)) ∨
              ChapterG.Section06.HasModelOn σ ⊤ ⊤
                (BinaryPermutation.naturalRepresentation (Fin 6)) ∨
              ChapterG.Section06.HasModelOn σ ⊤ ⊤
                (BinaryPermutation.naturalRepresentation (Fin 7))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hline
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  change rank A = 1 → _
  intro hr
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  obtain ⟨_,_,_,hd₁,_,_,_,_⟩ :=
    ((h.decomposable_five_partner_two_line_costs hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hline
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp
    (lt_of_lt_of_le (by rw [hd₁]; decide) (Submodule.finrank_le
      (dF.imageSpace (thompsonPlane T V (c.ambientFactor d s.first).space))))
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  have hi : IsIrreducible σ := imageRepresentation_isIrreducible ρ hirr
  obtain ⟨hgen,hm⟩ :=
    ((h.decomposable_five_partner_two_line_rank_one_central_model
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hline hr
  refine ⟨hgen,?_⟩
  rcases hm with hn | h6 | h7 | hc
  · exact Or.inl hn
  · exact Or.inr (Or.inl h6)
  · exact Or.inr (Or.inr h7)
  · exact (not_six_core_model_of_faithful_irreducible σ (imageRepresentation_injective ρ) hi hc).elim

end CFSG.Quasithin.Chapter15.Section01
