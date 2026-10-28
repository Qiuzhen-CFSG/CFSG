module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreThompson
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The actual central fixed line in the order-two partner branch

When the original partner module has order two, it equals the central
involution seed, and the partner is its full centralizer. The same fixed
span F has precisely that line fixed by T and by Mc. Every nontrivial
Mc-invariant subgroup of F meets the center of T and contains the line.
This establishes a unique minimal invariant subgroup on the actual F;
it supplies neither reducedness of F nor normalization of E.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual order-two partner fixes its unique minimal invariant line
in the original elementary span F, and this is also its Sylow fixed subgroup. -/
theorem PreparedChosenModule.decomposable_five_partner_two_fixed_line
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
      let Uc := localModule T Mc
      let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
      Uc = centralInvolutions T ∧ Mc = centralizer (centralInvolutions T : Set G) ∧
        F ⊓ centralizer (T : Set G) = Uc ∧ F ⊓ centralizer (Mc : Set G) = Uc ∧
        ∀ W : Subgroup G, W ≤ F → Mc ≤ normalizer (W : Set G) → W ≠ ⊥ → Uc ≤ W := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let Z := centralInvolutions T
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let Q := C.pCoreIn 2
  let F := conjugateSpanBy E C
  obtain ⟨_,_,hQT,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,hFA,heF,_,hnF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let := heF
  have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  have hFT : F ≤ (T : Subgroup G) := by
    intro f hf
    exact hQT (hJQ ((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).1)
  have hUF : Uc ≤ F := (hUE.trans inf_le_left).trans (le_conjugateSpanBy E C)
  have hZU : Z ≤ Uc := le_conjugateSpanBy _ _
  have hZne : Z ≠ ⊥ := centralInvolutions_ne_bot_of_maximal_local T hM.1
  have hUZ : Uc = Z := (eq_of_le_of_card_ge hZU (by
    have hh := (one_lt_card_iff_ne_bot Z).mpr hZne
    change Nat.card Uc = 2 at hcU
    omega)).symm
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMcU : Mc ≤ centralizer (Uc : Set G) := centralizes_of_normalizes_card_two
    hcU (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc)
  have hMcEq : Mc = centralizer (centralInvolutions T : Set G) := by
    apply le_antisymm
    · exact hMcU.trans_eq (congrArg (fun W : Subgroup G => centralizer (W : Set G)) hUZ)
    · exact hMcC.2
  have hfixed : F ⊓ centralizer (T : Set G) = Uc := by
    apply le_antisymm
    · intro f hf
      rw [hUZ]
      exact (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hFT hf.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) f hf.1,
          fun t ht => hf.2 t ht⟩
    · exact le_inf hUF ((le_centralizer_iff.mp hMcU).trans (centralizer_le hTMc))
  have hfixedMc : F ⊓ centralizer (Mc : Set G) = Uc := le_antisymm
    ((inf_le_inf_left F (centralizer_le hTMc)).trans_eq hfixed)
    (le_inf hUF (le_centralizer_iff.mp hMcU))
  refine ⟨hUZ,hMcEq,hfixed,hfixedMc,?_⟩
  intro W hWF hnW hWne
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWF
  have hWT : W ≤ (T : Subgroup G) := hWF.trans hFT
  have hmeet : W ⊓ Uc ≠ ⊥ := by
    obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp
      (inf_centerIn_ne_bot T.isPGroup' hWne hWT (hTMc.trans hnW))
    have hzU : (z : G) ∈ Uc := by
      rw [hUZ]
      exact (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hWT z.property.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property.1,
          z.property.2.2⟩
    intro he
    have hz : (z : G) ∈ (⊥ : Subgroup G) := he ▸ ⟨z.property.1,hzU⟩
    exact hzne (Subtype.ext (mem_bot.mp hz))
  have heq : W ⊓ Uc = Uc := eq_of_le_of_card_ge inf_le_right (by
    have hh := (one_lt_card_iff_ne_bot (W ⊓ Uc : Subgroup G)).mpr hmeet
    change Nat.card Uc = 2 at hcU
    omega)
  exact heq.ge.trans inf_le_left

end CFSG.Quasithin.Chapter15.Section01
