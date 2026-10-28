module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ActionAssembly
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.NormalizerIrreducible

/-!
# The complete chosen critical pair and its terminal contradiction

Partner-core containment now holds in every original structural alternative.
The proved involution actions, hyperplane control, weak closure, Burnside
fusion and critical-track construction give the actual source pair, with
both coranks equal to one. The final consumer applies the already established
normal-closure transport and E.3.6 contradiction.

All remaining premises are preceding source conclusions: the chosen module
and small parabolics (qt-e-152-small-parabolic), the residual and marked plane
geometry (qt-e-152-plane-geometry and qt-e-152-residual-geometry), and plane
uniqueness (qt-e-152-plane-uniqueness). Their final discharge belongs to
qt-e-152-chosen-action-contradiction. No partner-core, chief-recognition,
parabolic, weak-closure or critical-track callback remains.

Source: Aschbacher–Smith 15.2.25–28 and the terminal argument, pp.1118–1120.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChapterE ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The full source critical-pair family, including literal weak closures and both exact coranks. -/
theorem source_chosen_critical_pair
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hMH : M ⊓ H = (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hi : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G))
    (b : internalActionImage M V h.prepared.normalized)
    (hb : b ∈ (T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)
    (hb2 : orderOf b = 2)
    (hfixed : ∀ v : V, (v : G) ∈ ZS ↔ b.val v = v)
    (hc : ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),zpowers b⁆ =
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized))
    (hcases : letI := h.prepared.elementary
      (SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
        SmallChosenActionModels (internalActionImage M V h.prepared.normalized)) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    V ≤ twoCoreIn Mc ∧
      (∀ x ∈ (T : Subgroup G), x ^ 2 = 1 →
        x ∈ (T : Subgroup G) ⊓ centralizer (ZS : Set G)) ∧
      ⁅V,(T : Subgroup G) ⊓ centralizer (ZS : Set G)⁆ ≤ ZS ∧
      (letI := h.prepared.elementary; 1 < globalS V) ∧
      indexedWeakClosure V (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      indexedWeakClosure V (twoCoreIn H) 0 ≤
        H ⊓ centralizer (conjugateSpan H V : Set G) ∧
      (∀ g : G, ZS ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) ∧
      ∃ g : G,
        subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) = 1 ∧
        subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
          (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) = 1 ∧
        ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
        ZS ⊓ ZS.map (MulAut.conj g).toMonoidHom = ⊥ := by
  let := h.prepared.elementary
  have hcore := source_chosen_partner_core h hgeo hMc hZ hquotient hres hs hplane
  obtain ⟨_,_,hTS,hcomm,hr⟩ := source_chosen_involution_actions h hgeo hu hi b hb hb2
    hfixed hc hcases
  have hR := source_chosen_globalR_gt_one_of_core h hgeo hu hcore
  obtain ⟨hS,hW,hWH⟩ := source_chosen_weakClosure_of_globalR T h H hgeo.outside hR
    h.module_parameters.1 h.module_parameters.2
  exact ⟨hcore,hTS,hcomm,hS,hW,hWH,
    source_chosen_overlap_of_core T h hgeo hu (hW.trans inf_le_right) hcore,
    source_chosen_corank_one_of_source_track T h hgeo hMH hunique hu
      h.module_parameters.1 h.module_parameters.2 hcore hr⟩

/-- The chosen-action terminal consumer, retaining only the original earlier-source premises. -/
theorem source_chosen_contradiction_of_action_models
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hMH : M ⊓ H = (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hi : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G))
    (b : internalActionImage M V h.prepared.normalized)
    (hb : b ∈ (T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)
    (hb2 : orderOf b = 2)
    (hfixed : ∀ v : V, (v : G) ∈ ZS ↔ b.val v = v)
    (hc : ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),zpowers b⁆ =
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized))
    (hcases : letI := h.prepared.elementary
      (SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
        SmallChosenActionModels (internalActionImage M V h.prepared.normalized)) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) : False := by
  obtain ⟨_,hTS,hcomm,hS,_,_,hoverlap,g,hfirst,hsecond,hmove,_⟩ :=
    source_chosen_critical_pair h hgeo hu hMH hunique hi b hb hb2 hfixed hc hcases
      hMc hZ hquotient hres hs hplane
  exact source_chosen_contradiction_of_critical_pair T h H ZS hgeo hTS hcomm hS
    hoverlap g hfirst.le hsecond.le hmove

end CFSG.Quasithin.Chapter15.Section02
