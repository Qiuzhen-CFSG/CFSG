module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableMaximal
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePartner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialAmbient

/-!
# The actual centralizer partner in the cubic decomposable row

The original exchanged symmetric-three factors make the literal Sylow
action image maximal. The actual third-local action constraints then give
exactly the two original maximal two-local overgroups. On the full chosen
module, the same image maximality identifies the partner with the
centralizer of the original central seed and identifies its intersection
with M as the action kernel together with T.

The decomposition, its Thompson markings, and the original action map
remain unchanged. No global Thompson residual premise is used.
Source: Aschbacher--Smith 15.1.7(6), 15.1.13--14 and the intersection
argument of 15.2.5, printed pp.1087,1090--1091,1107--1108.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- No third maximal two-local contains the original Sylow subgroup in the
prime-three decomposable row. The same actual Thompson pair is retained. -/
theorem PreparedChosenModule.decomposable_three_maximal_overgroups
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      s.prime = 3 → maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  classical
  let := h.elementary
  intro U c d s π hp hs hdec hthree
  let D := internalActionImage M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let P := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V h.normalized).rangeRestrict_surjective
  have hmax := s.sylow_image_isCoatom_of_prime_three hG T hM h.normalized
    c d π hp hs hdec hthree
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    by_cases hNMc : N = Mc
    · simp [hNMc]
    obtain ⟨_,hnot,hproper⟩ := h.third_maximal_action_constraints
      hG T hempty hM hJ hu hN hNM hNMc
    let A := ((M ⊓ N).subgroupOf M).map f
    have hPA : (P : Subgroup D) < A := by
      refine lt_of_le_of_ne (map_mono
        (subgroupOf_mono M (le_inf hM.1.2 hN.2))) ?_
      intro he
      exact hnot (show IsPGroup 2 A by rw [←he]; exact P.isPGroup')
    exact (hproper (hmax.2 A hPA)).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact hM.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩

/-- The full original cubic decomposable action identifies the literal
partner and its intersection with M, without assuming global normalization. -/
theorem PreparedChosenModule.decomposable_three_partner_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      s.prime = 3 →
      Mc = centralizer (centralInvolutions T : Set G) ∧
        M ⊓ Mc = M ⊓ centralizer (centralInvolutions T : Set G) ∧
        M ⊓ centralizer (centralInvolutions T : Set G) =
          (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  let := h.elementary
  intro U c d s π hp hs hdec hthree
  exact h.nine_partner_centralizer_of_sylow_image_coatom hG hempty hM hJ hu hne hfull
    (s.sylow_image_isCoatom_of_prime_three hG T hM h.normalized c d π hp hs hdec hthree)

end CFSG.Quasithin.Chapter15.Section01
