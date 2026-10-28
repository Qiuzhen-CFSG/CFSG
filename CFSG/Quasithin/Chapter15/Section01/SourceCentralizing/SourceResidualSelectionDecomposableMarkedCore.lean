module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposablePartner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableSylowSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.Radical

/-!
# The original decomposable fixed group in the center of Q₁

An elementary abelian subgroup E lies in the central omega subgroup of
O₂(C_G(E)): it is a central normal two-subgroup of its own centralizer.
The prime-three decomposable geometry identifies the actual M_Z with this
centralizer. Thus the same sixteen-element E lies in Ω₁Z(Q₁), with the
original four-element marking and central seed as complementary factors.

The literal radical remains inside C_T(E). No normalization of E by L,
identification with Ω₁Z(O₂(LQ₁)), or Sylow property of Q₁ in LQ₁ is asserted.

Source: Aschbacher--Smith 15.1.17--20, printed pp.1093--1095.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- A marked elementary centralizer places its same marking in Ω₁Z(Q₁). -/
theorem CaseIComponentData.le_omegaCenter_radical_of_marked_centralizer
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (e : CaseIComponentData T M Mc V) (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hMZ : e.MZ = centralizer (E : Set G)) :
    E ≤ omegaOneCenterAmbient e.Q1 := by
  have hEC : E ≤ centralizer (E : Set G) := E.le_centralizer
  have hEQ : E ≤ e.Q1 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 E) (hEC.trans_eq hMZ.symm)
    (hMZ.le.trans (Subgroup.centralizer_le_normalizer _))
  intro x hx
  refine (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hEQ hx,?_,?_⟩
  · exact congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) ⟨x,hx⟩)
  · intro q hq
    exact (hMZ.le (e.Q1_le_MZ hq) x hx).symm

/-- The actual prime-three source retains the sixteen-element fixed group,
both original four-groups, and their central containment in its literal Q₁. -/
theorem PreparedChosenModule.decomposable_three_marked_core_geometry
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
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      s.prime = 3 →
    ∀ e : CaseIComponentData T M Mc V,
      e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space →
      e.PreExclusionSource h.normalized 3 →
      e.MZ = centralizer (thompsonFixed T V : Set G) ∧
        thompsonFixed T V ≤ omegaOneCenterAmbient e.Q1 ∧
        e.Q1 ≤ (T : Subgroup G) ⊓ centralizer (thompsonFixed T V : Set G) ∧
        Nat.card (thompsonFixed T V) = 16 ∧
        Nat.card (centralInvolutions T) = 4 ∧ Nat.card e.Z1 = 4 ∧
        Disjoint e.Z1 (centralInvolutions T) ∧
        e.Z1 ⊔ centralInvolutions T = thompsonFixed T V := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hthree e heZ es
  have hMc := (h.decomposable_three_partner_centralizer
    hG T hempty hM hJ hu hne hfull c d s π hp hs hdec hthree).1
  have hMZ : e.MZ = centralizer (thompsonFixed T V : Set G) := by
    change centralizer (e.Z1 : Set G) ⊓ Mc = _
    rw [heZ,inf_comm]
    exact (s.marked_partner_centralizer_of_prime_three
      hG T hM h hfull hMc c d hd π hp hs hthree).1
  let : IsElementaryAbelian 2 (thompsonFixed T V) := IsElementaryAbelian.of_le inf_le_left
  have hQ : e.Q1 ≤ (T : Subgroup G) ⊓ centralizer (thompsonFixed T V : Set G) :=
    le_inf ((e.catalogue_radical_le_sylow es.centralizer_sylow hu).trans e.S_le_T)
      (e.Q1_le_MZ.trans_eq hMZ)
  obtain ⟨hZ,ha,hgen,_,_⟩ := s.central_seed_geometry_of_prime_three
    hG T hM h hfull c d hd π hp hs hthree
  refine ⟨hMZ,e.le_omegaCenter_radical_of_marked_centralizer _ hMZ,hQ,
    s.fixed_card,hZ,?_,?_,?_⟩
  · rw [heZ]
    exact s.thompson_card s.first
  · exact heZ.symm ▸ ha
  · exact heZ.symm ▸ hgen

end CFSG.Quasithin.Chapter15.Section01
