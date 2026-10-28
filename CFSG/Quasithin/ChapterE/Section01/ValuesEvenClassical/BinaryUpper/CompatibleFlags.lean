module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.CompatibleFlags.Alignment
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.CompatibleFlags.Solvable
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.CompatibleFlags.MiddleSection
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Compatible generating flags for the binary cases of E.1.14(1)

Sylow conjugacy supplies a single model equivalence for which both actual
generating flags are normalized by the ambient Sylow subgroup, including its
graph automorphisms. For this same marking, the diagonal calculations prove
that the outer flag is solvable. The middle flag is solvable in dimension four;
in dimension five its quotient by its intrinsic two-core has simple generalized
Fitting subgroup isomorphic to PSL₃(2), supplemented by a Sylow two-subgroup.

The final application uses the genuine SQTK hypotheses with `L = F*(G)` and
`G = LT`. It supplies the two generating overgroups, each containing `T`, and
their local structures without any extra alignment or quotient premise. These
are the local structural inputs to the binary upper bound; the E-generation
bounds and the final equality `n(G) = 1` belong to its consuming argument.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.14(1), printed p.214, citing Aschbacher (1982), Lemma 4.7.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper

/-- A single Sylow-compatible marking gives the two normalized flag factors
whose actual ambient overgroups contain `T` and generate `G`. Local quotient
calculations can use this same marking for both members of the family. -/
theorem exists_sylowAligned_generating_flags {G : Type*} [Group G] [Finite G]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* PSL d) (hLT : L ⊔ (T : Subgroup G) = ⊤) :
    ∃ e' : L ≃* PSL d,
      SylowAligned L (T : Subgroup G) e' ∧
      (T : Subgroup G) ≤ Subgroup.normalizer (transportedParabolic L e' (outerRoots d) : Set G) ∧
      (T : Subgroup G) ≤ Subgroup.normalizer (transportedParabolic L e' (middleRoots d) : Set G) ∧
      (∀ H ∈ binaryFlagFamily L (T : Subgroup G) e', (T : Subgroup G) ≤ H) ∧
      sSup (binaryFlagFamily L (T : Subgroup G) e') = ⊤ := by
  let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨e', he'⟩ := exists_sylowAligned L T e (by omega)
  exact ⟨e', he', sylowAligned_outer_normalizes hd L _ e' he',
    sylowAligned_middle_normalizes hd L _ e' he',
    fun _ hH => le_of_mem_binaryFlagFamily L _ e' hH,
    binaryFlagFamily_generates L _ e' hLT⟩

/-- Choose one marking for both generating flags and discharge their local
structure simultaneously. The middle flag has its stronger dimension-specific
conclusion, and the five-dimensional quotient retains any graph extension. -/
theorem exists_sylowAligned_structured_generating_flags
    {G : Type*} [Group G] [Finite G]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* PSL d) (hLT : L ⊔ (T : Subgroup G) = ⊤) :
    ∃ e' : L ≃* PSL d,
      SylowAligned L (T : Subgroup G) e' ∧
      Group.IsSolvable (ambientFlag L (T : Subgroup G) e' (outerRoots d)) ∧
      ((d = 4 ∧ Group.IsSolvable (ambientFlag L (T : Subgroup G) e' (middleRoots d))) ∨
        (d = 5 ∧ HasBinaryMiddleSection (ambientFlag L (T : Subgroup G) e' (middleRoots d)))) ∧
      (∀ H ∈ binaryFlagFamily L (T : Subgroup G) e', (T : Subgroup G) ≤ H) ∧
      sSup (binaryFlagFamily L (T : Subgroup G) e') = ⊤ := by
  obtain ⟨e', he', _, _, hT, hgen⟩ := exists_sylowAligned_generating_flags hd L T e hLT
  refine ⟨e', he', ambientFlag_outer_isSolvable hd L T e' he', ?_, hT, hgen⟩
  rcases hd with rfl | rfl
  · exact Or.inl ⟨rfl, ambientFlag_middle_four_isSolvable L T e' he'⟩
  · exact Or.inr ⟨rfl, sylowAligned_hasBinaryMiddleSection L T e' he'⟩

/-- The local structural input for the binary cases of E.1.14(1), applied to
the actual generalized Fitting subgroup. Every member of the explicit generating
family contains the source Sylow subgroup and is either solvable or has the
proved binary middle section. No local E-generation bound is assumed. -/
theorem sqtk_exists_compatible_flags {G : Type*} [Group G] [Finite G]
    {K : GroupClass} (_hG : IsSQTK K G)
    [IsSimpleGroup (Theory.GroupTheory.generalizedFitting G)]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (T : Sylow 2 G)
    (e : Theory.GroupTheory.generalizedFitting G ≃* PSL d)
    (hLT : Theory.GroupTheory.generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    ∃ e' : Theory.GroupTheory.generalizedFitting G ≃* PSL d,
      SylowAligned (Theory.GroupTheory.generalizedFitting G) (T : Subgroup G) e' ∧
      Group.IsSolvable
        (ambientFlag (Theory.GroupTheory.generalizedFitting G) (T : Subgroup G) e' (outerRoots d)) ∧
      (Group.IsSolvable
          (ambientFlag (Theory.GroupTheory.generalizedFitting G) (T : Subgroup G) e' (middleRoots d)) ∨
        HasBinaryMiddleSection
          (ambientFlag (Theory.GroupTheory.generalizedFitting G) (T : Subgroup G) e' (middleRoots d))) ∧
      (∀ H ∈ binaryFlagFamily (Theory.GroupTheory.generalizedFitting G) (T : Subgroup G) e',
        (T : Subgroup G) ≤ H ∧ (Group.IsSolvable H ∨ HasBinaryMiddleSection H)) ∧
      sSup (binaryFlagFamily (Theory.GroupTheory.generalizedFitting G) (T : Subgroup G) e') = ⊤ := by
  obtain ⟨e', he', hout, hmid, hT, hgen⟩ :=
    exists_sylowAligned_structured_generating_flags hd
      (Theory.GroupTheory.generalizedFitting G) T e hLT
  have hm := hmid.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  refine ⟨e', he', hout, hm, ?_, hgen⟩
  intro H hH
  refine ⟨hT H hH, ?_⟩
  rcases hH with rfl | hH
  · exact Or.inl hout
  · obtain rfl := hH
    exact hm

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper
