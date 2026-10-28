module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.FaithfulMoved.BaumannPair
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.FaithfulMoved.BaumannPair.IntrinsicControl
/-!
# The Baumann-invariant intrinsic factor pair in the original local quotient

The faithful moved action supplies the intrinsic pair and its complementary
four-group moved spaces. Orthogonal coordinates identify every Baumann action
as preserving the two definite planes; the intrinsic control theorem then fixes
each cubic factor individually. Mapping to the original M/O₂(M) and taking the
actual two-residual preimages preserves this invariance. The same pair retains
its M-permutation and its original T-interchange.

No factor permutation or individual Baumann invariance is assumed. All inputs
are exactly the preceding 15.4.11 hypotheses, Y membership, and clause (3).
Source: Aschbacher--Smith, 15.4.12(6)(ii), printed pp.1160--1161,
combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
open BinaryNormalizer
open LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]

/-- The single marked pair satisfies the moved-space decomposition, original
quotient structure, M permutation, Baumann invariance, and T interchange. -/
theorem Input.marked_double_baumann_factors {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ ρ : image M X →* MulAut (movedModule (T : Subgroup G) M X),
      Function.Injective ρ ∧
      (∀ (x : X) (w : movedModule (T : Subgroup G) M X),
        (ρ (memberProjection M X h.member_le x) w : G) =
          (x : G) * (w : G) * (x : G)⁻¹) ∧
      letI := MulDistribMulAction.compHom (movedModule (T : Subgroup G) M X) ρ
      ∃ P : FactorPair (A := image M X) (W := movedModule (T : Subgroup G) M X),
        (∀ i, Nat.card (commutatorAction (P.line i) (movedModule (T : Subgroup G) M X)) = 4) ∧
        IsCompl (commutatorAction (P.line false) (movedModule (T : Subgroup G) M X))
          (commutatorAction (P.line true) (movedModule (T : Subgroup G) M X)) ∧
        let A := quotientFactors M X (movedModule (T : Subgroup G) M X) P
        (∀ i, Nat.card (A i) = 3) ∧ Function.Injective A ∧
        A false ⊔ A true = image M X ∧
        (∀ (g : M) i, ∃ j,
          (A i).map (MulAut.conj (quotientMap M g)).toMonoidHom = A j) ∧
        (∀ i, ((ChapterB.baumann (T : Subgroup G)).subgroupOf M).map (quotientMap M) ≤
          normalizer (A i : Set (CoreQuotient M))) ∧
        (∀ i, ChapterB.baumann (T : Subgroup G) ≤ normalizer (liftedFactors M (quotientMap M) A i : Set G)) ∧
        ∃ t ∈ (T : Subgroup G),
          (liftedFactors M (quotientMap M) A false).map (MulAut.conj t).toMonoidHom =
            liftedFactors M (quotientMap M) A true ∧
          (liftedFactors M (quotientMap M) A true).map (MulAut.conj t).toMonoidHom =
            liftedFactors M (quotientMap M) A false ∧
          t ∉ normalizer (liftedFactors M (quotientMap M) A false : Set G) := by
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 3 (image M X) := h.image_structure.1
  let : IsElementaryAbelian 2 W := h.moved_elementary
  obtain ⟨c,γ,ρ,hi,hρ,hc,hγ,hbase⟩ := h.double_orthogonal_baumann
  let _ := MulDistribMulAction.compHom W ρ
  let _ : FaithfulSMul (image M X) W := ⟨fun {a b} he => hi (MulEquiv.ext he)⟩
  have hA : Nat.card (image M X) = 9 := by simpa using h.image_structure.2
  have hW : Nat.card W = 16 := by simpa using h.moved_card
  obtain ⟨P⟩ := exists_factorPair (W := W) hA hW
  let A := quotientFactors M X W P
  have hnX := (normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal
  have hintr (b : (ChapterB.baumann (T : Subgroup G)).subgroupOf M) i :
      (P.line i).map (imageConjugation M X hnX b).toMonoidHom = P.line i := by
    apply factorPair_map_eq_of_noninterchanging_coordinates ρ hi c hc
      (imageConjugation M X hnX b) (moduleConjugation M W h.moved_normalized b)
      (source_intertwining M X W h.member_le hnX h.moved_normalized ρ hρ b)
      (γ b) _ (hbase b) P i
    intro w
    apply c.symm.injective
    rw [c.symm_apply_apply]
    exact Subtype.ext (hγ b w).symm
  have hquot (b : (ChapterB.baumann (T : Subgroup G)).subgroupOf M) i :
      (A i).map (MulAut.conj (quotientMap M b)).toMonoidHom = A i := by
    have hh := congrArg (Subgroup.map (image M X).subtype) (hintr b i)
    rw [map_map] at hh
    have he : (image M X).subtype.comp (imageConjugation M X hnX b).toMonoidHom =
        (MulAut.conj (quotientMap M b)).toMonoidHom.comp (image M X).subtype := by
      ext a
      rfl
    rw [he] at hh
    simpa only [A,quotientFactors,map_map] using hh
  have hnS i : ((ChapterB.baumann (T : Subgroup G)).subgroupOf M).map (quotientMap M) ≤
      normalizer (A i : Set (CoreQuotient M)) := by
    rintro _ ⟨b,hb,rfl⟩
    exact mem_normalizer_iff_map_conj_eq.mpr (hquot ⟨b,hb⟩ i)
  have hSM : ChapterB.baumann (T : Subgroup G) ≤ M :=
    (show ChapterB.baumann (T : Subgroup G) ≤ (T : Subgroup G) from inf_le_left).trans h.sylow_le
  obtain ⟨hcard,hinj,hgen⟩ := quotientFactors_structure M X W P
  obtain ⟨hmoved,hcompl⟩ := P.moved_decomposition hW
  refine ⟨ρ,hi,hρ,P,hmoved,hcompl,hcard,hinj,hgen,
    source_pair_permuted M X W h.member_le hnX h.moved_normalized hA hW ρ hi hρ P,
    hnS,?_,?_⟩
  · intro i
    have hh := liftedFactors_normalized M (quotientMap M) A
      ((ChapterB.baumann (T : Subgroup G)).subgroupOf M) i (hnS i)
    rwa [map_subgroupOf_eq_of_le hSM] at hh
  · exact source_pair_swap M X W (T : Subgroup G) h.member_le h.sylow_le hnX
      h.moved_normalized hA hW ρ hi hρ h.image_irreducible P

/-- The same quotient pair, ready for the residual-factor algebra consumer. -/
theorem Input.double_quotient_baumann_factors {K : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ A : Bool → Subgroup (CoreQuotient M),
      (∀ i, Nat.card (A i) = 3) ∧ Function.Injective A ∧
      A false ⊔ A true = image M X ∧
      (∀ (g : M) i, ∃ j,
        (A i).map (MulAut.conj (quotientMap M g)).toMonoidHom = A j) ∧
      (∀ i, ((ChapterB.baumann (T : Subgroup G)).subgroupOf M).map (quotientMap M) ≤
        normalizer (A i : Set (CoreQuotient M))) ∧
      (∀ i, ChapterB.baumann (T : Subgroup G) ≤ normalizer (liftedFactors M (quotientMap M) A i : Set G)) ∧
      ∃ t ∈ (T : Subgroup G),
        (liftedFactors M (quotientMap M) A false).map (MulAut.conj t).toMonoidHom =
          liftedFactors M (quotientMap M) A true ∧
        (liftedFactors M (quotientMap M) A true).map (MulAut.conj t).toMonoidHom =
          liftedFactors M (quotientMap M) A false ∧
        t ∉ normalizer (liftedFactors M (quotientMap M) A false : Set G) := by
  obtain ⟨ρ,_,_,P,_,_,hcard,hinj,hgen,hperm,hnS,hnlift,hswap⟩ := h.marked_double_baumann_factors
  let _ := MulDistribMulAction.compHom (movedModule (T : Subgroup G) M X) ρ
  exact ⟨quotientFactors M X (movedModule (T : Subgroup G) M X) P,
    hcard,hinj,hgen,hperm,hnS,hnlift,hswap⟩
end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
