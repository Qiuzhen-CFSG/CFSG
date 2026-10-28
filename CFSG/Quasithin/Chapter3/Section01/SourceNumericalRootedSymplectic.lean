module
public import CFSG.Quasithin.Chapter3.Section01.SourceE213RecognizedPair
public import CFSG.Quasithin.Chapter3.Section01.SourceDualNumerical
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootRecognized

/-!
# The rooted symplectic obstruction to the original qrc cubic bound

The full minimal-parabolic core quotient retains the original module, simple
component and Sylow image. Sylow conjugacy aligns that same component with
its standard symplectic unipotent subgroup. The completed root-free E.2.7
recognition theorem now produces the literal marked pair required by E.2.13,
and the action bound transfers to the original M₀-module.

Thus the only remaining geometric alternative contains an actual root element
in the opposite pair of the original quotient image. Its field, component
inclusion, Sylow marking and strict image-size interval are all retained.
The second theorem also discharges the independent dual-FF branch using B.5.13.
Recognition of this root-containing pair remains a source obligation.

Source: Aschbacher--Smith E.2.7--13, pp.219--225, and 3.1.6--8, pp.573--576.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The remaining literal quotient pair, with an actual root element and the
original Sylow marking. No carrier-to-matrix identification is implicit. -/
@[expose] def QrcHypotheses.HasRootedSymplecticOutsideCoreModel
    (h : QrcHypotheses T M M₀ H V) : Prop :=
  ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤,
  ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧
    K ⊔ ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) = ⊤ ∧
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore (T.subtype h.right_mem.1.1.2) hp)
    let S := (T.subtype h.right_mem.1.1.2).mapSurjective
      (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore (T.subtype h.right_mem.1.1.2) hp))
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card F = 2^f ∧
    ∃ e : Sp F ≃* K.map q,
      (S : Subgroup (H ⧸ ChapterB.minimalParabolicCore (T.subtype h.right_mem.1.1.2) hp)).comap
        ((K.map q).subtype.comp e.toMonoidHom) = unipotent ∧
      2 < Nat.card ((V.subgroupOf H).map q) ∧
      Nat.card ((V.subgroupOf H).map q) < (2^f)^2 ∧
      ∃ x ∈ TwoConjugate.oppositePair
        (((V.subgroupOf H).map q).comap ((K.map q).subtype.comp e.toMonoidHom)),
        InvolutionTypes.IsRootElement x

/-- The root-free symplectic source branch bounds the original qrc action;
only the actual root-containing marked pair remains. -/
theorem QrcHypotheses.outsideCore_cubicRatio_le_two_or_rooted_symplectic_model
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hout : ¬ V ≤ H.pCoreIn 2) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      h.HasRootedSymplecticOutsideCoreModel := by
  let := h.module_elementary
  rcases h.outsideCore_cubicRatio_le_two_or_symplectic_middle_model hG hM hu hout with hb | hm
  · exact Or.inl hb
  obtain ⟨hp,K,hK,hN,hgen,f,hf,hm,hsmall,hlarge⟩ := hm
  let := hN
  obtain ⟨F,hF,hfin,hFcard,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hFcard
  let S := T.subtype h.right_mem.1.1.2
  let J := ChapterB.minimalParabolicCore S hp
  let B := ChapterB.minimalParabolicMax S hp
  let q := QuotientGroup.mk' J
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.subgroupOf H
  let Wq := W.map q
  let Kq := K.map q
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 Wq := IsElementaryAbelian.map q
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => h.module_le_sylow hx
  have hWqS : Wq ≤ (Sq : Subgroup (H ⧸ J)) := map_mono hWS
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := h.intrinsic_module_normalized
  have hTqW : (Sq : Subgroup (H ⧸ J)) ≤ normalizer (Wq : Set (H ⧸ J)) :=
    (map_mono hTV).trans (le_normalizer_map q)
  have hWcore : W ≤ B.pCoreIn 2 := h.intrinsic_module_le_maximal_core hG hM hp
  have hs : ¬ Group.IsSolvable H := by
    intro hsol
    let := hsol
    exact hK.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective K.subtype_injective)
  obtain ⟨hKs,_,hKn,hKT⟩ := ChapterE.Structure.source_normal_simple_image S hp hs K hK hgen
  let : IsSimpleGroup Kq := hKs
  let : Kq.Normal := hKn
  have hmin : ChapterB.IsMinimalParabolicOver Sq ⊤ :=
    (ChapterE.Structure.source_star_minimal_core_free S hp).1
  have hcore : ChapterB.minimalParabolicCore Sq hmin = ⊥ :=
    (ChapterE.Structure.source_star_minimal_core_free S hp).2
  have hmax : ChapterB.minimalParabolicMax Sq hmin = B.map q :=
    (ChapterB.minimalParabolicMax_map_core S hp q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWqcore : Wq ≤ (ChapterB.minimalParabolicMax Sq hmin).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hWcore).trans
      (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q B)
  let e₀ : Kq ≃* Sp F := e.trans EvenProjective.equiv.symm
  obtain ⟨c,hmark⟩ := ChapterE.Structure.SymplecticFour.exists_alignment hFcard
    (by omega : 1 ≤ f) Sq Kq e₀
  let e₁ : Sp F ≃* Kq := (e₀.trans (MulAut.conj c)).symm
  by_cases hr : ∃ x ∈ TwoConjugate.oppositePair (Wq.comap (Kq.subtype.comp e₁.toMonoidHom)),
      InvolutionTypes.IsRootElement x
  · exact Or.inr ⟨hp,K,hK,hN,hgen,F,hF,hfin,inferInstance,f,hf,hFcard,
      e₁,hmark,hsmall,hlarge,hr⟩
  apply Or.inl
  have hsq : IsSQTK KnownSimple.IsKnownSimple (H ⧸ J) :=
    ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
      (sqtk_of_mem_H hG h.right_mem.1.1.1) S hp hs
  have hrec := ChapterE.Structure.SymplecticFour.source_nonroot_hasRecognizedPair
    hFcard (by omega : 1 < f) hsq Sq hmin hcore Kq e₁ hmark hKT
    Wq hWqS hWqcore hTqW hsmall (by simpa only [not_exists,not_and] using hr)
  rw [hmax] at hrec
  exact h.cubicRatio_le_two_of_recognized_star hG hM hout hp hrec

/-- The entire original qrc numerical problem is reduced to the rooted pair.
The inside-core and dual-FF alternatives have no remaining premises. -/
theorem QrcHypotheses.cubicRatio_le_two_or_rooted_symplectic_model
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      h.HasRootedSymplecticOutsideCoreModel := by
  let := h.module_elementary
  rcases h.cubicRatio_le_two_or_source_branch hG hM hu hne with hb | hout | hdual
  · exact Or.inl hb
  · exact h.outsideCore_cubicRatio_le_two_or_rooted_symplectic_model hG hM hu hout
  · exact Or.inl (h.cubicRatio_le_two_of_literal_dualFF hG hM hu hdual)

end CFSG.Quasithin.Chapter3
