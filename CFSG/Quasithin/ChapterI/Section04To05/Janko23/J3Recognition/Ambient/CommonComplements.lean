module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.FieldOverlap

/-!
# A common complement in the two actual plane normalizers

Choose a Sylow three-subgroup S of the whole order-576 overlap. Its order
is nine. Sylow conjugacy in each order-2880 plane normalizer moves a split
complement to contain this same S, without changing the plane marking.

The two resulting ambient complements intersect in exactly S. Indeed a
common element in R has square in E, hence square one by disjointness
from the first plane; every involution in R belongs to one of the two
planes, so that common element is trivial. Multiplication by R bounds
the intersection's order by nine. Thus R and S also split the whole
overlap. Both natural action equations and their agreed E coordinates
are retained when rebuilding the field-affine embeddings.

This establishes a shared actual complement on the overlap. It does not
supply the opposite-root/Weyl relations for PSL₂(16), ambient generation,
or the remaining presentation coordinate identity.

Sources: Aschbacher, *Sporadic Groups* (1994), 46.14(1–5a), pp.257–258;
Aschbacher–Smith I.4.7(2), p.418. The complement alignment uses Sylow
conjugacy and the previously proved root and natural-action calculations.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient

private theorem complement_containing_nine {H : Type*} [Group H] [Finite H]
    (V C S : Subgroup H) [V.Normal]
    (hC : V.IsComplement' C) (hc : Nat.card C = 180)
    (hH : Nat.card H = 2880) (hS : Nat.card S = 9) :
    ∃ C' : Subgroup H, V.IsComplement' C' ∧ S ≤ C' := by
  let Q : Sylow 3 C := Classical.choice inferInstance
  have hQ : Nat.card Q = 9 := by
    rw [Q.card_eq_multiplicity, hc]
    decide +kernel
  let B := (Q : Subgroup C).map C.subtype
  have hB : Nat.card B = 9 := (card_map_of_injective C.subtype_injective).trans hQ
  let P : Sylow 3 H := Sylow.ofCard B (by rw [hB,hH]; decide +kernel)
  let P' : Sylow 3 H := Sylow.ofCard S (by rw [hS,hH]; decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P P'
  let C' := C.map (MulAut.conj g).toMonoidHom
  have hvg : V.map (MulAut.conj g).toMonoidHom = V := Subgroup.Normal.map_conj_eq V g
  have hd : Disjoint V C' := by
    apply disjoint_iff.mpr
    rw [←hvg, ←map_inf _ _ _ (MulAut.conj g).injective, hC.disjoint.eq_bot, Subgroup.map_bot]
  refine ⟨C',isComplement'_of_card_mul_and_disjoint ?_ hd,?_⟩
  · rw [card_map_of_injective (MulAut.conj g).injective]
    exact hC.card_mul_card
  · have he : B.map (MulAut.conj g).toMonoidHom = S := by
      exact congrArg (fun R : Sylow 3 H => (R : Subgroup H)) hg
    rw [←he]
    exact map_mono (map_subtype_le _)


open LocalSixteen Representation.CentralCubicNaturalFour
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem marked_complement_containing (P : ReturningPair D)
    (hclass : OneInvolutionClass G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (S : Subgroup G) (hSN : S ≤ normalizer (A : Set G)) (hS : Nat.card S = 9)
    (f : A.normalizerMonoidHom.range ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ n x, a (n • x) = naturalAction (f n) (a x)) :
    ∃ (C : Subgroup (normalizer (A : Set G))) (l : C ≃* LinearGroup),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
      S ≤ C.map (normalizer (A : Set G)).subtype ∧
      (∀ (c : C) (x : A),
        a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x)) := by
  obtain ⟨C₀,hC₀⟩ := P.plane_normalizer_splits hclass A hA hAR
  obtain ⟨C,hC,hSC⟩ := complement_containing_nine
    (A.subgroupOf (normalizer (A : Set G))) C₀ (S.subgroupOf (normalizer (A : Set G)))
    hC₀ (P.plane_complement_card hclass A hA hAR C₀ hC₀)
    (P.plane_normalizer_card hclass A hA hAR)
    ((Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv).trans hS)
  let k := A.normalizerMonoidHom.rangeRestrict.comp C.subtype
  have hi : Function.Injective k := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro c hc
    apply mem_bot.mpr
    apply Subtype.ext
    apply hC.disjoint.le_bot
    refine ⟨?_,c.property⟩
    rw [←P.plane_normalizer_action_kernel A hA hAR]
    exact congrArg Subtype.val hc
  have hs : Function.Surjective k :=
    (Nat.bijective_iff_injective_and_card k).mpr
      ⟨hi,(P.plane_complement_card hclass A hA hAR C hC).trans
        (P.plane_normalizer_action_card hclass A hA hAR).symm⟩ |>.2
  refine ⟨C,(MulEquiv.ofBijective k ⟨hi,hs⟩).trans f,hC,?_,?_⟩
  · have hh := map_mono (f := (normalizer (A : Set G)).subtype) hSC
    rwa [map_subgroupOf_eq_of_le hSN] at hh
  · intro c x
    exact ha (k c) x


omit [Finite G] in
private theorem ambient_complement_disjoint (A : Subgroup G)
    (C : Subgroup (normalizer (A : Set G)))
    (hc : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C) :
    Disjoint A (C.map (normalizer (A : Set G)).subtype) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  rintro x ⟨ha, c, hc', rfl⟩
  have hh : c = 1 := mem_bot.mp (hc.disjoint.le_bot ⟨ha,hc'⟩)
  exact mem_bot.mpr (congrArg Subtype.val hh)

private theorem common_complement_card_bound (P : ReturningPair D)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root)
    (L : Subgroup G)
    (hLO : L ≤ normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G))
    (hd₁ : Disjoint (P.A₁ eR) L) (hd₂ : Disjoint (P.A₂ eR) L) : Nat.card L ≤ 9 := by
  have hd : Disjoint P.R L := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    have hs : x ^ 2 = 1 := mem_bot.mp (hd₁.le_bot
      ⟨P.E_le_plane _ (P.A₁_card eR) (P.A₁_le_R eR) (P.R_square_mem_E hx.1),
        L.pow_mem hx.2 2⟩)
    rcases root_involution_in_planes P eR x hx.1 hs with h | h
    · exact hd₁.le_bot ⟨h,hx.2⟩
    · exact hd₂.le_bot ⟨h,hx.2⟩
  let O := normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G)
  have hRO : P.R ≤ O := le_inf
    (P.R_le_plane_normalizer _ (P.A₁_card eR) (P.A₁_le_R eR))
    (P.R_le_plane_normalizer _ (P.A₂_card eR) (P.A₂_le_R eR))
  let m : P.R × L → O := fun r => ⟨(r.1 : G) * (r.2 : G),
    O.mul_mem (hRO r.1.property) (hLO r.2.property)⟩
  have hi : Function.Injective m := by
    intro r s h
    exact mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hh := Nat.card_le_card_of_injective m hi
  rw [Nat.card_prod, P.R_card, overlap_card P eR] at hh
  omega

/-- Both natural plane complements can contain the same order-nine subgroup.
Their full ambient intersection is exactly that subgroup, and it complements
R in the actual whole overlap. The plane coordinates agree on the original E. -/
theorem compatible_plane_complements (P : ReturningPair D) (hclass : OneInvolutionClass G)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    ∃ (S : Subgroup G)
      (C₁ : Subgroup (normalizer (P.A₁ eR : Set G)))
      (f₁ : C₁ ≃* LinearGroup) (a₁ : P.A₁ eR ≃* Plane)
      (C₂ : Subgroup (normalizer (P.A₂ eR : Set G)))
      (f₂ : C₂ ≃* LinearGroup) (a₂ : P.A₂ eR ≃* Plane),
      Nat.card S = 9 ∧
      Disjoint P.R S ∧
      P.R ⊔ S = normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G) ∧
      ((P.A₁ eR).subgroupOf (normalizer (P.A₁ eR : Set G))).IsComplement' C₁ ∧
      (∀ (c : C₁) (x : P.A₁ eR),
        a₁ ((P.A₁ eR).normalizerMonoidHom c x) = naturalAction (f₁ c) (a₁ x)) ∧
      ((P.A₂ eR).subgroupOf (normalizer (P.A₂ eR : Set G))).IsComplement' C₂ ∧
      (∀ (c : C₂) (x : P.A₂ eR),
        a₂ ((P.A₂ eR).normalizerMonoidHom c x) = naturalAction (f₂ c) (a₂ x)) ∧
      C₁.map (normalizer (P.A₁ eR : Set G)).subtype ⊓
        C₂.map (normalizer (P.A₂ eR : Set G)).subtype = S ∧
      (∀ (x : G) (hx₁ : x ∈ P.A₁ eR) (hx₂ : x ∈ P.A₂ eR),
        a₁ ⟨x,hx₁⟩ = a₂ ⟨x,hx₂⟩) ∧
      (∀ x : P.E,
        (a₁ ⟨x,((P.planes_inf eR).ge.trans inf_le_left) x.property⟩).toAdd 1 = 0) := by
  let O := normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G)
  have hRO : P.R ≤ O := le_inf
    (P.R_le_plane_normalizer _ (P.A₁_card eR) (P.A₁_le_R eR))
    (P.R_le_plane_normalizer _ (P.A₂_card eR) (P.A₂_le_R eR))
  let Q : Sylow 3 O := Classical.choice inferInstance
  have hQ : Nat.card Q = 9 := by
    rw [Q.card_eq_multiplicity, overlap_card P eR]
    decide +kernel
  let S := (Q : Subgroup O).map O.subtype
  have hS : Nat.card S = 9 := (card_map_of_injective O.subtype_injective).trans hQ
  have hSO : S ≤ O := map_subtype_le _
  have hRS : Disjoint P.R S := disjoint_of_coprime_natCard (by rw [P.R_card,hS]; decide)
  have hsup : P.R ⊔ S = O := by
    have hR : Nat.card (P.R.subgroupOf O) = 64 :=
      (Nat.card_congr (subgroupOfEquivOfLe hRO).toEquiv).trans P.R_card
    have hc : (P.R.subgroupOf O).IsComplement' (Q : Subgroup O) :=
      isComplement'_of_coprime (by rw [hR,hQ,overlap_card P eR])
        (by rw [hR,hQ]; decide)
    have hh := congrArg (Subgroup.map O.subtype) hc.sup_eq_top
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hRO, ←MonoidHom.range_eq_map, O.range_subtype] at hh
  obtain ⟨k₁,a₁,k₂,a₂,ha₁,ha₂,heq,_,hl⟩ := compatible_automizer_markings P hclass eR
  obtain ⟨C₁,f₁,hC₁,hS₁,hf₁⟩ := marked_complement_containing P hclass _
    (P.A₁_card eR) (P.A₁_le_R eR) S (hSO.trans inf_le_left) hS k₁ a₁ ha₁
  obtain ⟨C₂,f₂,hC₂,hS₂,hf₂⟩ := marked_complement_containing P hclass _
    (P.A₂_card eR) (P.A₂_le_R eR) S (hSO.trans inf_le_right) hS k₂ a₂ ha₂
  let L := C₁.map (normalizer (P.A₁ eR : Set G)).subtype ⊓
    C₂.map (normalizer (P.A₂ eR : Set G)).subtype
  have hL : Nat.card L ≤ 9 := common_complement_card_bound P eR L
    (inf_le_inf (map_subtype_le _) (map_subtype_le _))
    ((ambient_complement_disjoint _ C₁ hC₁).mono_right inf_le_left)
    ((ambient_complement_disjoint _ C₂ hC₂).mono_right inf_le_right)
  have he : L = S := (eq_of_le_of_card_ge (le_inf hS₁ hS₂) (hS ▸ hL)).symm
  exact ⟨S,C₁,f₁,a₁,C₂,f₂,a₂,hS,hRS,hsup,hC₁,hf₁,hC₂,hf₂,he,heq,hl⟩


open Sporadic.Janko3.SourceRecognition.PlaneCoordinates
open Sporadic.Janko3.SourceRecognition.PlaneTransport

/-- Actual field subgroups whose parent natural complements coincide on the
same Hall subgroup of the whole overlap. All field and translation markings
are retained, including the common base-field map and crossing involutions. -/
theorem compatible_fields_with_common_complement
    (P : ReturningPair D) (hclass : OneInvolutionClass G)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    ∃ (S : Subgroup G)
      (C₁ : Subgroup (normalizer (P.A₁ eR : Set G)))
      (f₁ : C₁ ≃* LinearGroup) (a₁ : P.A₁ eR ≃* Plane)
      (j₁ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G)
      (C₂ : Subgroup (normalizer (P.A₂ eR : Set G)))
      (f₂ : C₂ ≃* LinearGroup) (a₂ : P.A₂ eR ≃* Plane)
      (j₂ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G),
      Nat.card S = 9 ∧
      Disjoint P.R S ∧
      P.R ⊔ S = normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G) ∧
      ((P.A₁ eR).subgroupOf (normalizer (P.A₁ eR : Set G))).IsComplement' C₁ ∧
      (∀ (c : C₁) (x : P.A₁ eR),
        a₁ ((P.A₁ eR).normalizerMonoidHom c x) = naturalAction (f₁ c) (a₁ x)) ∧
      FieldEmbedding (P.A₁ eR) C₁ a₁ j₁ ∧
      ((P.A₂ eR).subgroupOf (normalizer (P.A₂ eR : Set G))).IsComplement' C₂ ∧
      (∀ (c : C₂) (x : P.A₂ eR),
        a₂ ((P.A₂ eR).normalizerMonoidHom c x) = naturalAction (f₂ c) (a₂ x)) ∧
      FieldEmbedding (P.A₂ eR) C₂ a₂ j₂ ∧
      C₁.map (normalizer (P.A₁ eR : Set G)).subtype ⊓
        C₂.map (normalizer (P.A₂ eR : Set G)).subtype = S ∧
      (∀ (x : G) (hx₁ : x ∈ P.A₁ eR) (hx₂ : x ∈ P.A₂ eR),
        a₁ ⟨x,hx₁⟩ = a₂ ⟨x,hx₂⟩) ∧
      j₁.comp baseRoot = j₂.comp baseRoot ∧ (j₁.comp baseRoot).range = P.E ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₂ eR ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₂ eR := by
  obtain ⟨S,C₁,f₁,a₁,C₂,f₂,a₂,hS,hRS,hsup,hC₁,hf₁,hC₂,hf₂,hmeet,heq,hl⟩ :=
    compatible_plane_complements P hclass eR
  obtain ⟨j₁,hj₁⟩ := field_embedding_of_complement _ C₁ f₁ a₁ hC₁ hf₁
  obtain ⟨j₂,hj₂⟩ := field_embedding_of_complement _ C₂ f₂ a₂ hC₂ hf₂
  exact ⟨S,C₁,f₁,a₁,j₁,C₂,f₂,a₂,j₂,hS,hRS,hsup,hC₁,hf₁,hj₁,hC₂,hf₂,hj₂,hmeet,heq,
    field_overlap_of_markings P eR C₁ a₁ j₁ C₂ a₂ j₂ hC₁ hj₁ hC₂ hj₂ heq hl⟩

end CFSG.Quasithin.Janko23.J3Recognition.Ambient
