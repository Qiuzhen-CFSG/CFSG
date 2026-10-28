module

public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
public import Theory.Mathieu.M22.Properties.OuterHexadRadical
public import Theory.Mathieu.M22.Properties.PairHexadIncidence
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry

/-!
# Native M₂₂ plane and flag calculations

The full hexad-design stabilizer has order 11520, the full pair stabilizer in an
incident flag has order 3840, and the full flag intersection has order 768.
These are the literal stabilizers in the degree-22 design action.  Mapping them
through the faithful conjugation action on `MulAut M22` gives relative indices
15 and 5 for every incident pair–hexad flag.

The six-point map is the actual `M22OuterHexad.action`, transported through the
subgroup equivalence induced by `m22DesignAutToAut`; its range is all of
`Sym (Fin 6)` and its kernel is elementary abelian of order 16.  The quotient
map is retained for consumers of the plane overlap.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §4 and exposition (3.1),
pp. 16–17.  The native calculations use the checked M₂₂ design, pair–hexad
incidence, outer-hexad radical and automorphism-coverage modules.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound.Concrete
open scoped Pointwise

noncomputable def nativeInner : Subgroup m22DesignAut := M22.subgroupOf m22DesignAut

lemma native_inner_range :
    MonoidHom.range inclusion = nativeInner := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact h.property
  · intro hg
    exact ⟨⟨g.val, hg⟩, rfl⟩

lemma native_hex_inner :
    (MulAction.stabilizer m22DesignAut m22Hexad123) ⊓ nativeInner =
      m22HexadStabilizer.map inclusion := by
  rw [← native_inner_range, inf_comm]
  rw [← Subgroup.map_comap_eq inclusion (MulAction.stabilizer m22DesignAut m22Hexad123)]
  rfl

lemma native_pair_inner :
    (MulAction.stabilizer m22DesignAut m22Pair12) ⊓ nativeInner =
      m22PairStabilizer.map inclusion := by
  rw [← native_inner_range, inf_comm]
  rw [← Subgroup.map_comap_eq inclusion (MulAction.stabilizer m22DesignAut m22Pair12)]
  rfl

lemma native_outer_mem_hex :
    m22OuterDesignAut ∈ MulAction.stabilizer m22DesignAut m22Hexad123 := by
  rw [MulAction.mem_stabilizer_finset]
  intro a
  revert a
  decide +kernel

lemma native_outer_mem_pair :
    m22OuterDesignAut ∈ MulAction.stabilizer m22DesignAut m22Pair12 := by
  rw [MulAction.mem_stabilizer_finset]
  intro a
  revert a
  decide +kernel

lemma native_outer_not_inner : m22OuterDesignAut ∉ nativeInner := by
  intro h
  exact m22OddPairSwap_not_mem_M22 h

lemma native_index_two_of_outer (R : Subgroup m22DesignAut)
    (ho : m22OuterDesignAut ∈ R) :
    ((R ⊓ nativeInner).subgroupOf R).index = 2 := by
  apply (Subgroup.index_eq_two_iff_exists_notMem_and).2
  refine ⟨⟨m22OuterDesignAut, ho⟩, ?_, ?_⟩
  · intro h
    exact native_outer_not_inner h.2
  · intro b
    obtain ⟨h, hh | hh⟩ := m22DesignAut_normalForm b.1
    · right
      refine ⟨b.2, ?_⟩
      change (b.1 : Equiv.Perm (Fin 22)) ∈ M22
      rw [hh]
      exact h.2
    · left
      have he : b.1 * m22OuterDesignAut = M22ValueBound.Concrete.inclusion h := by
        apply Subtype.ext
        change (b.1 : Equiv.Perm (Fin 22)) * m22OddPairSwap = (h : Equiv.Perm (Fin 22))
        rw [hh, mul_assoc]
        have hs : m22OddPairSwap * m22OddPairSwap = (1 : Equiv.Perm (Fin 22)) := by
          decide +kernel
        rw [hs, mul_one]
      refine ⟨R.mul_mem b.2 ho, ?_⟩
      change b.1 * m22OuterDesignAut ∈ nativeInner
      rw [he]
      exact h.2

lemma native_card_of_outer (R : Subgroup m22DesignAut)
    {n : ℕ} (ho : m22OuterDesignAut ∈ R) (hc : Nat.card (R ⊓ nativeInner : Subgroup m22DesignAut) = n) :
    Nat.card R = 2 * n := by
  have hi := native_index_two_of_outer R ho
  have he : Nat.card ((R ⊓ nativeInner).subgroupOf R) = Nat.card (R ⊓ nativeInner : Subgroup m22DesignAut) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h := ((R ⊓ nativeInner).subgroupOf R).card_mul_index
  rw [he, hi, hc] at h
  omega

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups

namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound.Concrete
open scoped Pointwise

lemma native_hex_card_standard :
    Nat.card (MulAction.stabilizer m22DesignAut m22Hexad123) = 11520 := by
  have hc : Nat.card (((MulAction.stabilizer m22DesignAut m22Hexad123) ⊓ nativeInner : Subgroup m22DesignAut)) =
      Nat.card m22HexadStabilizer := by
    rw [native_hex_inner, card_map_of_injective inclusion_injective]
  have h := native_card_of_outer _ native_outer_mem_hex hc
  rw [m22HexadStabilizer_card] at h
  simpa using h

lemma native_pair_card_standard :
    Nat.card (MulAction.stabilizer m22DesignAut m22Pair12) = 3840 := by
  have hc : Nat.card (((MulAction.stabilizer m22DesignAut m22Pair12) ⊓ nativeInner : Subgroup m22DesignAut)) =
      Nat.card m22PairStabilizer := by
    rw [native_pair_inner, card_map_of_injective inclusion_injective]
  have h := native_card_of_outer _ native_outer_mem_pair hc
  rw [m22PairStabilizer_card] at h
  simpa using h

lemma native_inter_card_standard :
    Nat.card (((MulAction.stabilizer m22DesignAut m22Hexad123) ⊓
      MulAction.stabilizer m22DesignAut m22Pair12 : Subgroup m22DesignAut)) = 768 := by
  let R : Subgroup m22DesignAut := (MulAction.stabilizer m22DesignAut m22Hexad123) ⊓
      MulAction.stabilizer m22DesignAut m22Pair12
  have ho : m22OuterDesignAut ∈ R := ⟨native_outer_mem_hex, native_outer_mem_pair⟩
  have hI : R ⊓ nativeInner =
      M22SolvableSylow.pairHexad.map inclusion := by
    calc
      R ⊓ nativeInner =
          ((MulAction.stabilizer m22DesignAut m22Hexad123) ⊓ nativeInner) ⊓
            ((MulAction.stabilizer m22DesignAut m22Pair12) ⊓ nativeInner) := by
              simp [R, inf_assoc, inf_left_comm, inf_comm]
      _ = m22HexadStabilizer.map inclusion ⊓ m22PairStabilizer.map inclusion := by
            rw [native_hex_inner, native_pair_inner]
      _ = (m22HexadStabilizer ⊓ m22PairStabilizer).map inclusion :=
            (map_inf _ _ _ inclusion_injective).symm
      _ = M22SolvableSylow.pairHexad.map inclusion := rfl
  have hc : Nat.card (R ⊓ nativeInner : Subgroup m22DesignAut) = 384 := by
    rw [hI, card_map_of_injective inclusion_injective, M22SolvableSylow.pairHexad_card]
  exact native_card_of_outer R ho hc

lemma native_hex_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (MulAction.stabilizer m22DesignAut B) = 11520 := by
  obtain ⟨g, hg⟩ := exists_smul_m22Hexad123_eq hB
  let q : m22DesignAut := M22ValueBound.Concrete.inclusion g
  have he : q • m22Hexad123 = B := by
    exact hg
  have hs : MulAction.stabilizer m22DesignAut B =
      Subgroup.map (MulAut.conj q).toMonoidHom
        (MulAction.stabilizer m22DesignAut m22Hexad123) := by
    rw [← he, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [hs, card_map_of_injective (MulAut.conj q).injective]
  exact native_hex_card_standard

lemma native_pair_hex_card {A : Finset (Fin 22)} {B : Finset (Fin 22)}
    (hA : A.card = 2) (hB : B ∈ m22Blocks) (hAB : A ⊆ B) :
    Nat.card (MulAction.stabilizer m22DesignAut A) = 3840 := by
  obtain ⟨g, hgA, hgB⟩ := m22_pair_hexad_flag_conjugacy hA hB hAB
  let q : m22DesignAut := M22ValueBound.Concrete.inclusion g
  have heA : q • m22Pair12 = A := hgA
  have hs : MulAction.stabilizer m22DesignAut A =
      Subgroup.map (MulAut.conj q).toMonoidHom
        (MulAction.stabilizer m22DesignAut m22Pair12) := by
    rw [← heA, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [hs, card_map_of_injective (MulAut.conj q).injective]
  exact native_pair_card_standard

lemma native_inter_card {A : Finset (Fin 22)} {B : Finset (Fin 22)}
    (hA : A.card = 2) (hB : B ∈ m22Blocks) (hAB : A ⊆ B) :
    Nat.card (((MulAction.stabilizer m22DesignAut B) ⊓
      MulAction.stabilizer m22DesignAut A : Subgroup m22DesignAut)) = 768 := by
  obtain ⟨g, hgA, hgB⟩ := m22_pair_hexad_flag_conjugacy hA hB hAB
  let q : m22DesignAut := M22ValueBound.Concrete.inclusion g
  have heA : q • m22Pair12 = A := hgA
  have heB : q • m22Hexad123 = B := hgB
  have hs : (MulAction.stabilizer m22DesignAut B) ⊓
      MulAction.stabilizer m22DesignAut A =
      Subgroup.map (MulAut.conj q).toMonoidHom
        ((MulAction.stabilizer m22DesignAut m22Hexad123) ⊓
          MulAction.stabilizer m22DesignAut m22Pair12) := by
    rw [← heB, ← heA, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rw [← map_inf _ _ _ (MulAut.conj q).injective]
  rw [hs, card_map_of_injective (MulAut.conj q).injective]
  exact native_inter_card_standard

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups

namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound.Concrete
open scoped Pointwise

lemma native_design_hex_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (designStabilizer B) = 11520 := by
  rw [designStabilizer, card_map_of_injective m22DesignAutToAut_injective]
  exact native_hex_card hB

lemma native_design_pair_card {A : Finset (Fin 22)} {B : Finset (Fin 22)}
    (hA : A.card = 2) (hB : B ∈ m22Blocks) (hAB : A ⊆ B) :
    Nat.card (designStabilizer A) = 3840 := by
  rw [designStabilizer, card_map_of_injective m22DesignAutToAut_injective]
  exact native_pair_hex_card hA hB hAB

lemma native_design_inter_card {A : Finset (Fin 22)} {B : Finset (Fin 22)}
    (hA : A.card = 2) (hB : B ∈ m22Blocks) (hAB : A ⊆ B) :
    Nat.card (((designStabilizer B) ⊓ designStabilizer A : Subgroup (MulAut M22))) = 768 := by
  rw [designStabilizer, designStabilizer,
    ← map_inf _ _ _ m22DesignAutToAut_injective,
    card_map_of_injective m22DesignAutToAut_injective]
  exact native_inter_card hA hB hAB

lemma native_design_flag_indices {A : Finset (Fin 22)} {B : Finset (Fin 22)}
    (hA : A.card = 2) (hB : B ∈ m22Blocks) (hAB : A ⊆ B) :
    ((designStabilizer B) ⊓ designStabilizer A).relIndex (designStabilizer B) = 15 ∧
      ((designStabilizer B) ⊓ designStabilizer A).relIndex (designStabilizer A) = 5 := by
  have hBcard : Nat.card (designStabilizer B) = 11520 := native_design_hex_card hB
  have hAcard : Nat.card (designStabilizer A) = 3840 := native_design_pair_card hA hB hAB
  have hIcard : Nat.card (((designStabilizer B) ⊓ designStabilizer A :
      Subgroup (MulAut M22))) = 768 := native_design_inter_card hA hB hAB
  have hsubB : Nat.card (((designStabilizer B) ⊓ designStabilizer A).subgroupOf
      (designStabilizer B)) = 768 := by
    have he := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (G := MulAut M22) (H := (designStabilizer B) ⊓ designStabilizer A)
      (K := designStabilizer B) inf_le_left).toEquiv
    exact he.trans hIcard
  have hsubA : Nat.card (((designStabilizer B) ⊓ designStabilizer A).subgroupOf
      (designStabilizer A)) = 768 := by
    have he := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (G := MulAut M22) (H := (designStabilizer B) ⊓ designStabilizer A)
      (K := designStabilizer A) inf_le_right).toEquiv
    exact he.trans hIcard
  have hrelB := (((designStabilizer B) ⊓ designStabilizer A).subgroupOf
      (designStabilizer B)).card_mul_index
  have hrelA := (((designStabilizer B) ⊓ designStabilizer A).subgroupOf
      (designStabilizer A)).card_mul_index
  rw [hsubB, hBcard] at hrelB
  rw [hsubA, hAcard] at hrelA
  have hidxB : (((designStabilizer B) ⊓ designStabilizer A).subgroupOf
      (designStabilizer B)).index = 15 := by omega
  have hidxA : (((designStabilizer B) ⊓ designStabilizer A).subgroupOf
      (designStabilizer A)).index = 5 := by omega
  exact ⟨hidxB, hidxA⟩

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups

namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound.Concrete
open scoped Pointwise

noncomputable def nativePlaneStabilizerEquiv {B : Finset (Fin 22)} :
    MulAction.stabilizer m22DesignAut B ≃* designStabilizer B :=
  Subgroup.equivMapOfInjective _ m22DesignAutToAut m22DesignAutToAut_injective

noncomputable def nativePlaneAction {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    designStabilizer B →* Equiv.Perm (Fin 6) :=
  (M22OuterHexad.action hB).comp
    (nativePlaneStabilizerEquiv (B := B)).symm.toMonoidHom

private lemma native_outer_kernel_eq {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (M22OuterHexad.action hB).ker =
      ((m22HexadPointwiseKernel B).map inclusion).subgroupOf
        (MulAction.stabilizer m22DesignAut B) := by
  have hKle : (m22HexadPointwiseKernel B).map inclusion ≤
      MulAction.stabilizer m22DesignAut B := by
    rintro _ ⟨u, hu, rfl⟩
    have huB := m22HexadPointwiseKernel_le B hu
    rw [MulAction.mem_stabilizer_finset'] at huB ⊢
    intro a ha
    exact huB ha
  ext x
  change x ∈ (M22OuterHexad.action hB).ker ↔
    x.val ∈ ((m22HexadPointwiseKernel B).map inclusion : Subgroup m22DesignAut)
  constructor
  · intro hx
    rw [← M22OuterHexad.action_ker_map hB]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← M22OuterHexad.action_ker_map hB] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact (show y = x from Subtype.ext he) ▸ hy

private lemma native_outer_kernel_elementary {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (M22OuterHexad.action hB).ker := by
  rw [native_outer_kernel_eq hB]
  have hK0 : IsElementaryAbelian 2 (m22HexadPointwiseKernel B) :=
    m22HexadPointwiseKernel_elementaryAbelian hB
  have hK : IsElementaryAbelian 2 ((m22HexadPointwiseKernel B).map inclusion) :=
    @IsElementaryAbelian.map 2 _ _ _ _ _ _ hK0 inclusion
  have hle : (m22HexadPointwiseKernel B).map inclusion ≤
      MulAction.stabilizer m22DesignAut B := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have huB := m22HexadPointwiseKernel_le B hu
    rw [MulAction.mem_stabilizer_finset'] at huB ⊢
    intro a ha
    exact huB ha
  exact @IsElementaryAbelian.of_surjective 2 _ _ _ _ hK
    ((Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.surjective

private lemma native_outer_kernel_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (M22OuterHexad.action hB).ker = 16 := by
  rw [native_outer_kernel_eq hB]
  have hle : (m22HexadPointwiseKernel B).map inclusion ≤
      MulAction.stabilizer m22DesignAut B := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have huB := m22HexadPointwiseKernel_le B hu
    rw [MulAction.mem_stabilizer_finset'] at huB ⊢
    intro a ha
    exact huB ha
  calc
    Nat.card (((m22HexadPointwiseKernel B).map inclusion).subgroupOf
      (MulAction.stabilizer m22DesignAut B)) =
        Nat.card ((m22HexadPointwiseKernel B).map inclusion) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    _ = Nat.card (m22HexadPointwiseKernel B) :=
      card_map_of_injective inclusion_injective
    _ = 16 := m22HexadPointwiseKernel_card hB

private lemma native_outer_action_surjective {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Surjective (M22OuterHexad.action hB) := by
  have hk := native_outer_kernel_card hB
  have hc := native_hex_card hB
  have hi := (M22OuterHexad.action hB).ker.card_mul_index
  rw [hk, hc] at hi
  have hr : Nat.card (M22OuterHexad.action hB).range = 720 := by
    rw [← Subgroup.index_ker]
    omega
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [hr]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

lemma native_plane_action_surjective {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Surjective (nativePlaneAction hB) := by
  exact (native_outer_action_surjective hB).comp
    (nativePlaneStabilizerEquiv (B := B)).symm.surjective

lemma native_plane_action_kernel_elementary {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (nativePlaneAction hB).ker := by
  have hk : (nativePlaneAction hB).ker =
      (M22OuterHexad.action hB).ker.map
        (nativePlaneStabilizerEquiv (B := B)).toMonoidHom := by
    dsimp [nativePlaneAction]
    exact MonoidHom.ker_comp_mulEquiv (M22OuterHexad.action hB)
      (nativePlaneStabilizerEquiv (B := B)).symm
  rw [hk]
  exact @IsElementaryAbelian.map 2 _ _ _ _ _ _ (native_outer_kernel_elementary hB)
    (nativePlaneStabilizerEquiv (B := B)).toMonoidHom

lemma native_plane_action_kernel_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Nat.card (nativePlaneAction hB).ker = 16 := by
  have hk : (nativePlaneAction hB).ker =
      (M22OuterHexad.action hB).ker.map
        (nativePlaneStabilizerEquiv (B := B)).toMonoidHom := by
    dsimp [nativePlaneAction]
    exact MonoidHom.ker_comp_mulEquiv (M22OuterHexad.action hB)
      (nativePlaneStabilizerEquiv (B := B)).symm
  rw [hk, card_map_of_injective (nativePlaneStabilizerEquiv (B := B)).injective]
  exact native_outer_kernel_card hB

noncomputable def nativePlaneQuotientEquiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (designStabilizer B ⧸ (nativePlaneAction hB).ker) ≃* Equiv.Perm (Fin 6) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (native_plane_action_surjective hB)

theorem nativePlanePointModel {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    IsElementaryAbelian 2 (nativePlaneAction hB).ker ∧
    Nat.card (nativePlaneAction hB).ker = 16 ∧
    Nonempty ((designStabilizer B ⧸ (nativePlaneAction hB).ker) ≃*
      Equiv.Perm (Fin 6)) :=
  ⟨native_plane_action_kernel_elementary hB,
    native_plane_action_kernel_card hB,
    ⟨nativePlaneQuotientEquiv hB⟩⟩

@[simp] theorem nativePlaneQuotientEquiv_mk {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : designStabilizer B) :
    nativePlaneQuotientEquiv hB (QuotientGroup.mk g) = nativePlaneAction hB g := rfl

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups


namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
open Subgroup Sporadic.Mathieu
open scoped Pointwise

/-- The point overlap quotient, instantiated with the native hexad model. -/
noncomputable def PointData.planeQuotientEquiv_native {G : Type*} [Group G] [Finite G]
    {z : G} (P : PointData z) (h : IsTypeJ4 z) :=
  P.planeQuotientEquiv h

theorem PointData.nativePlaneModel {G : Type*} [Group G] [Finite G]
    {z : G} (P : PointData z) (h : IsTypeJ4 z) :
    Nonempty ((P.M.subgroupOf (centralizer z) ⧸
      (twoThreeCore (centralizer z)).subgroupOf (P.M.subgroupOf (centralizer z))) ≃*
        designStabilizer P.hexad) ∧
    IsElementaryAbelian 2 (nativePlaneAction P.hexad_mem).ker ∧
    Nat.card (nativePlaneAction P.hexad_mem).ker = 16 ∧
    Nonempty ((designStabilizer P.hexad ⧸
      (nativePlaneAction P.hexad_mem).ker) ≃* Equiv.Perm (Fin 6)) := by
  exact ⟨⟨P.planeQuotientEquiv h⟩, nativePlanePointModel P.hexad_mem⟩

/-- The native flag indices discharge the model premises in the ambient transfer. -/
theorem tripleIndices_native {G : Type*} [Group G] [Finite G] {z : G}
    {P : PointData z} (L : LineData z P) (_h : IsTypeJ4 z) :
    (P.M ⊓ L.G₂ ⊓ centralizer z).relIndex (P.M ⊓ centralizer z) = 15 ∧
      (P.M ⊓ L.G₂ ⊓ centralizer z).relIndex (L.G₂ ⊓ centralizer z) = 5 := by
  have hi := native_design_flag_indices L.pair_card P.hexad_mem L.pair_le_hexad
  exact tripleIndices L hi.1 hi.2

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups
