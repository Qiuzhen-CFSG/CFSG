module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.CosetAction
public import Theory.SpecificGroups.SymplecticFour.BorelLocalCover
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.EndpointIndices
public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.GroupTheory.Amalgam.Reversal
public import Theory.Quasithin.EvenCharacteristic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Full marked comparison after symplectic recognition

A normal concrete symplectic subgroup of full Sylow-two order is the whole
source quotient, by the actual unipotent normal generation. Sylow conjugacy
then adjusts an ambient equivalence so that the original U maps to the
standard unipotent subgroup. Normalizers identify the full Borel. Local
characteristic two and maximality identify both parabolics, and their
distinctness gives exactly the two permitted orientations. The existing
amalgam-transport API restricts one equivalence to both endpoints and the
whole overlap, preserving both squares and the literal quotient map Q.q.
The projective transport uses the entire scalar center.

The ambient symplectic equivalence is an explicit input of this adapter.
This is not Higman recognition or a construction of a model homomorphism.
The geometric source theorem must construct it; q=2 is never replaced by
the derived alternating group.

Source: Fong–Seitz II (7C), p.193 and (8A), p.197; Aschbacher–Smith F.1.12,
pp.262–264. Sylow alignment and amalgam transport reuse the existing general
APIs; the characteristic-two Borel coverage includes the binary field.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

omit [CharP F 2] in
/-- Full Sylow order removes the ambient symplectic overgroup. -/
theorem normal_symplectic_eq_top
    (hgen : split.unipotentClosure = ⊤)
    (hU : Nat.card split.U = (Nat.card F)^4)
    (K : Subgroup (X ⧸ Q.D)) [K.Normal] (e : K ≃* Sp F) : K = ⊤ := by
  let V₀ := (unipotent (F := F)).map e.symm.toMonoidHom
  let V := V₀.map K.subtype
  have hcard : Nat.card V = Nat.card split.U := by
    rw [card_map_of_injective K.subtype_injective,
      card_map_of_injective e.symm.injective,card_unipotent,hU]
  exact normal_eq_top_of_full_order_subgroup Q split hgen K V (map_subtype_le _) hcard

omit [CharP F 2] in
/-- The resulting equivalence is on the whole original quotient. -/
def wholeEquiv (hgen : split.unipotentClosure = ⊤)
    (hU : Nat.card split.U = (Nat.card F)^4)
    (K : Subgroup (X ⧸ Q.D)) [K.Normal] (e : K ≃* Sp F) : (X ⧸ Q.D) ≃* Sp F :=
  (topEquiv.symm.trans (MulEquiv.subgroupCongr
    (normal_symplectic_eq_top Q split hgen hU K e).symm)).trans e

/-- Sylow conjugacy adjusts a group recognition to the actual source U. -/
theorem exists_unipotent_aligned (e : (X ⧸ Q.D) ≃* Sp F) :
    ∃ (g : Sp F) (e' : (X ⧸ Q.D) ≃* Sp F), e' = e.trans (MulAut.conj g) ∧
      split.U.map e'.toMonoidHom = unipotent (F := F) := by
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  exact SolvableSylowControl.exists_aligned_equiv e split.sylow (unipotentSylow hF n.property)

omit [Finite F] [CharP F 2] in
theorem map_borel_of_unipotent (e : (X ⧸ Q.D) ≃* Sp F)
    (hU : split.U.map e.toMonoidHom = unipotent (F := F)) :
    Q.tits.B.map e.toMonoidHom = borel (F := F) := by
  rw [← split.normalizer_eq,map_normalizer_eq_of_bijective _ e.bijective,
    hU,← borel_eq_normalizer_unipotent]

private theorem parabolics_ne :
    Q.tits.standardParabolic {Q.simple 0} ≠ Q.tits.standardParabolic {Q.simple 1} := by
  intro he
  have hs := (Q.tits.standardParabolic_eq_iff
    (Set.singleton_subset_iff.mpr (Q.simple_mem 0))
    (Set.singleton_subset_iff.mpr (Q.simple_mem 1))).mp he
  exact (by decide : (0 : Fin 2) ≠ 1) (Q.simple_injective (Set.singleton_injective hs))

variable (hc : ∀ i : Fin 2,
  centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
    Set (Q.tits.standardParabolic {Q.simple i})) ≤ pCore 2 (Q.tits.standardParabolic {Q.simple i}))

include hc in
theorem map_parabolic_of_borel (e : (X ⧸ Q.D) ≃* Sp F)
    (hB : Q.tits.B.map e.toMonoidHom = borel (F := F)) (i : Fin 2) :
    (Q.tits.standardParabolic {Q.simple i}).map e.toMonoidHom = pointParabolic (F := F) ∨
    (Q.tits.standardParabolic {Q.simple i}).map e.toMonoidHom = planeParabolic (F := F) := by
  let J := (Q.tits.standardParabolic {Q.simple i}).map e.toMonoidHom
  have hmax : IsCoatom J := (OrderIso.isCoatom_iff e.mapSubgroup _).mpr (Q.parabolic_isCoatom i)
  have hb : borel (F := F) ≤ J := hB ▸ map_mono (Q.tits.B_le_standardParabolic _)
  have hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap _)).mp (hc i)
  rcases borel_overgroup_parabolic_of_characteristicTwo J hb hchar with hp | hp
  · exact Or.inl (le_antisymm hp ((isCoatom_iff_ge_of_le.mp hmax).2 _ pointParabolic_ne_top hp))
  · exact Or.inr (le_antisymm hp ((isCoatom_iff_ge_of_le.mp hmax).2 _ planeParabolic_ne_top hp))

include hc in
/-- Both endpoints are recovered together, allowing exactly the two orientations. -/
theorem map_parabolics_of_borel (e : (X ⧸ Q.D) ≃* Sp F)
    (hB : Q.tits.B.map e.toMonoidHom = borel (F := F)) :
    ((Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = pointParabolic (F := F) ∧
      (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = planeParabolic (F := F)) ∨
    ((Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = planeParabolic (F := F) ∧
      (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = pointParabolic (F := F)) := by
  have hne : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom ≠
      (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom := by
    intro he
    exact parabolics_ne Q ((map_injective e.injective) he)
  rcases map_parabolic_of_borel Q hc e hB 0 with h0 | h0 <;>
    rcases map_parabolic_of_borel Q hc e hB 1 with h1 | h1
  · exact (hne (h0.trans h1.symm)).elim
  · exact Or.inl ⟨h0,h1⟩
  · exact Or.inr ⟨h0,h1⟩
  · exact (hne (h0.trans h1.symm)).elim

omit [Finite F] [CharP F 2] in
@[expose] def flagAmalgam (F : Type*) [Field F] :
    RankTwoAmalgam (pointParabolic (F := F)) (borel (F := F)) (planeParabolic (F := F)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

private def standardInclusionIso : RankTwoAmalgam.Iso Q.standardAmalgam
    (RankTwoAmalgam.ofSubgroups (Q.tits.standardParabolic {Q.simple 0}) Q.tits.B
      (Q.tits.standardParabolic {Q.simple 1}) (Q.tits.B_le_standardParabolic _)
      (Q.tits.B_le_standardParabolic _)) where
  left := MulEquiv.refl _
  middle := MulEquiv.refl _
  right := MulEquiv.refl _
  left_commutes b := by
    apply Subtype.ext
    change (Q.standardAmalgam.left b : X ⧸ Q.D) = b
    rw [RootCoordinates.standardAmalgam_left_eq_inclusion]
    rfl
  right_commutes b := by
    apply Subtype.ext
    change (Q.standardAmalgam.right b : X ⧸ Q.D) = b
    rw [RootCoordinates.standardAmalgam_right_eq_inclusion]
    rfl

omit [Finite F] [CharP F 2] in
def markedIso (e : (X ⧸ Q.D) ≃* Sp F)
    (hB : Q.tits.B.map e.toMonoidHom = borel (F := F))
    (h0 : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = pointParabolic (F := F))
    (h1 : (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = planeParabolic (F := F)) :
    RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam F) :=
  (standardInclusionIso Q).trans (RankTwoAmalgam.ofSubgroupsIso e (Q.tits.B_le_standardParabolic _)
    (Q.tits.B_le_standardParabolic _) inf_le_left inf_le_right h0 hB h1)

omit [Finite F] [CharP F 2] in
def reversedMarkedIso (e : (X ⧸ Q.D) ≃* Sp F)
    (hB : Q.tits.B.map e.toMonoidHom = borel (F := F))
    (h0 : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = planeParabolic (F := F))
    (h1 : (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = pointParabolic (F := F)) :
    RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam F).reverse :=
  (standardInclusionIso Q).trans (RankTwoAmalgam.ofSubgroupsIso e (Q.tits.B_le_standardParabolic _)
    (Q.tits.B_le_standardParabolic _) inf_le_right inf_le_left h0 hB h1)

section QuotientMaps
variable (e : (X ⧸ Q.D) ≃* Sp F)
  (hB : Q.tits.B.map e.toMonoidHom = borel (F := F))

omit [Finite F] [CharP F 2] in
/-- The same quotient projection gives both endpoint maps and the entire overlap. -/
def quotientMarkedIso
    (h0 : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = pointParabolic (F := F))
    (h1 : (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = planeParabolic (F := F)) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (flagAmalgam F) := Q.markedIso.trans (markedIso Q e hB h0 h1)

omit [Finite F] [CharP F 2] in
/-- Reversing the model orientation retains the original quotient projection. -/
def quotientReversedMarkedIso
    (h0 : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = planeParabolic (F := F))
    (h1 : (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = pointParabolic (F := F)) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (flagAmalgam F).reverse := Q.markedIso.trans (reversedMarkedIso Q e hB h0 h1)

omit [Finite F] [CharP F 2] in
theorem quotientMarkedIso_apply
    (h0 : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = pointParabolic (F := F))
    (h1 : (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = planeParabolic (F := F)) :
    (∀ a : P 0, ((quotientMarkedIso Q e hB h0 h1).left a : Sp F) = e (Q.q a)) ∧
    (∀ b : (P 0 ⊓ P 1 : Subgroup X),
      ((quotientMarkedIso Q e hB h0 h1).middle b : Sp F) = e (Q.q b)) ∧
    (∀ a : P 1, ((quotientMarkedIso Q e hB h0 h1).right a : Sp F) = e (Q.q a)) := by
  constructor
  · intro a
    change e (Q.markedIso.left a : X ⧸ Q.D) = _
    rw [Q.markedIso_left_apply]
  constructor
  · intro b
    change e (Q.markedIso.middle b : X ⧸ Q.D) = _
    rw [Q.markedIso_middle_apply]
  · intro a
    change e (Q.markedIso.right a : X ⧸ Q.D) = _
    rw [Q.markedIso_right_apply]

omit [Finite F] [CharP F 2] in
theorem quotientReversedMarkedIso_apply
    (h0 : (Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = planeParabolic (F := F))
    (h1 : (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = pointParabolic (F := F)) :
    (∀ a : P 0, ((quotientReversedMarkedIso Q e hB h0 h1).left a : Sp F) = e (Q.q a)) ∧
    (∀ b : (P 0 ⊓ P 1 : Subgroup X),
      ((quotientReversedMarkedIso Q e hB h0 h1).middle b : Sp F) = e (Q.q b)) ∧
    (∀ a : P 1, ((quotientReversedMarkedIso Q e hB h0 h1).right a : Sp F) = e (Q.q a)) := by
  constructor
  · intro a
    change e (Q.markedIso.left a : X ⧸ Q.D) = _
    rw [Q.markedIso_left_apply]
  constructor
  · intro b
    change e (Q.markedIso.middle b : X ⧸ Q.D) = _
    rw [Q.markedIso_middle_apply]
  · intro a
    change e (Q.markedIso.right a : X ⧸ Q.D) = _
    rw [Q.markedIso_right_apply]

omit [Finite F] in
/-- The entire scalar center is accounted for by the actual quotient map. -/
theorem projective_map (H : Subgroup (X ⧸ Q.D)) :
    H.map (e.trans EvenProjective.equiv).toMonoidHom =
      (H.map e.toMonoidHom).map (QuotientGroup.mk' (center (Sp F))) := by
  have he : (e.trans EvenProjective.equiv).toMonoidHom =
      (QuotientGroup.mk' (center (Sp F))).comp e.toMonoidHom := by
    ext g
    exact EvenProjective.equiv_apply _
  rw [he,Subgroup.map_map]
end QuotientMaps

include hc split in
/-- Recognition of the ambient group suffices for full marked recognition.
Constructing the ambient equivalence remains the geometric recognition step. -/
theorem marked_comparison_of_equiv (e : (X ⧸ Q.D) ≃* Sp F) :
    Nonempty (RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam F).reverse) := by
  obtain ⟨g,e',_,hU⟩ := exists_unipotent_aligned Q split e
  have hB := map_borel_of_unipotent Q split e' hU
  rcases map_parabolics_of_borel Q hc e' hB with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact Or.inl ⟨markedIso Q e' hB h0 h1⟩
  · exact Or.inr ⟨reversedMarkedIso Q e' hB h0 h1⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
