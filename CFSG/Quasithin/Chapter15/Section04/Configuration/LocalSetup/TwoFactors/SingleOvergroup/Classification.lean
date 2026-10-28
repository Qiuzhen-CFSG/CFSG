module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.ModelExclusions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.AutM12Center
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.DerivedG2Center
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The F.6.5 case inspection used in 15.4.15

The classification input below is the core-free specialization of F.6.5(2–3).
It is an explicit universal implication, not a theorem asserted in this module.
It retains all eleven alternatives: the three actual group isomorphisms in
(i–v), including the relative extension in (iv), and compatible amalgam
isomorphisms to the six concrete geometric models in (vi). The two orientations
are allowed. The non-two-group Fitting assertion is precisely F.6.5(3).

Characteristic two excludes (i–v). Actual omega-center calculations exclude
PSL₃(2), G₂(2), G₂(2)′, M₁₂ and Aut(M₁₂). The symplectic alternative then gives
both C₂ × S₄ identifications by the proved matrix equivalences. In particular
neither this identification nor impossibility of a Chapter 15 branch is part
of the classification input. This inspection uses the stronger concrete
omega-center calculations; order four alone suffices in the six binary cases.

The general F.6 owner must instantiate the universal classification input.
No classification or existence of a named model is proved by these definitions.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.5, p.305;
F.1.12(1–3,8,12–13), pp.262–263; 15.4.15, p.1161.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup

universe u
variable {G : Type u} [Group G]

/-- The source inclusion amalgam, with its whole intersection. -/
def inclusionAmalgam (A B : Subgroup G) : RankTwoAmalgam A (A ⊓ B : Subgroup G) B :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Actual group identifications of all three entries in a displayed triple. -/
def HasTripleTypes (A B : Subgroup G) (L D R : Type*)
    [Group L] [Group D] [Group R] : Prop :=
  Nonempty (A ≃* L) ∧ Nonempty ((A ⊓ B : Subgroup G) ≃* D) ∧ Nonempty (B ≃* R)

/-- The five displayed small triples in F.6.5(2). In (iv), the slash describes
an extension: the normal subgroup is inside the right generator. -/
inductive SmallAlternative (A B : Subgroup G) : Prop
  | i (iso : HasTripleTypes A B (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 2)) (Equiv.Perm (Fin 3)))
  | ii (iso : HasTripleTypes A B (DihedralGroup 6)
      (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) (DihedralGroup 6))
  | iii (iso : HasTripleTypes A B (DihedralGroup 12)
      (DihedralGroup 4) (Equiv.Perm (Fin 4)))
  | iv (left : Nonempty (A ≃* Equiv.Perm (Fin 4)))
      (middle : Nonempty ((A ⊓ B : Subgroup G) ≃* DihedralGroup 4))
      (extension : ∃ N : Subgroup B, ∃ _ : N.Normal,
        Nonempty (N ≃* (Multiplicative (ZMod 3) ×
          (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)))) ∧
        Nonempty ((B ⧸ N) ≃* Equiv.Perm (Fin 2)))
  | v (iso : HasTripleTypes A B (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))
      (Equiv.Perm (Fin 2) × DihedralGroup 4) (Equiv.Perm (Fin 3) × DihedralGroup 4))

/-- The actual positive-root inclusion amalgam in G₂(2). -/
def binaryG2Amalgam :=
  RankTwoAmalgam.ofSubgroups Atlas.G2.BinaryParabolicPair.firstParabolic
    (Atlas.G2.unipotent (K := ZMod 2)) Atlas.G2.BinaryCore.secondParabolic
    (Atlas.G2.BinaryParabolicPair.parabolic_intersection ▸ inf_le_left)
    (Atlas.G2.BinaryParabolicPair.parabolic_intersection ▸ inf_le_right)

/-- Its restriction to the actual commutator subgroup; all three groups are
still embedded in the same split-octonion carrier. -/
def derivedG2Amalgam :=
  RankTwoAmalgam.ofSubgroups Atlas.G2.BinaryParabolicPair.derivedFirstAmbient
    Atlas.G2.BinaryParabolicPair.derivedSylowAmbient
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient
    (Atlas.G2.BinaryParabolicPair.derived_parabolic_intersection ▸ inf_le_left)
    (Atlas.G2.BinaryParabolicPair.derived_parabolic_intersection ▸ inf_le_right)

/-- The two actual Witt-design parabolics and their whole overlap. -/
def m12Amalgam :=
  inclusionAmalgam Sporadic.Mathieu.M12SmallPair.firstParabolic
    Sporadic.Mathieu.M12SmallPair.secondParabolic

/-- The involution centralizer in the actual full automorphism group. -/
def autM12First : Subgroup (MulAut Sporadic.Mathieu.M12) :=
  centralizer ({MulAut.conj Sporadic.Mathieu.M12SmallPair.z} : Set _)

/-- The normalizer of the marked four-group in the same automorphism group. -/
def autM12Second : Subgroup (MulAut Sporadic.Mathieu.M12) :=
  normalizer (Sporadic.Mathieu.M12SmallPair.natural.map MulAut.conj : Set _)

/-- The six binary geometric alternatives of F.6.5(vi), retaining actual
compatible isomorphisms. The Aut(M₁₂) alternative includes its actual Sylow
marking; no printed, inconsistent core description is used. -/
inductive GeometricAlternative (A B : Subgroup G) : Prop
  | linear (iso : Nonempty (RankTwoAmalgam.Iso (inclusionAmalgam A B)
      ChapterF.GreenBook.LieModels.BinaryLinear.amalgam))
  | symplectic (iso : Nonempty (RankTwoAmalgam.Iso (inclusionAmalgam A B)
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam (ZMod 2))))
  | g2 (iso : Nonempty (RankTwoAmalgam.Iso (inclusionAmalgam A B) binaryG2Amalgam))
  | derived_g2 (iso : Nonempty (RankTwoAmalgam.Iso (inclusionAmalgam A B) derivedG2Amalgam))
  | m12 (iso : Nonempty (RankTwoAmalgam.Iso (inclusionAmalgam A B) m12Amalgam))
  | aut_m12 (P : Sylow 2 (MulAut Sporadic.Mathieu.M12))
      (overlap : autM12First ⊓ autM12Second = (P : Subgroup _))
      (iso : Nonempty (RankTwoAmalgam.Iso (inclusionAmalgam A B)
        (inclusionAmalgam autM12First autM12Second)))

/-- F.6.5(2–3)'s alternatives in one orientation. The Fitting clause is a
source conclusion valid independently of Chapter 15, not a branch exclusion
postulated for its application. -/
def OrientedAlternative (A B : Subgroup G) : Prop :=
  (SmallAlternative A B ∧
    (¬ IsPGroup 2 (generalizedFitting A) ∨ ¬ IsPGroup 2 (generalizedFitting B))) ∨
  GeometricAlternative A B

/-- The authorized universal classification input. All F.6.1 hypotheses and
the trivial two-core required for a Goldschmidt amalgam are explicit. Since
15.4.12 supplies the trivial core before applying F.6.5, no quotient
identifications are required in this core-free specialization. -/
def GoldschmidtClassification : Prop :=
  ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
    ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ →
      OrientedAlternative A B ∨ OrientedAlternative B A

/-- Inspect all six geometric alternatives. The actual center order four
forces the symplectic case and constructs both required group equivalences. -/
theorem geometric_identification {A B : Subgroup G}
    (h : GeometricAlternative A B)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (A ⊓ B)) = 4) :
    Nonempty (A ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) ∧
      Nonempty (B ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) := by
  cases h with
  | linear iso =>
    exact (not_linear_binary_overlap _ hZ (iso.map fun e => e.middle)).elim
  | symplectic iso =>
    obtain ⟨e⟩ := iso
    have hF : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card]
    exact ⟨⟨symplectic_point_identification hF e.left⟩,
      ⟨symplectic_plane_identification hF e.right⟩⟩
  | g2 iso =>
    exact (not_g2_binary_overlap _ hZ (iso.map fun e => e.middle)).elim
  | derived_g2 iso =>
    obtain ⟨e⟩ := iso
    have he := omega_center_card_eq_of_equiv (A ⊓ B)
      Atlas.G2.BinaryParabolicPair.derivedSylowAmbient e.middle
    have hc := g2_derived_omega_center_card
    omega
  | m12 iso =>
    exact (not_m12_overlap _ hZ (iso.map fun e => e.middle)).elim
  | aut_m12 P overlap iso =>
    obtain ⟨e⟩ := iso
    exact (not_autm12_overlap _ hZ P
      ⟨e.middle.trans (MulEquiv.subgroupCongr overlap)⟩).elim

/-- F.6.5(3) eliminates all five small alternatives using the characteristic
two already proved for both generators. -/
theorem oriented_identification [Finite G] {A B : Subgroup G}
    (h : OrientedAlternative A B)
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (A ⊓ B)) = 4) :
    Nonempty (A ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) ∧
      Nonempty (B ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) := by
  rcases h with ⟨_, hsmall⟩ | h
  · have hpA : IsPGroup 2 (generalizedFitting A) := hA ▸ pCore_isPGroup
    have hpB : IsPGroup 2 (generalizedFitting B) := hB ▸ pCore_isPGroup
    exact (hsmall.elim (fun hn => hn hpA) (fun hn => hn hpB)).elim
  · exact geometric_identification h hZ

/-- Apply the full authorized classification input, allowing the source to
interchange its two vertices. -/
theorem goldschmidt_identification [Finite G]
    (classification : GoldschmidtClassification.{u}) {A B : Subgroup G}
    (h : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (A ⊓ B)) = 4) :
    Nonempty (A ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) ∧
      Nonempty (B ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) := by
  rcases classification G A B h hcore with h | h
  · exact oriented_identification h hA hB hZ
  · exact (oriented_identification h hB hA (by simpa only [inf_comm] using hZ)).symm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
