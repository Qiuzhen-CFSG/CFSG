module

public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo
public import Theory.SpecificGroups.Triality.Model.QTKEParameters
public import Theory.GroupTheory.Amalgam.RankTwo

/-!
# The genuine triality case of F.1.12

For every q = 2^n with n > 0, the two root-defined parabolics in the genuine
D4 graph-field carrier meet in the root Borel and generate the carrier. The
fixed positive subgroup is Sylow of order q^12. Both local factors, separately
defined as embedded O^{2′} of the parabolics, contain this Sylow subgroup.
Their joins with the Borel give a compatible isomorphism from the literal
source amalgam (L₁B,B,L₂B) to the root-parabolic inclusion amalgam.

The three-arm node is L₁: its quotient by O₂ is PSL₂ over GF(q³), and O₂ is
special of order q^9 with center of order q. The center equals both the derived
and Frattini subgroups, is elementary abelian, and is nontrivial. The central
node is L₂, with quotient PSL₂(q) and two-core order q^11. The first factor
centralizes the embedded center of the chosen Sylow. For q > 2 both local
factors equal their solvable residuals; q = 2 remains the separate exception.

The proofs assemble the concrete Bruhat geometry, root coordinates, exact
Levi kernels and fixed-field identifications. The imported outer-action results
retain Aut(GF(q³)) and its restriction on the second quotient. Their embedded
core equality supplies the p.264 Sylow step in an actual faithful normal
extension. At q = 2 exhaustive automorphism coverage excludes every proper
outer two-extension. Recognition of an arbitrary source amalgam, derivation of
local inner action from the source normality hypothesis, and final extension
elimination remain with the parent F.1.12 proof.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
F.1.4–5 and F.1.11–12(I)(4), (II), printed pp.260,262–264
(`refs/quasithin.pdf`); GLS3 §§2.3–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.Triality

open Theory.GroupTheory
open _root_.Triality.Standard
open _root_.Triality.Standard.Parabolics

private theorem subgroupAmalgam_compatibility {G : Type*} [Group G]
    (A B C : Subgroup G) (hA : B ≤ A) (hC : B ≤ C) (b : B) :
    ((RankTwoAmalgam.ofSubgroups A B C hA hC).left b : G) =
      ((RankTwoAmalgam.ofSubgroups A B C hA hC).right b : G) := rfl

variable (P : Parameters)

/-- The common root Borel maps into both root parabolics by inclusion.
In characteristic two, `overlap` identifies it with their whole intersection. -/
def amalgam : RankTwoAmalgam (parabolic P .arms) (borel P) (parabolic P .central) :=
  RankTwoAmalgam.ofSubgroups _ _ _
    (borel_le_parabolic P .arms) (borel_le_parabolic P .central)

theorem left_injective : Function.Injective (amalgam P).left :=
  RankTwoAmalgam.ofSubgroups_left_injective _ _ _ _ _

theorem right_injective : Function.Injective (amalgam P).right :=
  RankTwoAmalgam.ofSubgroups_right_injective _ _ _ _ _

/-- Both maps agree in the actual carrier on every element of the chosen Borel. -/
theorem ambient_compatibility (b : borel P) :
    ((amalgam P).left b : Carrier P) = ((amalgam P).right b : Carrier P) :=
  subgroupAmalgam_compatibility (parabolic P .arms) (borel P) (parabolic P .central)
    (borel_le_parabolic P .arms) (borel_le_parabolic P .central) b


open scoped MatrixGroups

/-- The two parabolics meet in exactly the root Borel. -/
theorem overlap (hp : P.prime = 2) :
    parabolic P .arms ⊓ parabolic P .central = borel P :=
  parabolic_inf_binary P hp

/-- Both parabolics are proper in the actual triality carrier. -/
theorem parabolic_proper (hp : P.prime = 2) (a : Node) : parabolic P a ≠ ⊤ :=
  parabolic_ne_top_binary P hp a

/-- Together the two root parabolics generate the carrier. -/
theorem parabolics_generate (hp : P.prime = 2) :
    parabolic P .arms ⊔ parabolic P .central = ⊤ := parabolic_sup_binary P hp

/-- The source Sylow subgroup is the graph-field fixed positive root group. -/
def sylow (hp : P.prime = 2) : Sylow 2 (Carrier P) := unipotentSylow P hp

@[simp] theorem sylow_coe (hp : P.prime = 2) :
    (sylow P hp : Subgroup (Carrier P)) = unipotent P := rfl

theorem sylow_card (hp : P.prime = 2) : Nat.card (sylow P hp) = P.q ^ 12 :=
  card_unipotent_binary P hp

/-- The Borel is the full normalizer of this actual Sylow subgroup. -/
theorem sylow_normalizer (hp : P.prime = 2) :
    Subgroup.normalizer (sylow P hp : Set (Carrier P)) = borel P :=
  ConcreteBruhat.normalizer_unipotent_eq_borel P hp

theorem sylow_le_localFactor (hp : P.prime = 2) (a : Node) :
    (sylow P hp : Subgroup (Carrier P)) ≤ localFactor P a :=
  unipotentSylow_le_localFactor P hp a

/-- The source local factor is normal in its parabolic, not in the whole carrier. -/
theorem localFactor_relative_normal (a : Node) :
    ((localFactor P a).subgroupOf (parabolic P a)).Normal := localFactor_normal P a

/-- The source amalgam uses the distinct local factors joined with the Borel. -/
def sourceAmalgam :
    RankTwoAmalgam (localFactor P .arms ⊔ borel P : Subgroup (Carrier P)) (borel P)
      (localFactor P .central ⊔ borel P : Subgroup (Carrier P)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ le_sup_right le_sup_right

/-- The literal (L₁B,B,L₂B) amalgam is isomorphic to the root-parabolic amalgam,
including both commuting squares on the whole Borel. -/
def sourceAmalgamIso (hp : P.prime = 2) :
    RankTwoAmalgam.Iso (sourceAmalgam P) (amalgam P) where
  left := MulEquiv.subgroupCongr (localFactor_sup_borel_binary P hp .arms)
  middle := MulEquiv.refl _
  right := MulEquiv.subgroupCongr (localFactor_sup_borel_binary P hp .central)
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- The source orientation uses the embedded center of the chosen Sylow. -/
theorem source_orientation (hp : P.prime = 2) :
    ⁅localFactor P .arms, (Subgroup.center (sylow P hp)).map (sylow P hp : Subgroup (Carrier P)).subtype⁆ = ⊥ :=
  localFactor_arms_commutator_center_unipotent P hp

/-- The first two-core is nonabelian, including over the field of order two. -/
theorem arms_twoCore_commutator_ne_bot (hp : P.prime = 2) :
    commutator (pCore 2 (localFactor P .arms)) ≠ ⊥ := by
  intro h
  have hc := localFactor_arms_twoCore_center_card P hp
  rw [localFactor_arms_twoCore_center_eq_commutator P hp, h, Subgroup.card_bot] at hc
  have hq := P.q_ge_two
  omega

/-- All special-group clauses in the source notation q^(1+8), with the actual O₂. -/
theorem arms_twoCore_special (hp : P.prime = 2) :
    let Q := pCore 2 (localFactor P .arms)
    IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
      commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
      IsElementaryAbelian 2 (Subgroup.center Q) ∧
      Nat.card Q = P.q ^ 9 ∧ Nat.card (Subgroup.center Q) = P.q :=
  ⟨pCore_isPGroup, arms_twoCore_commutator_ne_bot P hp,
    (localFactor_arms_twoCore_center_eq_commutator P hp).symm,
    (localFactor_arms_twoCore_center_eq_frattini P hp).symm,
    localFactor_arms_twoCore_center_elementary P hp,
    localFactor_arms_twoCore_card P hp, localFactor_arms_twoCore_center_card P hp⟩

/-- The complete local clauses of F.1.12(I)(4). The first field has order q³;
the second has order q, and each quotient is by its intrinsic two-core. -/
theorem source_local_structure (hp : P.prime = 2) :
    Nat.card (ExtensionField P) = P.q ^ 3 ∧
    Nat.card (GaloisField P.prime P.exponent) = P.q ∧
    Nonempty ((localFactor P .arms ⧸ pCore 2 (localFactor P .arms)) ≃*
      PSL(2, ExtensionField P)) ∧
    (let Q := pCore 2 (localFactor P .arms)
     IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
       commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
       IsElementaryAbelian 2 (Subgroup.center Q) ∧
       Nat.card Q = P.q ^ 9 ∧ Nat.card (Subgroup.center Q) = P.q) ∧
    Nonempty ((localFactor P .central ⧸ pCore 2 (localFactor P .central)) ≃*
      PSL(2, GaloisField P.prime P.exponent)) ∧
    Nat.card (pCore 2 (localFactor P .central)) = P.q ^ 11 :=
  ⟨card_extensionField P, GaloisField.card P.prime P.exponent (by have := P.exponent_pos; omega),
    ⟨localFactorArmsQuotientEquivPSL2 P hp⟩, arms_twoCore_special P hp,
    ⟨localFactorCentralQuotientEquivPSL2 P hp⟩, localFactor_central_twoCore_card P hp⟩

/-- In the concrete carrier both factors contain the chosen Sylow. -/
theorem localFactor_sup_sylow (hp : P.prime = 2) (a : Node) :
    localFactor P a ⊔ (sylow P hp : Subgroup (Carrier P)) = localFactor P a :=
  sup_eq_left.mpr (sylow_le_localFactor P hp a)

/-- The two embedded cores of the concrete LiS and Li are the same root radical. -/
theorem localFactor_sup_sylow_core (hp : P.prime = 2) (a : Node) :
    (localFactor P a ⊔ (sylow P hp : Subgroup (Carrier P))).pCoreIn 2 =
      (localFactor P a).pCoreIn 2 ∧
    (localFactor P a).pCoreIn 2 = radical P a := by
  rw [localFactor_sup_sylow]
  exact ⟨rfl, localFactor_twoCore_map P hp a⟩

/-- The large-field conclusion of F.1.12(II)(i), with embedded solvable residuals. -/
theorem source_large_residuals (hp : P.prime = 2) (hq : 2 < P.q) (a : Node) :
    (Subgroup.solvableResidual (localFactor P a)).map (localFactor P a).subtype =
      localFactor P a ∧ (sylow P hp : Subgroup (Carrier P)) ≤ localFactor P a :=
  ⟨localFactor_solvableResidual_map P hp hq a, sylow_le_localFactor P hp a⟩

/-- The only small-field exception in this family is the actual ³D₄(2) carrier. -/
theorem source_residual_alternatives (hp : P.prime = 2) :
    (∀ a : Node,
      (Subgroup.solvableResidual (localFactor P a)).map (localFactor P a).subtype =
        localFactor P a ∧ (sylow P hp : Subgroup (Carrier P)) ≤ localFactor P a) ∨
    P.q = 2 := by
  by_cases hq : P.q = 2
  · exact Or.inr hq
  · exact Or.inl (source_large_residuals P hp (by have := P.q_ge_two; omega))

/-- The genuine binary model supplies every local and geometric clause of case (4).
No construction, quotient, radical, or overlap premise remains. Recognition of an
arbitrary source amalgam and final extension elimination belong to F.1.12's parent. -/
theorem concrete_case_four (n : ℕ) (hn : 0 < n) :
    let P := binaryParameters n hn
    ∃ S : Sylow 2 (Carrier P),
      (S : Subgroup (Carrier P)) = unipotent P ∧
      Nat.card S = (2 ^ n) ^ 12 ∧
      Subgroup.normalizer (S : Set (Carrier P)) = borel P ∧
      parabolic P .arms ⊓ parabolic P .central = borel P ∧
      parabolic P .arms ⊔ parabolic P .central = ⊤ ∧
      (∀ a : Node, parabolic P a ≠ ⊤) ∧
      Nonempty (RankTwoAmalgam.Iso (sourceAmalgam P) (amalgam P)) ∧
      (∀ a : Node, (S : Subgroup (Carrier P)) ≤ localFactor P a) ∧
      ⁅localFactor P .arms, (Subgroup.center S).map (S : Subgroup (Carrier P)).subtype⁆ = ⊥ ∧
      Nat.card (ExtensionField P) = (2 ^ n) ^ 3 ∧
      Nat.card (GaloisField 2 n) = 2 ^ n ∧
      Nonempty ((localFactor P .arms ⧸ pCore 2 (localFactor P .arms)) ≃*
        PSL(2, ExtensionField P)) ∧
      (let Q := pCore 2 (localFactor P .arms)
       IsPGroup 2 Q ∧ commutator Q ≠ ⊥ ∧
         commutator Q = Subgroup.center Q ∧ frattini Q = Subgroup.center Q ∧
         IsElementaryAbelian 2 (Subgroup.center Q) ∧
         Nat.card Q = (2 ^ n) ^ 9 ∧ Nat.card (Subgroup.center Q) = 2 ^ n) ∧
      Nonempty ((localFactor P .central ⧸ pCore 2 (localFactor P .central)) ≃*
        PSL(2, GaloisField 2 n)) ∧
      Nat.card (pCore 2 (localFactor P .central)) = (2 ^ n) ^ 11 := by
  let P := binaryParameters n hn
  exact ⟨sylow P rfl, sylow_coe P rfl, sylow_card P rfl,
    sylow_normalizer P rfl, overlap P rfl, parabolics_generate P rfl,
    parabolic_proper P rfl, ⟨sourceAmalgamIso P rfl⟩,
    sylow_le_localFactor P rfl, source_orientation P rfl, source_local_structure P rfl⟩

open _root_.Triality.Standard.ParabolicOuterTwo Subgroup

/-- The p.264 step in an actual self-centralizing normal triality extension.
The Sylow subgroup of LiS is constructed by restriction of the ambient Sylow;
local inner action forces S into the embedded local factor and hence the carrier.
All cores and intersections are literal subgroups of the same extension. -/
theorem extension_sylow_step {E : Type*} [Group E] [Finite E]
    (K : Subgroup E) [K.Normal] (n : ℕ) (hn : 0 < n)
    (e : K ≃* BinaryCarrier n hn) (hC : centralizer (K : Set E) = ⊥)
    (a : Node) (S : Sylow 2 E)
    (hSL : (S : Subgroup E) ≤ normalizer ((localFactor (binaryParameters n hn) a).map
      (K.subtype.comp e.symm.toMonoidHom)))
    (hinner :
      let L := (localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom)
      let T := S.subtype (show (S : Subgroup E) ≤ L ⊔ (S : Subgroup E) from le_sup_right)
      (T : Subgroup _).map (pCoreJoinAction 2 hSL) ≤ MulAut.innerSubgroup (L ⧸ pCore 2 L)) :
    let L := (localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom)
    (L ⊔ (S : Subgroup E)).pCoreIn 2 = L.pCoreIn 2 ∧
    (S : Subgroup E) = L.pCoreIn 2 ⊔ ((S : Subgroup E) ⊓ L) ∧
    (S : Subgroup E) ≤ L ∧ (S : Subgroup E) ≤ K := by
  let L := (localFactor (binaryParameters n hn) a).map (K.subtype.comp e.symm.toMonoidHom)
  let T := S.subtype (show (S : Subgroup E) ≤ L ⊔ (S : Subgroup E) from le_sup_right)
  have hT : (T : Subgroup _).map (L ⊔ (S : Subgroup E)).subtype = (S : Subgroup E) := by
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  have hfactor := normalExtension_source_factorization K n hn e hC a S S.isPGroup'
    hSL T hT hinner
  have hle : (S : Subgroup E) ≤ L := by
    rw [hfactor]
    exact sup_le (pCoreIn_le 2 L) inf_le_right
  refine ⟨normalExtension_local_twoCore_eq K n hn e hC a S S.isPGroup' hSL,
    hfactor, hle, hle.trans ?_⟩
  rintro x ⟨g, _, rfl⟩
  exact (e.symm g).property

/-- At q = 2 no proper outer two-extension of the genuine carrier exists.
Coverage uses Aut(GF(8)), so the possible odd coefficient action is retained. -/
theorem no_extension_at_two {E : Type*} [Group E]
    (K : Subgroup E) [K.Normal] (e : K ≃* BinaryCarrier 1 Nat.zero_lt_one)
    (hC : centralizer (K : Set E) = ⊥) (h2 : IsPGroup 2 (E ⧸ K)) : K = ⊤ :=
  normalExtension_eq_top_at_two K e hC h2

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.Triality
