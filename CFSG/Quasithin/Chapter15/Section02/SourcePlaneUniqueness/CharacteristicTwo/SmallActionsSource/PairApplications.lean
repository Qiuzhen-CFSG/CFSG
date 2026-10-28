module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Orbit
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ComponentModels
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryRank

/-!
# Source applications of the constructed residual pair

The quotient construction supplies normal, two-perfect factors K₁,K₂
and their commutator containment. Applying the existing local normalizer
argument therefore requires only the remaining Y₁/Y₁ᵗ commutator relation.
The private compatibility conversion is used only for that argument;
its two joins with S are not identified with the source's marked H₁,H₂.

For the actual binary component, the earlier wreath argument proves
reducibility, which now constructs the residual pair and places Kc in
MI = Mc ∩ I with the correct prime-to-three residual identity. The
component exclusion also obtains two-perfectness and the K₁/K₂
commutator directly from the pair.

The seed-family Frattini argument, the marked-factor identification,
and the L₄(2) split exclusion remain with this source owner. Earlier
15.2.1--14 source clauses are supplied by qt-e-152-plane-geometry and
qt-e-152-small-parabolic, with final discharge by qt-e-152-plane-uniqueness.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.21--23, printed pp.1114--1116; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Relative normality of the constructed factors proves the required commutator bound. -/
theorem ResidualPair.commutator_le {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) : ⁅p.K₁,p.K₂⁆ ≤ p.K₁ ⊓ p.K₂ := by
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp
      (p.second.1.trans ((normal_subgroupOf_iff_le_normalizer p.first.1).mp p.first.2.1)))
    (le_normalizer_iff_commutator_le_right.mp
      (p.first.1.trans ((normal_subgroupOf_iff_le_normalizer p.second.1).mp p.second.2.1)))

omit [Finite G] in
/-- Index two transports S-invariance to the second factor. -/
theorem ResidualPair.second_normalized {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) (hSA : S ≤ A) (hi : S.relIndex A = 2) :
    S ≤ normalizer (p.K₂ : Set G) := by
  rw [← p.conjugate]
  exact normalizes_conjugate_of_normalizes
    (((normal_subgroupOf_iff_le_normalizer hSA).mp (normal_of_index_eq_two hi)) p.t_mem)
    p.normalized

omit [Finite G] in
private def pairAsSplit {A S K : Subgroup G} {t : G}
    (p : ResidualPair A S K t) (hSA : S ≤ A) (hi : S.relIndex A = 2) :
    SmallActionSplit A S K where
  H₁ := p.K₁ ⊔ S
  H₂ := p.K₂ ⊔ S
  K₁ := p.K₁
  K₂ := p.K₂
  t := t
  t_mem := p.t_mem
  t_not_mem := p.t_not_mem
  K_sup_S := by rw [sup_sup_sup_comm, sup_idem, p.span]
  K₁_sup_K₂ := p.span
  K₁_le := p.first.1
  K₂_le := p.second.1
  K₁_conj := p.conjugate
  S_normalizes_K₁ := p.normalized
  S_normalizes_K₂ := p.second_normalized hSA hi

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The local exclusion now derives the K₁/K₂ relation from normality. -/
theorem commutator_exclusion_of_residualPair (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t)
    {Y : Subgroup G} (seed : Seed M I (smallActionS T ZS) Y)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hYY : ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj t).toMonoidHom) :
    ¬ ⁅Y,p.K₂⁆ ≤ Y ⊓ p.K₂ :=
  commutator_exclusion_of_pair d hI hfit
    (pairAsSplit p inf_le_left (d.escape_index hI).2) seed hC hYY p.commutator_le

/-- Construct the conjugate residual factors and apply the local normalizer
argument. Only the seed-family commutator remains an additional local input. -/
theorem exists_pair_with_commutator_exclusion (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    {Y : Subgroup G} (seed : Seed M I (smallActionS T ZS) Y)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS)
    (hYY : ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj t).toMonoidHom) :
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t,
      ¬ ⁅Y,p.K₂⁆ ≤ Y ⊓ p.K₂ := by
  obtain ⟨p⟩ := exists_residualPair d hI hnot t ht htS
  exact ⟨p,commutator_exclusion_of_residualPair d hI hfit p seed hC hYY⟩

/-- The original binary component constructs the pair through its reducibility proof. -/
theorem binary_component_residualPair
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃*
          PlaneUniquenessPreceding.LinearThree.BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    Nonempty (ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t) :=
  exists_residualPair d hI (b.binary_reducible_of_wreath d hI hmove f hfull) t ht htS

/-- The original binary component places Kc in MI and identifies its residual. -/
theorem binary_component_orbit_residual
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃*
          PlaneUniquenessPreceding.LinearThree.BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤) :
    smallActionKc H Mc ≤ Mc ⊓ I ∧ smallActionKc H Mc =
      (primeToResidual 3 (Mc ⊓ I : Subgroup G)).map (Mc ⊓ I).subtype := by
  have hnot := b.binary_reducible_of_wreath d hI hmove f hfull
  exact ⟨(orbit_centralizes_of_reducible d horbit hI hnot).trans
    (d.centralizer_le_intersection hI), orbit_residual_MI_of_reducible d horbit hI hnot⟩

/-- Apply the binary commutator calculation with the constructed normal factors. -/
theorem binary_component_false_of_residualPair
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F) {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t)
    (hmove : X < conjugateSpanBy X (planeSylow T ZS) →
      Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃*
          PlaneUniquenessPreceding.LinearThree.BinaryWreath))
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hfull : (((M ⊓ X) ⊔ planeSylow T ZS).subgroupOf (M ⊓ I)).map f = ⊤)
    (hc : ⁅X,p.K₂⁆ ≤ X.pCoreIn 2)
    (hindex : Nat.Coprime 3 ((M ⊓ X).subgroupOf (M ⊓ I)).index)
    (hK : smallActionK H = smallActionKc H Mc)
    (hquot : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      Nonempty (((Y ⊔ smallActionS T ZS : Subgroup G) ⧸
        pCore 2 (Y ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤
        Y ⊓ Y.map (MulAut.conj t).toMonoidHom) : False :=
  binary_component_false_of_pair d hI hfit b
    (pairAsSplit p inf_le_left (d.escape_index hI).2) hmove f hker hfull
    p.second.2.2.1 hc hindex hK hquot hYY p.commutator_le

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
