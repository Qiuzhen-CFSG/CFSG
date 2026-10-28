module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.Marking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.DiagramAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.PlaneGeometry
public import Theory.ElementaryAbelian.Quotient

/-!
# Quotient and marking preparation for the four-dimensional case of 15.3.24

The actual source quotients are E₉ and S₃ × S₃. The marked image of
Y₊(S ∩ L) is solvable with three-part nine, and the Y₊ image retains its
cubic-generation identity. The section maps and induced Sylow action use
ambient conjugation and intrinsic two-cores throughout.

The two invariant cubic axes exclude graph interchange in the actual
Sylow action. The solvable Sylow overgroup in GL₄(2) is a plane stabilizer;
its maximality and L ≰ M give M ∩ L = Y₊(S ∩ L). Relative core transport
identifies the actual R ∩ L image with its elementary radical of order
sixteen. These constructions assemble in `source_preparation`.

The plane is constructed for every supplied L/O₂(L) ≃ PSL₄(2), including
an independently marked module supplied by classification. The full Y₊
image is the cubic-generated subgroup of this parabolic; it is not
identified with Y₊/O₂(Y₊). The genuine earlier clauses remain explicit in
`Earlier`; the subsequent module classification and elimination are not
asserted here.

Source: Aschbacher–Smith, 15.3.24, printed pp.1129–1130,
combined manuscript (1 March 2004).
-/

public section

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation

variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
variable {c : ComponentWitness d I}

/-- The required plane marking for any component-quotient coordinates,
in particular the coordinates chosen independently by module classification. -/
theorem nonempty_planeParabolic (h : Earlier d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4) :
    Nonempty (PlaneParabolic d c.L e) := by
  obtain ⟨p⟩ := nonempty_parabolicData h e
  exact ⟨p.marking⟩

/-- The actual section (R ∩ L)/O₂(L) is elementary of order sixteen.
`radical_denominator` identifies the full O₂(L) in this section, and
`coreSectionEquiv_apply` retains its original quotient projection. -/
theorem radical_section (h : Earlier d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4) :
    IsElementaryAbelian 2 (CoreSection c.L (d.R ⊓ c.L)) ∧
      Nat.card (CoreSection c.L (d.R ⊓ c.L)) = 16 := by
  obtain ⟨p⟩ := nonempty_parabolicData h e
  let a := p.radical_coordinates
  have : IsElementaryAbelian 2 (Multiplicative (Fin 4 → ZMod 2)) :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        apply Multiplicative.toAdd.injective
        change 2 • x.toAdd = 0
        exact ZModModule.char_nsmul_eq_zero 2 x.toAdd }
  refine ⟨IsElementaryAbelian.of_surjective a.symm.toMonoidHom a.symm.surjective, ?_⟩
  rw [Nat.card_congr a.toEquiv]
  change Nat.card (Fin 4 → ZMod 2) = 16
  simp

/-- The first two paragraphs of the four-dimensional branch of 15.3.24,
from the precise earlier inputs. Both quotients, innerness of the actual
Sylow action, the marked intersection and its radical are constructed.
The final equality specifies the full Y₊ image under the same marking. -/
theorem source_preparation (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2) (h : Earlier d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
    Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
    IsInnerOnComponent d c.L h.sylow_normalizes_component ∧
    ∃ p : ParabolicData d c.L e,
      modelImage (by decide) e d.Yplus = theta (BinaryLinear.parabolic p.marking.plane) := by
  obtain ⟨hy, hj⟩ := source_quotients h (Or.inl rfl) e
  obtain ⟨p⟩ := nonempty_parabolicData h e
  exact ⟨hy, hj, sylow_inner_four hI hf hrank c h e, p,
    yplusImage_eq_planeTheta h p.marking⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
