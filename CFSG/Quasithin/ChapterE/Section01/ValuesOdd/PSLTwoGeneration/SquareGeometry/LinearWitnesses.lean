module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections

/-!
# Linear prime-square local escape witnesses

For an actual PSL₂ or PGL₂ model, a large elementary actor is a four-group
and its ambient tau is the actor. An S₄ subgroup with nonnormal actor, or a
dihedral subgroup of order four times an odd prime, then supplies every E1
clause once its literal intersection with the chosen Sylow is Sylow in it.
The intrinsic odd-section theorem verifies the quotient by its two-core,
nontrivial odd core, commutator identity, two-group quotient and image rank.
This uses E1; no component or residual assertion is substituted for E2.

The final theorem assembles the two proved concrete placement calculations into the
`hlinear` input of `SquareGeometry.largeFamilyEscape_of_model_calculations`,
transporting actual witnesses through the supplied model isomorphism. The
inner calculation includes the subfield overgroups and the separate q=9
paired-normalizer argument. The diagonal calculation handles both inner and
outer four-groups. Thus p=3 and p=5 are included, with no remaining placement
or intrinsic-quotient premise. The field-automorphism branch remains with
the parent semilinear assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.3(2), E.1.2 and E.1.14(6), printed pp.33, 209--210 and 214;
the last cites Aschbacher (1982), Lemma 4.10.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
open Subgroup GorensteinWalter
variable {F : Type*} [Field F] [Finite F]
variable {G : Type*} [Group G] [Finite G]

/-- An actual local model supplies every E1 clause in a linear ambient group. -/
theorem isEMemberAt_of_localModel (hodd : IsOddPrimePower (Nat.card F))
    (hlarge : 3 < Nat.card F)
    (hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F))
    (T : Sylow 2 G) (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hr : 1 < Group.rank A) (hAH : A ≤ H)
    (hSylow : ∃ U : Sylow 2 H, (U : Subgroup H) = (T : Subgroup G).subgroupOf H)
    (hlocal : PrimeGeometry.LocalModel A H) : IsEMemberAt 1 (T : Subgroup G) A H := by
  have ho := PrimeGeometry.eCaseOdd_of_localModel A H
    (large_actor_isKleinFour hodd hmodel A hr) hAH hlocal
  have hrank : Group.rank ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 1 := by
    obtain ⟨p, _, _, _, _, _, hrank⟩ := ho
    exact hrank
  refine ⟨⟨inferInstance, hAT, hAH, ?_, hSylow, Or.inl ho⟩, Or.inl ⟨ho, hrank.le⟩⟩
  rw [tau_eq_actor hodd hlarge hmodel T A hAT hr]
  exact le_inf hAT hAH

/-- Local placement is the only remaining input on an actual linear model. -/
theorem largeFamilyEscapeAt_of_geometry (hodd : IsOddPrimePower (Nat.card F))
    (hlarge : 3 < Nat.card F)
    (hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F))
    (T : Sylow 2 G) (hgeometry : PrimeGeometry.ConcreteLocalGeometryAt T) :
    LargeFamilyEscapeAt T := by
  apply largeFamilyEscapeAt_of_maximal_escape T
  intro Ω hΩ hlargeActors M hM hTM hNM
  obtain ⟨A, hA, hAT, hfour, H, hAH, hSylow, hlocal, hHM⟩ :=
    hgeometry Ω hΩ hlargeActors M hM hTM hNM
  let : IsElementaryAbelian 2 A := hΩ.1 A hA
  have hne : A ≠ ⊥ := by
    intro he
    have hc := hfour.card_four
    rw [he, Subgroup.card_bot] at hc
    omega
  exact ⟨A, hA, hAT, H, isEMemberAt_of_localModel hodd hlarge hmodel T A H
    hAT (hlargeActors A hA hAT hne) hAH hSylow hlocal, hHM⟩

local instance : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Conditional assembly for the two concrete placement calculations.
`largeFamilyEscape_of_linear_model` discharges both inputs. -/
theorem largeFamilyEscape_of_linear_model_geometry
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hmodel : Nonempty (S ≃* PSL2 F) ∨ Nonempty (S ≃* PGL2 F))
    (hinner : ∀ T : Sylow 2 (PSL2 F), PrimeGeometry.ConcreteLocalGeometryAt T)
    (hdiagonal : ∀ T : Sylow 2 (PGL2 F), PrimeGeometry.ConcreteLocalGeometryAt T) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T := by
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp, hodd, by decide, hF⟩
  have hq3 : 3 < Nat.card F := by omega
  rcases hmodel with he | he
  · obtain ⟨e⟩ := he
    exact largeFamilyEscape_of_equiv e.symm (fun T =>
      largeFamilyEscapeAt_of_geometry hq hq3 (Or.inl ⟨MulEquiv.refl _⟩) T (hinner T))
  · obtain ⟨e⟩ := he
    exact largeFamilyEscape_of_equiv e.symm (fun T =>
      largeFamilyEscapeAt_of_geometry hq hq3 (Or.inr ⟨MulEquiv.refl _⟩) T (hdiagonal T))

/-- The complete linear input of `SquareGeometry.largeFamilyEscape_of_model_calculations`.
An actual PSL₂ or PGL₂ isomorphism over an odd prime-square field supplies
escaping E1 witnesses for every Sylow, including at q=9 and q=25. -/
theorem largeFamilyEscape_of_linear_model
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hlarge : 5 < p ^ 2)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hmodel : Nonempty (S ≃* PSL2 F) ∨ Nonempty (S ≃* PGL2 F)) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T :=
  largeFamilyEscape_of_linear_model_geometry hp hodd hlarge hF S hmodel
    (InnerPlacement.concreteLocalGeometryAt hp hodd hlarge hF)
    (DiagonalPlacement.concreteLocalGeometryAt hp hodd hlarge hF)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
