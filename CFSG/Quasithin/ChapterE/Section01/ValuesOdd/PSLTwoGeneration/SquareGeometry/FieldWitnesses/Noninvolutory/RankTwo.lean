module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory.Actors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.NormalTransfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Local E1 witnesses from the literal PSL₂ kernel

In the branch without field involutions every elementary family member lies
in the index-two PSL₂ kernel, and its large actors have ambient tau equal
to the actor. The kernel supplements every Sylow subgroup. The normal
subgroup transport therefore preserves the original family, weak closure,
and the literal Sylow intersection of each constructed local subgroup.

An actual S₄ model with nonnormal actor, or a dihedral model of order 4r
for r an odd prime, satisfies all intrinsic E1 conditions by `OddSections`.
The actor image in the quotient by the local two-core has rank one. These
are E1 witnesses, so no component or residual assertion is required.

The transport theorem retains the independent prime-square PSL₂ placement
theorem as an explicit premise. The `Noninvolutory` assembly discharges it
using `SquareGeometry/LinearWitnesses/InnerPlacement` and proves unconditional
escape for this branch. No semilinear local-model exhaustion is assumed.

Source: Aschbacher--Smith, E.1.1--2, E.1.5, E.1.8 and E.1.14(6), printed
pp.209--211 and 214; the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory
variable {F : Type*} [Field F] [Finite F]

/-- Actual marked linear local models are E1 members in the nonsplit ambient group. -/
theorem isEMemberAt_of_localModel {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (hlarge : 5 < p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S)
    (hindex : (pGammaL2LinearKernel F S).index = 2)
    (hkernel : pGammaL2LinearKernel F S = (pGammaL2PSLRange F).subgroupOf S)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1)
    (T : Sylow 2 S) (A H : Subgroup S) (hA : IsElementaryAbelian 2 A)
    (hfour : IsKleinFour A) (hAT : A ≤ (T : Subgroup S)) (hAH : A ≤ H)
    (hSyl : ∃ U : Sylow 2 H, (U : Subgroup H) = (T : Subgroup S).subgroupOf H)
    (hlocal : PrimeGeometry.LocalModel A H) :
    IsEMemberAt 1 (T : Subgroup S) A H := by
  let := hA
  have htau := PrimeGeometry.tau_eq_self_of_selfCentralizing T A hAT
    (twoCore_eq_bot hp hodd hF hlarge S hS)
    (kleinFour_selfCentralizing hp hodd hF hlarge S hS hindex hkernel hnofield A hfour)
  have ho := PrimeGeometry.eCaseOdd_of_localModel A H hfour hAH hlocal
  have hrank : Group.rank ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 1 := by
    obtain ⟨r, _, _, _, _, _, hr⟩ := ho
    exact hr
  exact ⟨⟨hA, hAT, hAH, by rw [htau]; exact le_inf hAT hAH, hSyl, Or.inl ho⟩,
    Or.inl ⟨ho, hrank.le⟩⟩

/-- All semilinear conditions are discharged; only the independent PSL₂
placement input remains for the no-field-involution escape theorem. -/
theorem largeFamilyEscape_of_inner_geometry {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (hlarge : 5 < p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S)
    (hindex : (pGammaL2LinearKernel F S).index = 2)
    (hkernel : pGammaL2LinearKernel F S = (pGammaL2PSLRange F).subgroupOf S)
    (hnofield : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1)
    (hgeometry : ∀ U : Sylow 2 (PSL2 F), PrimeGeometry.ConcreteLocalGeometryAt U) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T := by
  let K := pGammaL2LinearKernel F S
  let : K.Normal := pGammaL2LinearKernel_normal F S
  let e : K ≃* PSL2 F := (MulEquiv.subgroupCongr hkernel).trans
    ((subgroupOfEquivOfLe hS).trans (pGammaL2PSLRangeEquiv F).symm)
  have hgeometryK := PrimeGeometry.Diagonal.concreteGeometry_of_equiv e.symm hgeometry
  have hquot : IsPGroup 2 (S ⧸ K) := IsPGroup.of_card (n := 1) (by
    rw [← index_eq_card, hindex]; rfl)
  intro T Ω hΩ hlargeActors M hTM hM hNM
  obtain ⟨A, hAΩ, hAT, hfour, H, hAH, hSyl, hlocal, hHM⟩ :=
    PrimeGeometry.Diagonal.inner_escape_of_normal_geometry K T
      (T.sup_eq_top_of_quotient_isPGroup K hquot) hgeometryK Ω hΩ hlargeActors
      (fun A hA _ => elementary_le_linearKernel_of_no_field_involutions S hnofield A (hΩ.1 A hA))
      M hTM hM hNM
  exact ⟨A, hAΩ, hAT, H, isEMemberAt_of_localModel hp hodd hF hlarge S hS
    hindex hkernel hnofield T A H (hΩ.1 A hAΩ) hfour hAT hAH hSyl hlocal, hHM⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.Noninvolutory
