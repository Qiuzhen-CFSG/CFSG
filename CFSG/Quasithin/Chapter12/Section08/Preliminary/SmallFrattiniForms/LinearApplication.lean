module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.SmallFrattiniForms.Application
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.ElementaryAbelian.Quotient

/-!
# Binary linear forms on the literal tilded and central quotients

The literal identification U/Φ(U) ≃ Ũ transports the binary bilinear and
quadratic forms to `Additive Ũ`. Their evaluations are the marked commutator
and square maps, so the actual H/O₂(H) action preserves both forms whenever
the earlier-source action-kernel bound holds. On Û the central commutator
form is alternating and nondegenerate. Its quadratic companion requires the
separate elementary-center hypothesis.

Source: Aschbacher–Smith, Lemma 12.8.8(1–2), printed pp.851–852.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

section Tilde
variable [IsMulCommutative V]

theorem tilde_elementary_of_point (F : InvariantFlag T V n) (htwo : IsPGroup 2 F.U)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    IsElementaryAbelian 2 (F.tilde F.U) := by
  let : Fact (IsPGroup 2 F.U) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (F.U ⧸ frattini F.U) :=
    isElementaryAbelian_quotient_frattini
  exact IsElementaryAbelian.of_surjective (F.frattiniTildeEquiv hphi).toMonoidHom
    (F.frattiniTildeEquiv hphi).surjective

noncomputable def tildeBilinearForm (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    letI : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
    LinearMap.BilinForm (ZMod 2) (Additive (F.tilde F.U)) := by
  let : Fact (IsPGroup 2 F.U) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (F.U ⧸ frattini F.U) :=
    isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
  let f := (F.frattiniTildeEquiv hphi).symm.toMonoidHom.toAdditive.toZModLinearMap 2
  exact (SmallFrattini.quotientBilinearForm htwo (F.frattini_card_two_of_point hn hphi)).compl₁₂ f f

noncomputable def tildeQuadraticForm (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    letI : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
    QuadraticForm (ZMod 2) (Additive (F.tilde F.U)) := by
  let : Fact (IsPGroup 2 F.U) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (F.U ⧸ frattini F.U) :=
    isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
  exact (SmallFrattini.quotientQuadraticForm htwo (F.frattini_card_two_of_point hn hphi)).comp
    ((F.frattiniTildeEquiv hphi).symm.toMonoidHom.toAdditive.toZModLinearMap 2)

section Properties
variable (F : InvariantFlag T V n) (hn : 1 ≤ n) (htwo : IsPGroup 2 F.U)
variable (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)

theorem tildeBilinearForm_apply (x y : F.tilde F.U) :
    F.tildeBilinearForm hn htwo hphi (Additive.ofMul x) (Additive.ofMul y) =
      (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi)
        (F.tildePolar hn htwo hphi x y)).toAdd := rfl

theorem tildeQuadraticForm_apply (x : F.tilde F.U) :
    F.tildeQuadraticForm hn htwo hphi (Additive.ofMul x) =
      (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi)
        (F.tildeSquare hn htwo hphi x)).toAdd := rfl

theorem tildeBilinearForm_isAlt :
    letI : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
    (F.tildeBilinearForm hn htwo hphi).IsAlt := by
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
  intro x
  change (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi)
    (F.tildePolar hn htwo hphi x.toMul x.toMul)).toAdd = 0
  rw [tildePolar_self, map_one]
  rfl

theorem tildeBilinearForm_isSymm :
    letI : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
    (F.tildeBilinearForm hn htwo hphi).IsSymm := by
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
  constructor
  intro x y
  exact congrArg (fun z => (SmallFrattini.binaryMark
    (F.frattini_card_two_of_point hn hphi) z).toAdd)
    (F.tildePolar_symm hn htwo hphi x.toMul y.toMul)

theorem tildeQuadraticForm_polar :
    letI : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
    (F.tildeQuadraticForm hn htwo hphi).polarBilin = F.tildeBilinearForm hn htwo hphi := by
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
  let : Fact (IsPGroup 2 F.U) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (F.U ⧸ frattini F.U) :=
    isElementaryAbelian_quotient_frattini
  change ((SmallFrattini.quotientQuadraticForm htwo
    (F.frattini_card_two_of_point hn hphi)).comp
      ((F.frattiniTildeEquiv hphi).symm.toMonoidHom.toAdditive.toZModLinearMap 2)).polarBilin = _
  rw [QuadraticMap.polarBilin_comp, SmallFrattini.quotientQuadraticForm_polar]
  rfl

theorem tildeBilinearForm_radical (x : F.tilde F.U) :
    letI : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
    (∀ y : Additive (F.tilde F.U),
      F.tildeBilinearForm hn htwo hphi (Additive.ofMul x) y = 0) ↔
        F.tildeToUhat hn x = 1 := by
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point htwo hphi
  rw [← F.tildePolar_radical_iff hn htwo hphi x]
  have hzero (a : frattini F.U) :
      (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi) a).toAdd = 0 ↔ a = 1 := by
    change SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi) a = 1 ↔ a = 1
    exact (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi)).map_eq_one_iff
  constructor
  · intro hx y
    exact (hzero _).mp (hx (Additive.ofMul y))
  · intro hx y
    exact (hzero _).mpr (hx y.toMul)

theorem tildeBilinearForm_star_invariant
    (hcore : pCore 2 F.H ≤ (F.localTildeAction F.H le_rfl).ker)
    (h : HStar F.H) (x y : F.tilde F.U) :
    F.tildeBilinearForm hn htwo hphi (Additive.ofMul (F.tildeStarAction hcore h x))
      (Additive.ofMul (F.tildeStarAction hcore h y)) =
        F.tildeBilinearForm hn htwo hphi (Additive.ofMul x) (Additive.ofMul y) := by
  rw [tildeBilinearForm_apply, tildeBilinearForm_apply, tildePolar_star_invariant]

theorem tildeQuadraticForm_star_invariant
    (hcore : pCore 2 F.H ≤ (F.localTildeAction F.H le_rfl).ker)
    (h : HStar F.H) (x : F.tilde F.U) :
    F.tildeQuadraticForm hn htwo hphi (Additive.ofMul (F.tildeStarAction hcore h x)) =
      F.tildeQuadraticForm hn htwo hphi (Additive.ofMul x) := by
  rw [tildeQuadraticForm_apply, tildeQuadraticForm_apply, tildeSquare_star_invariant]

end Properties
end Tilde

theorem uhat_elementary_of_point (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    IsElementaryAbelian 2 F.Uhat :=
  elementary_quotient_of_frattini_le htwo _
    (central_of_normal_card_two _ (F.frattini_card_two_of_point hn hphi))

noncomputable def uhatBilinearForm (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) :
    letI : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
    LinearMap.BilinForm (ZMod 2) (Additive F.Uhat) :=
  SmallFrattini.centralBilinearForm htwo (F.frattini_card_two_of_point hn hphi)

noncomputable def uhatQuadraticForm (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hcenterPhi : frattini (center F.U) = ⊥) :
    letI : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
    QuadraticForm (ZMod 2) (Additive F.Uhat) :=
  SmallFrattini.centralQuadraticForm htwo (F.frattini_card_two_of_point hn hphi) hcenterPhi

section CentralProperties
variable (F : InvariantFlag T V n) (hn : 1 ≤ n) (htwo : IsPGroup 2 F.U)
variable (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)

theorem uhatBilinearForm_apply (x y : F.Uhat) :
    F.uhatBilinearForm hn htwo hphi (Additive.ofMul x) (Additive.ofMul y) =
      (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi)
        (F.uhatCommutator htwo x y)).toAdd := rfl

theorem uhatQuadraticForm_apply (hcenterPhi : frattini (center F.U) = ⊥) (x : F.Uhat) :
    F.uhatQuadraticForm hn htwo hphi hcenterPhi (Additive.ofMul x) =
      (SmallFrattini.binaryMark (F.frattini_card_two_of_point hn hphi)
        (F.uhatSquare htwo hcenterPhi x)).toAdd := rfl

theorem uhatBilinearForm_isAlt :
    letI : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
    (F.uhatBilinearForm hn htwo hphi).IsAlt := by
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
  exact SmallFrattini.centralBilinearForm_isAlt htwo (F.frattini_card_two_of_point hn hphi)

theorem uhatBilinearForm_isSymm :
    letI : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
    (F.uhatBilinearForm hn htwo hphi).IsSymm := by
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
  exact SmallFrattini.centralBilinearForm_isSymm htwo (F.frattini_card_two_of_point hn hphi)

theorem uhatBilinearForm_nondegenerate :
    letI : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
    (F.uhatBilinearForm hn htwo hphi).Nondegenerate := by
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
  exact SmallFrattini.centralBilinearForm_nondegenerate htwo (F.frattini_card_two_of_point hn hphi)

theorem uhatQuadraticForm_polar (hcenterPhi : frattini (center F.U) = ⊥) :
    letI : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
    (F.uhatQuadraticForm hn htwo hphi hcenterPhi).polarBilin = F.uhatBilinearForm hn htwo hphi := by
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point hn htwo hphi
  exact SmallFrattini.centralQuadraticForm_polar htwo (F.frattini_card_two_of_point hn hphi) hcenterPhi

theorem uhatBilinearForm_star_invariant
    (hcore : pCore 2 F.H ≤ F.uhatAction.ker) (h : HStar F.H) (x y : F.Uhat) :
    F.uhatBilinearForm hn htwo hphi (Additive.ofMul (F.uhatStarAction hcore h x))
      (Additive.ofMul (F.uhatStarAction hcore h y)) =
        F.uhatBilinearForm hn htwo hphi (Additive.ofMul x) (Additive.ofMul y) := by
  rw [uhatBilinearForm_apply, uhatBilinearForm_apply,
    uhatCommutator_star_invariant (hn := hn) (hphi := hphi)]

theorem uhatQuadraticForm_star_invariant (hcenterPhi : frattini (center F.U) = ⊥)
    (hcore : pCore 2 F.H ≤ F.uhatAction.ker) (h : HStar F.H) (x : F.Uhat) :
    F.uhatQuadraticForm hn htwo hphi hcenterPhi (Additive.ofMul (F.uhatStarAction hcore h x)) =
      F.uhatQuadraticForm hn htwo hphi hcenterPhi (Additive.ofMul x) := by
  rw [uhatQuadraticForm_apply, uhatQuadraticForm_apply,
    uhatSquare_star_invariant (hn := hn) (hphi := hphi)]

end CentralProperties

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
