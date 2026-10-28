module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.Degree
public import Theory.Representation.Mathieu.M23DegreeSpectrum

/-!
# The M23 spectrum: cover reduction and the literal GM02 consumer

The order-23 lower bound applies to the original faithful representation of
any central cover. For the full degree window, an independently proved
trivial-cover result transports that same representation to native M23.
The point-restriction and induction argument then supplies the spectrum,
and the existing degree-window theorem applies it to the source component.

The exact Mathieu multiplier calculation, the M22 degree gap and the
simple quotients of the induced point modules remain explicit inputs.
In particular this module does not yet export an unconditional
`m23SmallSpectrum`. Its final assembly belongs to the M23 spectrum task.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M23 paragraph, manuscript p.16; Theorem 6.6/Table 6.7, p.21.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
open Subgroup Theory.GroupTheory Representation Sporadic.Mathieu
open Representation.MathieuSmall.M23DegreeSpectrum
universe u v

/-- The cover consequence required from the existing Mathieu multiplier
owner. It is a group-theoretic input independent of the representation. -/
def M23CentralCoverTrivial : Prop :=
  ∀ {L : Type u} [Group L] [Finite L] [IsQuasisimple L],
    Nonempty (L ⧸ center L ≃* M23) → center L = ⊥

/-- Even before eliminating the center, the prime divisor 23 in the central
quotient gives the binary lower bound eleven on the original module. -/
theorem m23_finrank_ge_eleven
    {L : Type u} [Group L] [Finite L]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) L V)
    (hf : Function.Injective ρ) (e : L ⧸ center L ≃* M23) :
    11 ≤ Module.finrank (ZMod 2) V := by
  have hquot : Nat.card (L ⧸ center L) = 10200960 :=
    (Nat.card_congr e.toEquiv).trans m23_order
  have hp : 23 ∣ Nat.card L := by
    apply dvd_trans (show 23 ∣ Nat.card (L ⧸ center L) by rw [hquot]; norm_num)
    exact (center L).index_dvd_card
  have h := BinaryPrimeDegree.orderOf_le_finrank ρ hf
    (by decide : Nat.Prime 23) (by decide : 23 ≠ 2) hp
  simpa only [BinaryPrimeDegree.orderOf_two_mod_twentyThree] using h

/-- The bottom of the window is unconditional for arbitrary central covers. -/
theorem m23_finrank_eq_eleven_of_le_eleven
    {L : Type u} [Group L] [Finite L]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) L V)
    (hf : Function.Injective ρ) (e : L ⧸ center L ≃* M23)
    (hd : Module.finrank (ZMod 2) V ≤ 11) : Module.finrank (ZMod 2) V = 11 :=
  Nat.le_antisymm hd (m23_finrank_ge_eleven ρ hf e)

/-- Conditional cover-preserving assembly, with the original binary space
and faithful irreducible action transported through the supplied quotient. -/
theorem m23SmallSpectrum_of_inputs
    (hcover : M23CentralCoverTrivial.{u}) (hgap : M22SmallDegree.{v})
    (hheads : SmallInducedHeads) : M23SmallSpectrum.{u,v} := by
  intro L _ _ _ V _ _ _ ρ hf hi he hd
  obtain ⟨e⟩ := he
  have hz := hcover (L := L) ⟨e⟩
  let f : L ≃* M23 :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e
  let σ : Representation (ZMod 2) M23 V := ρ.comp f.symm.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff f.symm.toMonoidHom f.symm.surjective ρ).mpr hi
  exact finrank_eq_eleven_of_inputs hgap hheads σ (hf.comp f.symm.injective) hd

/-- Application to the actual GM02 source degree window. The parent GM02
sieve owns the generation input; the spectrum task owns the other inputs. -/
theorem m23DegreeEleven_of_spectrum_calculations
    (hg : InvolutionGeneration M23 3) (hcover : M23CentralCoverTrivial.{u})
    (hgap : M22SmallDegree.{v}) (hheads : SmallInducedHeads) : M23DegreeEleven.{u,v} :=
  m23DegreeEleven_of_gm02_inputs hg (m23SmallSpectrum_of_inputs hcover hgap hheads)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.GM02
