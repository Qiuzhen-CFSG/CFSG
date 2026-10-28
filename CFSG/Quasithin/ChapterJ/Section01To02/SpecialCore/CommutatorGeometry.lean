module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.Propagation
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.FixedSeed
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.ParabolicGeometry
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Full commutators and Steinberg geometry in J.2.3(6,8,9)

The propagation theorem rules out a proper commutator image once the
chosen Sylow-fixed lift has full image. This module applies that argument
to the literal Chapter J setup and constructs C_S(t)/V ≃ E₃₂ with
2-rank five. Its normal subgroup is V restricted to C_S(t), not V as a
normal subgroup of the ambient group.

The seed theorem obtains the full commutator image modulo Z from the actual
natural SL₂(4) action, then absorbs Z by Sylow invariance. The natural Ru1
action supplies the parabolic stabilizer used to propagate that seed to
every t in S outside V. The common Ru1 marking also identifies U/V with
the point-radical fixed plane and proves the conjugate-intersection clause.

The final assembly discharges the seed and natural-parabolic premises. Its
only inputs beyond LocalSetup are the preceding J.2.2(1) equalities
R₁ = Q ⊔ S and O₂(L₁T) = R₁. The source owner for J.2.1–2 produces these
equalities; the section owner discharges them when assembling J.2.3.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.3(6,8,9), printed p.433 (PDF p.444).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G} (r : RuOne L V)

include r in
/-- The elementary-abelian rank convention for the literal centralizer quotient. -/
theorem quotient_rank_five (t : L.pCoreIn 2)
    [(V.subgroupOf (L.pCoreIn 2 ⊓ centralizer ({(t : G)} : Set G))).Normal]
    (hfull : ⁅zpowers (t : G), L.pCoreIn 2⁆ = V) :
    primeRank 2 ((L.pCoreIn 2 ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      V.subgroupOf (L.pCoreIn 2 ⊓ centralizer ({(t : G)} : Set G))) = 5 := by
  let A := (L.pCoreIn 2 ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
    V.subgroupOf (L.pCoreIn 2 ⊓ centralizer ({(t : G)} : Set G))
  obtain ⟨e⟩ := r.coreCentralizer_quotient_equiv t hfull
  have hpowE (v : Multiplicative (Fin 5 → ZMod 2)) : v ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    change 2 • v.toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  have hpow (a : A) : a ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, hpowE, map_one]
  let : IsElementaryAbelian 2 A := {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hcardE : Nat.card (Multiplicative (Fin 5 → ZMod 2)) = 2 ^ 5 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hcard : Nat.card A = 2 ^ 5 := (Nat.card_congr e.toEquiv).trans hcardE
  apply le_antisymm
  · exact IsElementaryAbelian.primeRank_le_of_card_le A hcard.le
  · exact primeRank_ge_of_elementary_embedding hpowE hcardE e.symm.toMonoidHom e.symm.injective

/-- J.2.3(6), including the actual normal kernel, E₃₂ quotient and rank five,
after the one Sylow-fixed seed and natural parabolic fact are supplied.
The source assembly must still discharge those two inputs. -/
theorem source_six_of_seed (d : LocalSetup G)
    (hparabolic : NaturalParabolics d.L d.V)
    (hseed : SylowSeed d.ru1 d.sylowInL)
    (t : d.toTypeRuSetup.S) (ht : (t : G) ∉ d.V) :
    let := d.ru1.coreCentralizer_kernel_normal t
    ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V ∧
    Nonempty (((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) ≃*
        Multiplicative (Fin 5 → ZMod 2)) ∧
    primeRank 2 ((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) = 5 := by
  let := d.ru1.coreCentralizer_kernel_normal t
  have hfull := full_commutator_of_one_seed d.ru1 hparabolic d.sylowInL hseed t ht
  exact ⟨hfull, d.ru1.coreCentralizer_quotient_equiv t hfull,
    quotient_rank_five d.ru1 t hfull⟩

/-- The full-commutator conclusion of J.2.3(6), from the preceding core
equalities. Both the Sylow-fixed seed and its parabolic propagation are proved. -/
theorem full_commutator (d : LocalSetup G)
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁)
    (t : d.toTypeRuSetup.S) (ht : (t : G) ∉ d.V) :
    ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V :=
  FixedSeed.full_commutator d hprod hcore (natural_parabolics d.ru1) t ht

/-- J.2.3(6), with the literal relatively normal kernel, E₃₂ quotient,
and source rank-five conclusion. No seed or stabilizer premise remains. -/
theorem source_six (d : LocalSetup G)
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁)
    (t : d.toTypeRuSetup.S) (ht : (t : G) ∉ d.V) :
    let := d.ru1.coreCentralizer_kernel_normal t
    ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V ∧
    Nonempty (((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) ≃*
        Multiplicative (Fin 5 → ZMod 2)) ∧
    primeRank 2 ((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) = 5 :=
  source_six_of_seed d (natural_parabolics d.ru1) (FixedSeed.sylowSeed d hprod hcore) t ht

/-- J.2.3(6,8,9) from LocalSetup and the two preceding J.2.2(1) core
equalities. The fixed subgroup is in the literal S/V quotient, with its exact
ambient commutator preimage, and conjugates use the specified ambient element.
The J.2.3 assembly owner supplies the two preceding-source equalities. -/
theorem source_six_eight_nine (d : LocalSetup G)
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 = d.toTypeRuSetup.R₁) :
    let := d.ru1.steinberg.kernel_normal
    (∀ (t : d.toTypeRuSetup.S), (t : G) ∉ d.V →
      let := d.ru1.coreCentralizer_kernel_normal t
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V ∧
      Nonempty (((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
        d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) ≃*
          Multiplicative (Fin 5 → ZMod 2)) ∧
      primeRank 2 ((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
        d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) = 5) ∧
    quotientFixed d = (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map
      (QuotientGroup.mk' (d.V.subgroupOf d.toTypeRuSetup.S)) ∧
    (∀ s : d.toTypeRuSetup.S, (s : G) ∈ d.toTypeRuSetup.U ↔
      ∀ a ∈ d.toTypeRuSetup.R₁, ⁅a, (s : G)⁆ ∈ d.V) ∧
    ∀ l ∈ d.L, l ∉ d.toTypeRuSetup.H →
      d.toTypeRuSetup.U ⊓ d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom = d.V := by
  let := d.ru1.steinberg.kernel_normal
  have hparabolic : d.toTypeRuSetup.R₁ = d.parabolic.pCoreIn 2 := by
    rw [← d.H_inf_L, inf_comm] at hcore
    exact hcore.symm
  exact ⟨source_six d hprod hcore, source_eight_nine d hparabolic⟩

end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry
