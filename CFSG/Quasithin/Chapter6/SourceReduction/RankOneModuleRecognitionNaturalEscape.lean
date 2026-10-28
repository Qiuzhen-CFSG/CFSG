module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalEscapeDefs
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import GorensteinWalter.PSL2Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic

/-!
# The terminal contradiction on the actual quotient U/Z_S

The geometric identities give |U/Z_S| ≤ 256 by the proved 6.1.26 argument.
If this quotient is elementary abelian, its automorphism group embeds in
GL₈(2). The prime divisors of GL₈(2) are 2, 3, 5, 7, 17, 31 and 127.
Thus its actual action image cannot contain PSL₂(p) for p ≥ 11 with
p congruent to 3 or 5 modulo 8, the alternatives of 6.1.25(2).

This proves the final contradiction without the cross-characteristic degree
bound used in the book. Elementary abelianness of the quotient follows from
the layer and the commutator bound. The earlier source geometry and marked
component image remain explicit inputs; this is not yet 6.1.27.

Source: Aschbacher--Smith, 6.1.25--27, printed pp.677--679.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscape

private theorem card_GL_eight :
    Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) =
      2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ZMod.card]

private theorem prime_not_dvd_GL_eight {p : ℕ} (hp : p.Prime)
    (hlarge : 11 ≤ p) (hmod : p % 8 = 3 ∨ p % 8 = 5) :
    ¬ p ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  rw [card_GL_eight]
  simp only [hp.dvd_mul]
  intro h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  all_goals
    try replace h := hp.dvd_of_dvd_pow h
    have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
    omega

private theorem prime_dvd_card_psl {A : Type*} [Group A] {p : ℕ}
    (hp : p.Prime) (hlarge : 11 ≤ p) (hmodel : ClassicalGroup.IsPSL A 2 p) :
    p ∣ Nat.card A := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  have hodd := hp.odd_of_ne_two (by omega)
  have heven : 2 ∣ p ^ 2 - 1 := by
    obtain ⟨a, ha⟩ := hodd
    refine ⟨2 * a * (a + 1), ?_⟩
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  rw [Nat.card_congr e.toEquiv,
    GorensteinWalter.psl2_card_formula F
      ⟨p, 1, hp, hodd, by decide, by simpa using hcard⟩, hcard]
  apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right heven p)).mpr
  simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) heven

variable {G : Type*} [Group G] [Finite G] {T L V : Subgroup G}
  [hN : ((ZS T L V).subgroupOf (Escape.U T L V)).Normal]

/-- The source's PSL₂ prime image cannot act on the actual elementary
quotient once the geometric order bound is known. -/
theorem false_of_small_quotient
    (hsmall : Nat.card (Quotient T L V) ≤ 256)
    (helementary : IsElementaryAbelian 2 (Quotient T L V))
    (hcomponent : PrimeComponent T L V) : False := by
  let := helementary
  obtain ⟨p, hp, hlarge, hmod, K, hK⟩ := hcomponent
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := 8) (Quotient T L V) hsmall
  have hd := (prime_dvd_card_psl hp hlarge hK).trans
    ((K.map (action T L V)).card_subgroup_dvd_card.trans
      (card_dvd_of_injective f hf))
  exact prime_not_dvd_GL_eight hp hlarge hmod hd

omit hN in
/-- All splitting, irreducibility, and size premises of the terminal
estimate are discharged by the earlier geometric identities and genuine
natural actions. The quotient retains the caller's normality instance. -/
theorem Geometry.quotient_card_le (d : Geometry T L V)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card (Quotient T L V) ≤ 256 := by
  have hb := Escape.quotient_bound_of_geometric_identities
    d.g_mem d.l_mem hnatural d.generated d.intersection_commutes d.U_le_T
    d.core d.product d.central d.line_card d.conjugate_index d.fixed_right
    d.fixed_left hCT d.natural_section d.centralizer_index d.commutator d.U_index
  exact hb.2.2

/-- The literal terminal application of 6.1.26 to the prime component
from 6.1.25. Its earlier-source premises must still be constructed. -/
theorem false_of_geometry (d : Geometry T L V)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hCT : T ⊓ centralizer (L : Set G) = ⊥)
    (hV : IsElementaryAbelian 2 (layer L V))
    (hcomponent : PrimeComponent T L V) : False :=
  false_of_small_quotient (d.quotient_card_le hnatural hCT)
    (quotient_elementary_of_commutator T L V hV d.commutator) hcomponent

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscape
