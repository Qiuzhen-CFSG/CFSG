module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.OrderBounds
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.Consequences
public import GorensteinWalter.PSL2Cardinality
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Generators

/-!
# Concrete model exclusions for the dihedral shadow sieve

A Sylow subgroup isomorphic to D₈ excludes every subgroup whose order is
divisible by 16. The actual PSL₂ order formula excludes PSL₂(25) by the
prime 13 and the prime-field candidates in A.3.14(3) by their defining
prime. The explicit J₁ matrix group's checked element of order 11 excludes
J₁; no full J₁ order or simplicity certification is needed.

Each comparison is an actual group isomorphism with a subgroup of the
faithful shadow image. The exhaustive extraction of these cases from the
appendix component theorem remains separate.

Source: Aschbacher–Smith, A.3.14, printed pp.49–50, and the final paragraph
of the proof of Lemma 16.4.7, printed p.1187. J₁'s underlying ATLAS matrices
and attribution are retained in its imported model.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
variable {G : Type*} [Group G] [Finite G]

theorem not_sixteen_dvd (L : Subgroup G) (g r z : G)
    (S : Sylow 2 (Image L g r z)) (e : S ≃* DihedralGroup 4)
    (N : Subgroup (Image L g r z)) : ¬ 16 ∣ Nat.card N := by
  intro hn
  have h : 2 ^ 4 ∣ Nat.card (Image L g r z) := hn.trans N.card_subgroup_dvd_card
  have hs := S.pow_dvd_card_of_pow_dvd_card h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hs
  norm_num at hs

theorem exclude_psl2_twentyfive (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z))
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 25)
    (e : N ≃* GorensteinWalter.PSL2 F) : False := by
  apply not_thirteen_dvd L g r z hV N
  rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F
    ⟨5, 2, by decide, by decide, by decide, by simpa using hF⟩, hF]
  norm_num

theorem exclude_psl2_prime (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z))
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hfive : p ^ 2 % 5 = 1) (height : p % 8 = 3 ∨ p % 8 = 5)
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = p)
    (e : N ≃* GorensteinWalter.PSL2 F) : False := by
  apply excluded_prime_parameter L g r z hV N hp hlarge hfive height
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : 2 ∣ p ^ 2 - 1 := by
    obtain ⟨a, ha⟩ := hpodd
    refine ⟨2 * a * (a + 1), ?_⟩
    nlinarith [Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith)]
  rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F
    ⟨p, 1, hp, hpodd, by decide, by simpa using hF⟩, hF]
  apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right heven p)).mpr
  simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) heven

theorem exclude_janko_one (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z))
    (e : N ≃* Janko1.Model) : False := by
  apply not_eleven_dvd L g r z hV N
  rw [Nat.card_congr e.toEquiv]
  exact Janko1.OrderCertificate.orderOf_eleven ▸
    orderOf_dvd_natCard (Janko1.OrderCertificate.x * Janko1.OrderCertificate.y ^ 2)
end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
