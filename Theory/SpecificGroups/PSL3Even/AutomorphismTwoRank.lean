module

public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.ElementaryKernel
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import GorensteinWalter.PGL2DihedralSylow
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Automorphism two-rank of binary PSL₃: the smallest field and lower bound

Conjugation embeds PSL₃(2ⁿ) into its automorphism group: Grün's lemma and
perfectness of SL₃ give the required trivial projective center. Thus the
already proved group rank 2n is a lower bound for the automorphism rank.

For n=1 the actual exceptional isomorphism identifies Aut(PSL₃(2)) with
PGL₂(7). Its dihedral Sylow two-subgroups give the matching upper bound.
Coefficient-field transport proves this for every field of order two.

The upper bound for larger binary fields still requires standard-automorphism
coverage and the rank calculation in the actual linear-field-graph subgroup.
Neither assertion is assumed or established by the small-field calculation.
The imported elementary-kernel lemma supplies the faithful fixed-group
reduction for that remaining calculation.

Source: Aschbacher–Smith, 16.1.7(3a), printed p.1172, and 16.3.9, p.1180;
the rank table in G.9, printed p.356, records m₂(Aut(PSL₃(2ⁿ))) = 2n.
The exceptional-isomorphism imports retain their ATLAS attribution and license.
-/

public section

open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Even

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private instance : Finite (GorensteinWalter.PGL2 (ZMod 7)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem rank_le_of_dihedral_sylow {G : Type*} [Group G] [Finite G]
    (h : GorensteinWalter.HasDihedralSylowTwo G) : primeRank 2 G ≤ 2 := by
  let P : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨m, _, ⟨e⟩⟩ := h P
  exact (P.primeRank_eq.trans (primeRank_equiv 2 e)).le.trans (dihedral_rank_le_two m)

private theorem pgl_seven_rank : primeRank 2 (GorensteinWalter.PGL2 (ZMod 7)) ≤ 2 := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) := by
    refine ⟨7, 1, by decide, by decide, by decide, ?_⟩
    norm_num
  exact rank_le_of_dihedral_sylow
    (GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model (ZMod 7) hodd)

private theorem aut_binary_rank :
    primeRank 2 (MulAut (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ≤ 2 :=
  (primeRank_equiv 2 PSL3Two.Automorphisms.pgl2SevenEquivAut).ge.trans pgl_seven_rank

/-- The actual inner action realizes rank 2n in the full automorphism group. -/
theorem le_automorphism_two_rank (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    2 * n ≤ primeRank 2 (MulAut (ProjectiveSpecialLinearGroup (Fin 3) F)) := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  have hc : center (ProjectiveSpecialLinearGroup (Fin 3) F) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (SpecialLinearGroup (Fin 3) F)
  rw [← two_rank F hn hF]
  exact primeRank_le_of_injective 2 MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot hc)

/-- The full automorphism group over the smallest field has two-rank exactly two. -/
theorem automorphism_two_rank_eq_of_card_two
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 2) :
    primeRank 2 (MulAut (ProjectiveSpecialLinearGroup (Fin 3) F)) = 2 := by
  apply le_antisymm
  · let := Fintype.ofFinite F
    let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    rw [primeRank_equiv 2 (MulAut.congr (Atlas.fieldEquivPSL 3 e))]
    exact aut_binary_rank
  · simpa using le_automorphism_two_rank F (n := 1) (by decide)
      (by simpa using hF)

end Matrix.PSL3Even
