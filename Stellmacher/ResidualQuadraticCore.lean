module
public import Stellmacher.MainDefs
public import Stellmacher.SectionsOneToFourDefs
public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Theory.GroupTheory.Hall.OddSylowComplement

/-!
# Residually quadratic subgroups of characteristic-two groups

Let E≤P be finite and solvable, with P of characteristic two. If the
two-residual of E acts quadratically on O2(P), then E is a two-group.

An odd Hall complement of a Sylow two-subgroup of E lies in its
two-residual: its image in each defining two-group quotient is trivial.
The odd complement's quadratic action on O2(P) is trivial by coprime
commutator idempotence. Characteristic two then puts it in O2(P), where
its odd order forces triviality. The complementary Sylow is therefore E.

This is the contradiction used after (9.1)(3) when the extracted product
V is assumed abelian, in Stellmacher, Journal of Algebra 190 (1997), p.46.
The theorem retains the exact ambient core and residual and does not
assume that E is normal in P. Source: refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher

private theorem odd_subgroup_le_residual
    {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (U : Subgroup E) (hU : Odd (Nat.card U)) : U ≤ twoResidualSubgroup E := by
  intro u hu
  rw [twoResidualSubgroup,Subgroup.mem_sInf]
  rintro N ⟨hN,n,hn⟩
  let _ := hN
  let f := QuotientGroup.mk' N
  have hquot : IsPGroup 2 (E ⧸ N) := IsPGroup.of_card
    (by simpa only [Subgroup.index_eq_card] using hn)
  have hI := hquot.to_subgroup (U.map f)
  have hnot : ¬ 2 ∣ Nat.card (U.map f) := fun hh =>
    hU.not_two_dvd_nat (hh.trans (U.card_map_dvd f))
  have hcard := hI.card_eq_or_dvd.resolve_right hnot
  have hbot : U.map f = ⊥ := Subgroup.card_eq_one.mp hcard
  have hu' : u ∈ f.ker := (Subgroup.map_eq_bot_iff U).mp hbot hu
  simpa only [f,QuotientGroup.ker_mk'] using hu'

public theorem isPGroup_of_residual_quadratic_on_core
    {G : Type*} [Group G] [Finite G] (P E : Subgroup G)
    (hEP : E ≤ P) (hsolv : Group.IsSolvable E)
    (hchar : IsCharacteristicTwoType P)
    (hquad : ⁅⁅twoCoreAmbient P,twoResidualAmbient E⁆,twoResidualAmbient E⁆ = ⊥) :
    IsPGroup 2 E := by
  classical
  let S : Sylow 2 E := default
  obtain ⟨U,hUodd,hUcompl⟩ := Subgroup.exists_odd_complement_sylow_two hsolv S
  let Ua := U.map E.subtype
  let Q := twoCoreAmbient P
  have hUR : Ua ≤ twoResidualAmbient E := Subgroup.map_mono (odd_subgroup_le_residual E U hUodd)
  have hUaP : Ua ≤ P := (Subgroup.map_subtype_le _).trans hEP
  have hQn : (Q.subgroupOf P).Normal := by
    change (((pCore 2 P).map P.subtype).subgroupOf P).Normal
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hnorm : Ua ≤ Subgroup.normalizer (Q : Set G) := hUaP.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hQn)
  have hQp : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := P)).map P.subtype
  have hodd : Odd (Nat.card Ua) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hUodd
  have hcop : Nat.Coprime (Nat.card Ua) (Nat.card Q) := by
    obtain ⟨n,hn⟩ := hQp.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hquadU : ⁅⁅Q,Ua⁆,Ua⁆ = ⊥ := bot_unique
    ((Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hUR) hUR).trans_eq hquad)
  have hQsolv : Group.IsSolvable Q := by
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let _ := hQp.isNilpotent
    infer_instance
  have hcent := Subgroup.commutator_eq_bot_of_coprime_quadratic Q Ua hnorm hQsolv hcop hquadU
  have hUQ : Ua ≤ Q := by
    intro u hu
    have huP : (⟨u,hUaP hu⟩ : P) ∈ Subgroup.centralizer (pCore 2 P : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply P.subtype_injective
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcent) hu) q
        (Subgroup.mem_map_of_mem P.subtype hq)
    exact Subgroup.mem_map_of_mem P.subtype (hchar huP)
  have hUaCard : Nat.card Ua = 1 := (hQp.to_le hUQ).card_eq_or_dvd.resolve_right
    hodd.not_two_dvd_nat
  have hUbot : U = ⊥ := Subgroup.card_eq_one.mp (by
    rw [← Subgroup.card_map_of_injective (K := U) E.subtype_injective]
    exact hUaCard)
  have hS : (S : Subgroup E) = ⊤ := by simpa only [hUbot,sup_bot_eq] using hUcompl.sup_eq_top
  have hp : IsPGroup 2 (⊤ : Subgroup E) := hS ▸ S.isPGroup'
  exact hp.of_equiv Subgroup.topEquiv
end Stellmacher
