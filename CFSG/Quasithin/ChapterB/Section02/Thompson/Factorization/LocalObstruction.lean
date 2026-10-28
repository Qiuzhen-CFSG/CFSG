module

public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.Envelope
public import CFSG.Quasithin.ChapterB.Section02.Thompson.RankGap
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.ChainCentralizerTwoCore
public import Theory.GroupTheory.MinimalNormalCover
public import Theory.Representation.BinaryOffender.ThreePrimeHyperplane

/-!
# The local obstruction in solvable Thompson factorization

The near-maximum elementary subgroup B supplies J(Q) <= J1(S). The
omega-center E = Omega1 Z(J1(S)) stabilizes the normal chain Q > J(Q) > 1,
so lies in O2(N) = Q. It therefore lies in the actual elementary envelope
constructed from the N-conjugates of B.

If N(E) fails to cover a self-centralizing odd minimal normal section of
N/I, normality of the envelope forces its centralizer into I. Its index-two
fixed-space bound then contradicts the 3-prime hyperplane theorem whenever
the chosen elementary actor lies outside I. All these deductions are proved;
the source's induction, odd-section selection and Frattini construction of
the displayed local subgroups remain explicit mathematical inputs.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153. The literal
Aschbacher–Smith 13.1.9 application is in FFContradiction.Factorization.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem omega_thompson_one_le_local_core (S Q N : Subgroup G)
    (hQ : IsPGroup 2 Q) (hQS : Q ≤ S) (hQN : Q ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G))
    (hself : N ⊓ centralizer (Q : Set G) ≤ Q) (hcore : N.pCoreIn 2 = Q)
    (hEN : omegaOneCenterAmbient (thompsonJ S 1) ≤ N)
    (hJ : elementaryAbelianMaxJ Q ≤ thompsonJ S 1) :
    omegaOneCenterAmbient (thompsonJ S 1) ≤ Q := by
  let E := omegaOneCenterAmbient (thompsonJ S 1)
  let J := elementaryAbelianMaxJ Q
  let : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  have hEJ : E ≤ centralizer (J : Set G) := by
    intro e he
    exact centralizer_le hJ (mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp he).2.2)
  have hQE : Q ≤ normalizer (E : Set G) := by
    apply hQS.trans
    apply le_normalizer_iff.mpr
    intro s hs e he
    have hmap : (thompsonJ S 1).map (MulAut.conj s).toMonoidHom = thompsonJ S 1 := by
      have hsmap := mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)
      change S.map (MulAut.conj s).toMonoidHom = S at hsmap
      rw [←thompsonJ_map_equiv,hsmap]
    have hm : E.map (MulAut.conj s).toMonoidHom = E := by
      dsimp [E]
      rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj s).injective]
      change omegaOneCenterAmbient ((thompsonJ S 1).map (MulAut.conj s).toMonoidHom) = _
      rw [hmap]
    exact hm ▸ mem_map_of_mem (MulAut.conj s).toMonoidHom he
  have hEQJ : E ⊓ Q ≤ J := by
    let : IsElementaryAbelian 2 (E ⊓ Q : Subgroup G) := IsElementaryAbelian.of_injective (Subgroup.inclusion (show E ⊓ Q ≤ E from inf_le_left))
      (Subgroup.inclusion_injective _)
    have hh := elementary_centralizer_maxJ_le_omegaCenter Q (E ⊓ Q) inf_le_right
      (inf_le_left.trans hEJ)
    intro e he
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hh he)).1
  have hcomm : ⁅E,Q⁆ ≤ J :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hQE)
      (le_normalizer_iff_commutator_le_right.mp (hEN.trans hNQ))).trans hEQJ
  rw [←hcore]
  exact Theory.GroupTheory.le_twoCore_of_relative_chain N Q J E hQN
    ((sSup_le fun _ hA => hA.1).trans hQN) hEN hNQ
    (hNQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q)) hQ hself hEJ hcomm
end CFSG.Quasithin.ChapterB
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The literal GLS envelope contains the omega-center; the local core and
near-maximum family supply all chain and rank premises. -/
theorem thompson_one_le_factorizationEnvelope_of_local_core
    (S Q N B : Subgroup G) (hr : 1 < twoRank S)
    (hB : B ∈ thompsonFamily S 1) (hBQ : B ≤ Q) (hQS : Q ≤ S)
    (hQ : IsPGroup 2 Q) (hQN : Q ≤ N) (hNQ : N ≤ normalizer (Q : Set G))
    (hself : N ⊓ centralizer (Q : Set G) ≤ Q) (hcore : N.pCoreIn 2 = Q)
    (hEN : omegaOneCenterAmbient (thompsonJ S 1) ≤ N) :
    omegaOneCenterAmbient (thompsonJ S 1) ≤ factorizationEnvelope Q B N := by
  have hb : twoRank S ≤ twoRank Q + 1 := by
    obtain ⟨D,hD⟩ := elementaryAbelianMaxSubgroups_nonempty Q
    have hc := hD.2.2 B hBQ hB.2.1
    rw [hB.2.2.2,elementaryAbelianMaxSubgroups_card_eq Q D hD,
      maxOrder_eq_two_pow_rank] at hc
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
    omega
  exact thompson_one_le_characteristic_envelope S Q N B hr hB hBQ hQS hNQ
    (omega_thompson_one_le_local_core S Q N hQ hQS hQN hNQ hself hcore hEN
      (maxJ_le_thompson_one_of_rank_gap Q S hQS hr hb))

/-- The local configuration selected in G.26.18(a) is impossible in a
3-prime group. The odd chief section and its noncoverage are explicit;
the chain, envelope, fixed-space bound and contradiction are proved. -/
theorem factorization_local_obstruction
    (S Q N B A I : Subgroup G) [(I.subgroupOf N).Normal]
    (hr : 1 < twoRank S) (hB : B ∈ thompsonFamily S 1)
    (hBQ : B ≤ Q) (hQS : Q ≤ S) (hQ : IsPGroup 2 Q) (hQN : Q ≤ N)
    (hNQ : N ≤ normalizer (Q : Set G))
    (hself : N ⊓ centralizer (Q : Set G) ≤ Q) (hcore : N.pCoreIn 2 = Q)
    (hEN : omegaOneCenterAmbient (thompsonJ S 1) ≤ N)
    (hBA : B ≤ A) (hA : IsElementaryAbelian 2 A) (hAN : A ≤ N)
    (hne : ¬ A ≤ I) (h3 : Nat.Coprime 3 (Nat.card N))
    (Y : Subgroup (N ⧸ I.subgroupOf N)) [Y.Normal]
    {r : ℕ} [Fact r.Prime] (hYr : IsPGroup r Y) (hor : Odd r) (hYne : Y ≠ ⊥)
    (hmin : ∀ D : Subgroup (N ⧸ I.subgroupOf N), D.Normal → D ≤ Y → D = ⊥ ∨ D = Y)
    (hCY : centralizer (Y : Set (N ⧸ I.subgroupOf N)) ≤ Y)
    (hcover : ¬ Y ≤ ((normalizer (omegaOneCenterAmbient (thompsonJ S 1) : Set G)).subgroupOf N).map
      (QuotientGroup.mk' (I.subgroupOf N))) : False := by
  let E := omegaOneCenterAmbient (thompsonJ S 1)
  let V := factorizationEnvelope Q B N
  let E' := E.subgroupOf N
  let V' := V.subgroupOf N
  let q := QuotientGroup.mk' (I.subgroupOf N)
  have hVN : V ≤ N := (factorizationEnvelope_le Q B N).trans hQN
  have hNV := factorizationEnvelope_normalized Q B N hNQ
  have hEV : E ≤ V := thompson_one_le_factorizationEnvelope_of_local_core
    S Q N B hr hB hBQ hQS hQ hQN hNQ hself hcore hEN
  let : V'.Normal := normal_subgroupOf_of_le_normalizer hNV
  let : IsElementaryAbelian 2 V := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 A := hA
  have hn : normalizer (E' : Set N) ≤ (normalizer (E : Set G)).subgroupOf N := by
    intro n hn e
    constructor
    · intro he
      exact (hn (⟨e,hEN he⟩ : N)).mp he
    · intro he
      have heN : e ∈ N := (N.le_normalizer n.property e).mpr (hEN he)
      exact (hn (⟨e,heN⟩ : N)).mpr he
  have hCI' : centralizer (V' : Set N) ≤ q.ker :=
    centralizer_le_kernel_of_normalizer_not_covering q (QuotientGroup.mk'_surjective _)
      Y hmin hCY E' V' (subgroupOf_mono N hEV)
      (fun hh => hcover (hh.trans (map_mono hn)))
  have hCI : N ⊓ centralizer (V : Set G) ≤ I := by
    intro n hn
    have hh : (⟨n,hn.1⟩ : N) ∈ centralizer (V' : Set N) := by
      intro v hv
      exact Subtype.ext (hn.2 v hv)
    exact (QuotientGroup.eq_one_iff (⟨n,hn.1⟩ : N)).mp (hCI' hh)
  exact hne (Representation.NormalElementaryQuotient.elementary_le_of_relative_three_prime_hyperplane
    N V I A hVN hAN hNV h3 hCI
    (twoCore_eq_bot_of_odd_minimal_selfCentralizing Y hYr hor hYne hmin hCY)
    (factorizationEnvelope_fixed_index S Q N B A hB hQS hBA hA))
end CFSG.Quasithin.ChapterB
