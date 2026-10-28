module

public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.OddMinimal.ProperGeneration.Defs
public import Theory.Frattini.CoprimeSplitting
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Proper odd quotient pieces from a reducible Frattini section

Maschke's theorem gives two proper S-invariant subgroups B and C of
R = O_p(Q) with B ∨ C = R. Set D₁ = [B,a] and D₂ = [C,a].
Since [R,R] lies in Φ(R), R normalizes (D₁ ∨ D₂)Φ(R); the hypothesis
R = [R,a] makes this subgroup all of R. Frattini nongeneration therefore
gives D₁ ∨ D₂ = R, without a separate inversion calculation.

Coprime commutator idempotence gives Dᵢ = [Dᵢ,a]. Centrality of a in S
makes each Dᵢ S-invariant. Thus Jᵢ = DᵢS has a nontrivial normal
p-subgroup Dᵢ and a two-group quotient. If Jᵢ were Q, its odd core
would be Dᵢ = R, contradicting the properness of B or C.
The normal subgroup in the conclusion is the actual Dᵢ.subgroupOf Jᵢ.

The rank-one and nontrivial-core inputs are retained in the public source
interface, although the reducibility witness and full-commutator input
suffice for this construction. Actor centrality remains an explicit input.

Source: Aschbacher–Smith, E.5.2, printed p.243, minimal odd-member
reduction, and E.1.2(E1), printed p.210 (1 March 2004 manuscript).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {Q : Type*} [Group Q] [Finite Q]

private theorem cover_commutators {p : ℕ} [Fact p.Prime]
    (R a B C : Subgroup Q) (hR : IsPGroup p R)
    (hBR : B ≤ R) (hCR : C ≤ R) (hgen : B ⊔ C = R)
    (haB : a ≤ normalizer B) (haC : a ≤ normalizer C)
    (hfull : R = ⁅R,a⁆) : ⁅B,a⁆ ⊔ ⁅C,a⁆ = R := by
  let : Fact (IsPGroup p R) := ⟨hR⟩
  let D := ⁅B,a⁆ ⊔ ⁅C,a⁆
  let F := (frattini R).map R.subtype
  have hDR : D ≤ R := sup_le
    ((le_normalizer_iff_commutator_le_left.mp haB).trans hBR)
    ((le_normalizer_iff_commutator_le_left.mp haC).trans hCR)
  have hFR : F ≤ R := map_subtype_le _
  have hderived : ⁅R,R⁆ ≤ F := by
    rw [← map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (R := R) (p := p))
  have hnorm : R ≤ normalizer (D ⊔ F : Subgroup Q) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl (sup_le hDR hFR)).trans (hderived.trans le_sup_right))
  have hRpre : R ≤ commutatorPreimage R a (D ⊔ F) := by
    conv_lhs => rw [← hgen]
    exact sup_le (le_commutatorPreimage hBR (le_sup_left.trans le_sup_left))
      (le_commutatorPreimage hCR (le_sup_right.trans le_sup_left))
  have hRD : R ≤ D ⊔ F := by
    calc
      R = ⁅R,a⁆ := hfull
      _ ≤ ⁅commutatorPreimage R a (D ⊔ F),a⁆ := commutator_mono hRpre le_rfl
      _ ≤ D ⊔ F := commutator_commutatorPreimage_le R a (D ⊔ F) hnorm
  have htop : D.subgroupOf R ⊔ frattini R = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hDR, ← MonoidHom.range_eq_map, range_subtype]
    exact le_antisymm (sup_le hDR hFR) hRD
  have hdtop := frattini_nongenerating htop
  have hm := congrArg (Subgroup.map R.subtype) hdtop
  simpa only [map_subgroupOf_eq_of_le hDR, ← MonoidHom.range_eq_map, range_subtype]
    using hm

omit [Finite Q] in
private theorem normalizes_pair_commutator (B a S : Subgroup Q)
    (hB : S ≤ normalizer B) (ha : S ≤ normalizer a) :
    S ≤ normalizer (⁅B,a⁆ : Subgroup Q) := by
  rw [le_normalizer_iff]
  intro s hs x hx
  have hm : (⁅B,a⁆).map (MulAut.conj s).toMonoidHom ≤ ⁅B,a⁆ := by
    rw [map_commutator]
    apply commutator_mono
    · rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp (hB hs) b).mp hb
    · rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp (ha hs) b).mp hb
  exact hm (mem_map_of_mem (MulAut.conj s).toMonoidHom hx)

private theorem commutator_full {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (B a : Subgroup Q) (hB : IsPGroup p B) (ha : IsPGroup 2 a)
    (hn : a ≤ normalizer B) : ⁅B,a⁆ = ⁅⁅B,a⁆,a⁆ := by
  have hc : Nat.Coprime (Nat.card a) (Nat.card B) :=
    IsPGroup.coprime_card_of_ne 2 p hp.symm a B ha hB
  have hi := commutator_closure_coprime_idempotent B (a : Set Q)
    (by simpa only [closure_eq] using hn) (by
      intro x hx
      have hd : orderOf x ∣ Nat.card a := by
        simpa only [orderOf_mk] using orderOf_dvd_natCard (⟨x,hx⟩ : a)
      exact hc.of_dvd_left hd)
  simpa only [closure_eq] using hi.symm

private theorem piece_of_full_commutator {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Sylow 2 Q) (a D : Subgroup Q) (haS : a ≤ S)
    (hD : IsPGroup p D) (hn : (S : Subgroup Q) ≤ normalizer D)
    (hne : D ≠ ⊥) (hproper : D ≠ pCore p Q) (hfull : D = ⁅D,a⁆) :
    OddQuotientPiece p a S (D ⊔ S) := by
  let J : Subgroup Q := D ⊔ S
  have hDJ : D ≤ J := le_sup_left
  have hSJ : (S : Subgroup Q) ≤ J := le_sup_right
  have hnorm : J ≤ normalizer D := sup_le D.le_normalizer hn
  have hJproper : J ≠ ⊤ := by
    intro ht
    let : D.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (ht ▸ hnorm))
    have hquot : IsPGroup 2 (Q ⧸ D) :=
      isPGroup_quotient_of_sup_eq_top D S S.isPGroup' ht
    exact hproper (odd_core_of_normal_p_subgroup hp D hD hquot).symm
  let N := D.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hN : IsPGroup p N := hD.comap_subtype
  have hquot : IsPGroup 2 (J ⧸ N) := by
    apply isPGroup_quotient_of_sup_eq_top N ((S : Subgroup Q).subgroupOf J)
      S.isPGroup'.comap_subtype
    exact codisjoint_iff.mp (codisjoint_subgroupOf_sup D S)
  refine ⟨hSJ, hJproper, N, inferInstance, hN, hquot, ?_, ?_⟩
  · intro hz
    apply hne
    have hm := congrArg (Subgroup.map J.subtype) hz
    simpa only [N, map_subgroupOf_eq_of_le hDJ, Subgroup.map_bot] using hm
  · apply map_injective J.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (haS.trans hSJ),
      show N.map J.subtype = D from map_subgroupOf_eq_of_le hDJ]
    exact hfull

private theorem quotient_cover_of_invariant_cover {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (S : Sylow 2 Q) (a B C : Subgroup Q)
    (ha : IsPGroup 2 a) (haS : a ≤ S)
    (hcentral : (S : Subgroup Q) ≤ centralizer (a : Set Q))
    (hq : IsPGroup 2 (Q ⧸ pCore p Q))
    (hfull : pCore p Q = ⁅pCore p Q,a⁆)
    (hBR : B ≤ pCore p Q) (hCR : C ≤ pCore p Q)
    (hBproper : B ≠ pCore p Q) (hCproper : C ≠ pCore p Q)
    (hSB : (S : Subgroup Q) ≤ normalizer B)
    (hSC : (S : Subgroup Q) ≤ normalizer C) (hgen : B ⊔ C = pCore p Q) :
    ∃ J₁ J₂ : Subgroup Q,
      OddQuotientPiece p a S J₁ ∧ OddQuotientPiece p a S J₂ ∧ J₁ ⊔ J₂ = ⊤ := by
  have hp2 : p ≠ 2 := by intro he; subst p; norm_num at hp
  have hBa := le_normalizer_iff_commutator_le_left.mp (haS.trans hSB)
  have hCa := le_normalizer_iff_commutator_le_left.mp (haS.trans hSC)
  have hcover := cover_commutators (pCore p Q) a B C pCore_isPGroup hBR hCR hgen
    (haS.trans hSB) (haS.trans hSC) hfull
  have hD₁proper : ⁅B,a⁆ ≠ pCore p Q := by
    intro he
    exact hBproper (le_antisymm hBR (he ▸ hBa))
  have hD₂proper : ⁅C,a⁆ ≠ pCore p Q := by
    intro he
    exact hCproper (le_antisymm hCR (he ▸ hCa))
  have hD₁ne : ⁅B,a⁆ ≠ ⊥ := by
    intro hz
    exact hD₂proper (by simpa only [hz, bot_sup_eq] using hcover)
  have hD₂ne : ⁅C,a⁆ ≠ ⊥ := by
    intro hz
    exact hD₁proper (by simpa only [hz, sup_bot_eq] using hcover)
  have hSa : (S : Subgroup Q) ≤ normalizer a :=
    hcentral.trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨⁅B,a⁆ ⊔ S, ⁅C,a⁆ ⊔ S, ?_, ?_, ?_⟩
  · exact piece_of_full_commutator hp2 S a _ haS
      (pCore_isPGroup.to_le (hBa.trans hBR))
      (normalizes_pair_commutator B a S hSB hSa) hD₁ne hD₁proper
      (commutator_full hp2 B a (pCore_isPGroup.to_le hBR) ha (haS.trans hSB))
  · exact piece_of_full_commutator hp2 S a _ haS
      (pCore_isPGroup.to_le (hCa.trans hCR))
      (normalizes_pair_commutator C a S hSC hSa) hD₂ne hD₂proper
      (commutator_full hp2 C a (pCore_isPGroup.to_le hCR) ha (haS.trans hSC))
  · calc
      (⁅B,a⁆ ⊔ S) ⊔ (⁅C,a⁆ ⊔ S) = (⁅B,a⁆ ⊔ ⁅C,a⁆) ⊔ S := by rw [sup_sup_sup_comm, sup_idem]
      _ = pCore p Q ⊔ S := by rw [hcover]
      _ = ⊤ := by simpa only [sup_comm] using S.sup_eq_top_of_quotient_isPGroup _ hq
/-- Reducibility of the odd Frattini section produces two genuine proper
quotient pieces containing the prescribed Sylow two-subgroup. -/
public theorem odd_quotient_pieces_of_reducible_frattini {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p)
    (S : Sylow 2 Q) (a : Subgroup Q)
    (hq : IsPGroup 2 (Q ⧸ pCore p Q)) (_hRne : pCore p Q ≠ ⊥)
    (ha : IsElementaryAbelian 2 a) (haS : a ≤ S) (_harank : Group.rank a = 1)
    (hfull : pCore p Q = ⁅pCore p Q,a⁆)
    (hcentral : (S : Subgroup Q) ≤ centralizer (a : Set Q))
    (U : Subgroup Q) (hUnormal : U.Normal) (hUR : U ≤ pCore p Q)
    (hUzero : ¬ U ≤ (frattini (pCore p Q)).map (pCore p Q).subtype)
    (hUfull : U ⊔ (frattini (pCore p Q)).map (pCore p Q).subtype ≠ pCore p Q) :
    ∃ J₁ J₂ : Subgroup Q,
      OddQuotientPiece p a S J₁ ∧ OddQuotientPiece p a S J₂ ∧ J₁ ⊔ J₂ = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  let : U.Normal := hUnormal
  let : IsElementaryAbelian 2 a := ha
  have hcop : Nat.Coprime p (Nat.card S) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact hpodd.coprime_two_right.pow_right n
  obtain ⟨B, C, hBR, hCR, hBproper, hCproper, hSB, hSC, hgen⟩ :=
    exists_proper_invariant_frattini_cover (pCore p Q) S U pCore_isPGroup
      hcop hUR hUzero hUfull
  exact quotient_cover_of_invariant_cover hpodd S a B C
    (IsElementaryAbelian.isPGroup 2 a) haS hcentral hq hfull
    hBR hCR hBproper hCproper hSB hSC hgen

end CFSG.Quasithin.ChapterE
