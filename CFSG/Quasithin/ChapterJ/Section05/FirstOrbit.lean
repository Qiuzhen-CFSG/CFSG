module

public import CFSG.Quasithin.ChapterJ.Section05.Normalizer

/-!
# The actual first suborbit in J.5.3

The index-two extension MQ of the marked first parabolic has order40960,
which cannot divide the full Ree order. Thus the original Q has an element
g outside F. Index two makes g normalize M and puts its square in M.
Self-normalization of F, already proved from the original Q₅ centralizer,
then gives the two-point stabilizer M and setwise stabilizer MQ. Their
orders give the1755-point suborbit and2304-point remainder.

Only genuine earlier J.4 geometry is retained: recognition of F, the marked
maximal first parabolic, and its index-two extension by the original Q.
Source: Aschbacher–Smith J.5.3 and the opening of J.5.4, printed pp.445–446.
-/

public section
noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] (d:LocalSetup G)

/-- The literal original Q constructs the first suborbit and both stabilizers. -/
theorem source_first_suborbit (B5:Sylow 5 d.toTypeRuSetup.H) (F M:Subgroup G)
    (h5:Q₅ d B5≤F) (e:F≃*ReeF4.Model 0) (hMF:M⋖F) (hc:Nat.card M=20480)
    (hi:M.relIndex (M⊔d.toTypeRuSetup.Q)=2) :
    ∃g:G,g∈d.toTypeRuSetup.Q ∧ g∉F ∧
      Nat.card (Cosets F)=4060 ∧
      stabilizer F (g•basePoint F)=M.subgroupOf F ∧
      Nat.card (orbit F (g•basePoint F))=1755 ∧
      stabilizer G ({basePoint F,g•basePoint F}:Set (Cosets F))=M⊔d.toTypeRuSetup.Q ∧
      (({basePoint F}:Set (Cosets F))∪orbit F (g•basePoint F))ᶜ.ncard=2304 := by
  let J:=M⊔d.toTypeRuSetup.Q
  have hMJ:M≤J:=le_sup_left
  have hJ:Nat.card J=40960:=by
    have hh:=(M.subgroupOf J).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hMJ).toEquiv] at hh
    change Nat.card M*M.relIndex J=Nat.card J at hh
    rw [hc,hi] at hh
    exact hh.symm
  have hF:Nat.card F=35942400:=
    (Nat.card_congr e.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card
  have hQ:¬d.toTypeRuSetup.Q≤F:=by
    intro hQ
    have hh:=card_dvd_of_le (show J≤F from sup_le hMF.le hQ)
    rw [hJ,hF] at hh
    norm_num at hh
  obtain ⟨g,hgQ,hgF⟩:=SetLike.not_le_iff_exists.mp hQ
  have hgJ:g∈J:=(show d.toTypeRuSetup.Q≤J from le_sup_right) hgQ
  let :(M.subgroupOf J).Normal:=normal_of_index_eq_two hi
  have hnM:g∈normalizer (M:Set G):=le_normalizer_of_normal_subgroupOf hMJ hgJ
  have hnF:g∉normalizer (F:Set G):=by rwa [source_normalizer_eq_self d B5 F h5 e]
  have hpow:g^2∈M:=(M.subgroupOf J).sq_mem_of_index_two hi (⟨g,hgJ⟩:J)
  have hswap:g•(g•basePoint F)=basePoint F:=by
    rw [← mul_smul,← pow_two]
    exact (show g^2∈stabilizer G (basePoint F) from (stabilizer_quotient F).symm ▸ hMF.le hpow)
  have hgen:M⊔zpowers g=J:=sup_zpowers_eq_of_relIndex_prime hMJ Nat.prime_two hi hgJ
    (fun hm=>hgF (hMF.le hm))
  have hp:stabilizer G ({basePoint F,g•basePoint F}:Set (Cosets F))=J:=by
    rw [stabilizer_pair_eq_sup rfl hswap,stabilizer_smul_eq_stabilizer_map_conj,
      stabilizer_quotient,inf_conjugate_eq_of_covBy hMF hnM hnF,hgen]
  exact ⟨g,hgQ,hgF,source_coset_card ⟨d.toTypeRuSetup⟩ F e,
    stabilizer_coset_eq_of_covBy hMF hnM hnF,source_first_orbit_card e hMF hc hnM hnF,
    hp,source_remainder_card ⟨d.toTypeRuSetup⟩ e hMF hc hnM hnF⟩

end CFSG.Quasithin.ChapterJ.Section05
