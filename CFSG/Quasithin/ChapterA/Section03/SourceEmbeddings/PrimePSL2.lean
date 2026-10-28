module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups

/-!
# A.3.12 inside odd-prime PSL₂

Adjoin the intersection of the original full Sylow with the containing
component. If the smaller local component is proper, this nonsolvable join
is proper too. Dickson's classification makes the join A₅, and its solvable
proper subgroups force the smaller component to be the whole join. Thus the
original Sylow intersection lies in the actual A₅ subgroup. Its order rules
out an ambient factor of eight, giving the precise prime congruence in (8).

This proves the proper odd-prime branch, including the actual embedded pair
and both congruences, from the original local C-component condition. The
last theorem applies it to the literal ambient two-core quotient in 1.2.4.

Source: Aschbacher–Smith A.3.12(8), printed pp.47–48; C.5.13, p.163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The proper prime-field branch constructs the actual A₅ model and the
source's exceptional prime congruences, without a smaller-model premise. -/
theorem proper_primePSL2_models
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hne : B ≠ L) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL L 2 p) :
    A312ExceptionalPrime p ∧ LocalModels.IsAlternating B 5 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL.subnormal
  let J := B ⊔ (S : Subgroup L).map L.subtype
  have hST : (S : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hS, subgroupOf_map_subtype]
    exact inf_le_left
  have hJL : J ≤ L := sup_le hBL (map_subtype_le _)
  have hBJ : (B.subgroupOf J).IsCComponent :=
    hB.subgroupOf_of_le le_sup_left (sup_le le_sup_left (hST.trans le_sup_right))
  have hJne : J ≠ L := by
    intro he
    rw [he] at hBJ
    exact hne (le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hBJ)))
  let D := (J.subgroupOf L).map e.toMonoidHom
  let i : J ≃* D := (subgroupOfEquivOfLe hJL).symm.trans
    ((J.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)
  have hDne : D ≠ ⊤ := by
    intro he
    have ht : J.subgroupOf L = ⊤ := by
      apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
      rw [map_top_of_surjective _ e.surjective]
      exact he
    exact hJne (le_antisymm hJL (subgroupOf_eq_top.mp ht))
  have hDns : ¬ Group.IsSolvable D := by
    intro hs
    let := hs
    let : Group.IsSolvable J :=
      Group.isSolvable_of_isSolvable_injective (f := i.toMonoidHom) i.injective
    exact hBJ.not_isSolvable inferInstance
  obtain ⟨_, hdiv, ⟨d⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five
    ho hF D hDne hDns
  let j : J ≃* alternatingGroup (Fin 5) := i.trans d
  have hBJtop : B.subgroupOf J = ⊤ := by
    by_contra hproper
    exact hBJ.not_isSolvable
      (alternatingGroup.isSolvable_subgroup_of_equiv_five j (B.subgroupOf J) hproper)
  have heBJ : B = J := le_antisymm le_sup_left (subgroupOf_eq_top.mp hBJtop)
  have hfive : p ^ 2 % 5 = 1 := by
    have hs : 1 ≤ p ^ 2 := by nlinarith [hp.two_le]
    have hd := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have height : p % 8 = 3 ∨ p % 8 = 5 := by
    rw [← hF]
    apply Theory.PSL2.mod_eight_of_not_eight_dvd_card (hF ▸ ho)
    intro hd
    let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hSD : (S' : Subgroup _) ≤ D := map_mono (by
      intro s hs
      exact (show (S : Subgroup L).map L.subtype ≤ J from le_sup_right)
        (mem_map_of_mem L.subtype hs))
    have h8 : 8 ∣ Nat.card D := (S'.pow_dvd_card_of_pow_dvd_card (n := 3) hd).trans
      (card_dvd_of_le hSD)
    have hcard : Nat.card D = 60 := by
      rw [Nat.card_congr d.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hcard] at h8
    norm_num at h8
  exact ⟨⟨hp, ho, hfive, height⟩, by rw [heBJ]; exact ⟨j⟩⟩

/-- The actual embedded pair satisfies A.3.12(1) or (8). -/
theorem embedding_of_primePSL2
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL L 2 p) : A312Embedding B L := by
  by_cases he : B = L
  · exact .one he
  obtain ⟨hprime, hsmall⟩ := proper_primePSL2_models T hB hL hBL he hp ho hmodel
  exact .eight (.inr ⟨p, hprime, hsmall, hmodel⟩)

/-- Apply the proper prime-field classification to the exact images used
by 1.2.4, retaining the original ambient two-core quotient map. -/
theorem twoCore_embedding_of_primePSL2
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (L.map (QuotientGroup.mk' (pCore 2 G))) 2 p) :
    A312Embedding (B.map (QuotientGroup.mk' (pCore 2 G)))
      (L.map (QuotientGroup.mk' (pCore 2 G))) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  apply embedding_of_primePSL2
    (T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
    ?_ (hL.map_quotient (pCore 2 G)) (map_mono hBL) hp ho hmodel
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
