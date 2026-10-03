module
public import Stellmacher.SectionNine.DistanceOneVstarResidualContainment
public import Theory.GroupTheory.NormalCenterQuotient
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products

/-!
# Order and self-centralization of the selected terminal eight

For an elementary subgroup U of order eight in the exact distance-one Vstar,
the stated selection properties imply that its terminal normalizer has order
192 and its terminal centralizer equals U. The input keeps the actual ambient
context, residual normality, initial-center invariance, failure of terminal-core
invariance, and self-centralization inside Vstar explicit.

Vstar joined with the initial center has order64 and lies in the normalizer.
An actual cubic residual actor also lies there. Since a core element moves U,
the normalizer is proper in the order384 terminal stabilizer, forcing order192.
Its intersection with the order64 terminal core is exactly the order32 Vstar.
The actual terminal map onto SL₂(2) consequently restricts to a surjection
from this normalizer with kernel Vstar.

The normalizer's centralizer of U is normal and has no order-three element:
every cubic terminal element lies in the actual two-residual, while a residual
order-three actor fixes only the order-two center of Vstar, too small to contain
U. Cauchy's theorem and Lagrange's theorem make this centralizer a two-group.
Its normal image in SL₂(2) is trivial, so it lies in Vstar; the supplied
intrinsic self-centralization then identifies it with U. Finally every
terminal element centralizing U normalizes it, giving the full terminal
centralizer equality.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48. This lower leaf
supplies the order and faithful action needed for the terminal S4 quotient;
no terminal normalizer model is assumed.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven
open scoped Pointwise
universe u

private theorem cubic_mem_twoResidual {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (x : P) (hx : x ^ 3 = 1) : x ∈ twoResidualSubgroup P := by
  apply Subgroup.mem_sInf.mpr
  rintro N ⟨hN, n, hi⟩
  let : N.Normal := hN
  let q := QuotientGroup.mk' N
  have h3 : orderOf (q x) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (q x) ∣ 2 ^ n := by
    rw [← hi, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard (q x)
  have hone : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_right n) h3 h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)

private theorem normal_two_subgroup_sl2_eq_bot (P : Subgroup SL2Two) [P.Normal]
    (hp : IsPGroup 2 P) : P = ⊥ := by
  have hcard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hd := P.card_subgroup_dvd_card
  rw [hcard] at hd
  have hcop : Nat.Coprime (Nat.card P) 3 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card P ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hc | hc
  · exact Subgroup.card_eq_one.mp hc
  · apply le_antisymm _ bot_le
    exact (Subgroup.central_of_normal_card_two P hc).trans
      (SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two
        (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)).le

/-- The actual selected eight has terminal normalizer of order192 and is
self-centralizing in the terminal stabilizer. -/
public theorem distance_one_terminal_eight_order_and_centralizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (U : Subgroup G) (hElem : IsElementaryAbelian 2 U) (hUcard : Nat.card U = 8)
    (hUV : U ≤ conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a'))
    (hUE : NormalIn U (EAt ctx.Γ ctx.criticalPath.a'))
    (hZaN : ZAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (U : Set G))
    (hQnot : ¬ QAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (U : Set G))
    (hself : conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ⊓ Subgroup.centralizer (U : Set G) = U) :
    Nat.card (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) = 192 ∧
      GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.centralizer (U : Set G) = U := by
  classical
  let := hElem
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let NU := Subgroup.normalizer (U : Set G)
  let N := terminal ⊓ NU
  have hEV : E ≤ terminal := by
    simpa only [E, terminal, EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoResidualIn_le terminal
  have hEN : E ≤ NU := (Subgroup.normal_subgroupOf_iff_le_normalizer hUE.1).mp hUE.2
  have hVE : V ≤ E := distance_one_vstar_le_terminal_residual ctx hlength hfaithful hlocal
  have hcont := distance_one_vstar_containments ctx.toLocalContext hlength
  have hVT : V ≤ terminal := hcont.1.1
  have hVQ : V ≤ Q := hcont.2.1
  have hVN : V ≤ N := le_inf hVT (hVE.trans hEN)
  have hQT : Q ≤ T := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change QAt ctx.Γ ctx.criticalPath.a' ≤ T
    rw [hend]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hTterminal : T ≤ terminal := by
    have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
      rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
      congr 1
      exact Fin.ext hlength
    change T ≤ GAt ctx.Γ ctx.criticalPath.a'
    rw [hend]
    exact (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1
  have hZaT : Za ≤ T := by
    change ZAt ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a ≤ T
    rw [← hlocal.2.2.2.1]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hQcard : Nat.card Q = 64 := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) Q T bot_le hQT
    simp only [Subgroup.relIndex_bot_left] at hh
    have hi : Q.relIndex T = 2 := distance_one_terminal_core_index_in_sylow ctx.toLocalContext hlength hlocal
    rw [hi, hlocal.2.2.1] at hh
    omega
  have hVcard : Nat.card V = 32 := distance_one_vstar_card ctx.toLocalContext hlocal
  have hseedcard := (distance_one_seed_data ctx.toLocalContext hlength hfaithful hlocal).1
  change Nat.card (Za ⊓ Q : Subgroup G) = 8 at hseedcard
  have hZacard : Nat.card Za = 16 := hfaithful.1
  have hseed : Za ⊓ Q ≤ V := by
    intro x hx
    exact Subgroup.subset_closure ⟨1, ⟨x, hx⟩, by simp⟩
  have hinf : V ⊓ Za = Za ⊓ Q := by
    rw [inf_comm]
    exact le_antisymm (inf_le_inf_left Za hVQ) (le_inf inf_le_left hseed)
  have hn : terminal ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mp hcont.1.2
  have hjoincard : Nat.card (V ⊔ Za : Subgroup G) = 64 := by
    have hh := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes V Za
      (hZaT.trans (hTterminal.trans hn))
    rw [hVcard, hZacard, hinf, hseedcard] at hh
    omega
  have hjoinN : V ⊔ Za ≤ N := sup_le hVN (le_inf (hZaT.trans hTterminal) hZaN)
  obtain ⟨hz, hzcard, ⟨g, hg, hgorder⟩, _⟩ := distance_one_vstar_three_action ctx hlength hfaithful hlocal
  have h64div : 64 ∣ Nat.card N := hjoincard ▸ Subgroup.card_dvd_of_le hjoinN
  have h3div : 3 ∣ Nat.card N := by
    have hh := orderOf_dvd_natCard (⟨g, hEV hg, hEN hg⟩ : N)
    rw [← Subgroup.orderOf_coe, hgorder] at hh
    exact hh
  have h192div : 192 ∣ Nat.card N := (by decide : Nat.Coprime 64 3).mul_dvd_of_dvd_of_dvd h64div h3div
  have h192le : 192 ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos h192div
  have hTcard : Nat.card terminal = 384 := distance_one_terminal_card ctx.toLocalContext hlength hlocal
  have hNindex : 2 ≤ N.relIndex terminal := by
    have hpos : 0 < N.relIndex terminal := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N.subgroupOf terminal))
    have hne : N.relIndex terminal ≠ 1 := by
      intro heq
      have hle := Subgroup.relIndex_eq_one.mp heq
      exact hQnot ((hQT.trans hTterminal).trans (hle.trans inf_le_right))
    omega
  have hNcard : Nat.card N = 192 := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) N terminal bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at hh
    rw [hTcard] at hh
    nlinarith
  have hQN : Q ⊓ NU = V := by
    have hle : V ≤ Q ⊓ NU := le_inf hVQ (hVE.trans hEN)
    have hlow : 32 ≤ Nat.card (Q ⊓ NU : Subgroup G) := by
      simpa only [hVcard] using Subgroup.card_le_of_le hle
    have hindex : 2 ≤ (Q ⊓ NU).relIndex Q := by
      have hpos : 0 < (Q ⊓ NU).relIndex Q := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (Q ⊓ NU).subgroupOf Q))
      have hne : (Q ⊓ NU).relIndex Q ≠ 1 := by
        intro heq
        exact hQnot ((Subgroup.relIndex_eq_one.mp heq).trans inf_le_right)
      omega
    apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ NU) Q bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at hh
    rw [hQcard] at hh
    rw [hVcard]
    nlinarith
  obtain ⟨projection, hsurj, hker⟩ := hlocal.2.1
  change terminal →* SL2Two at projection
  change Function.Surjective projection at hsurj
  change projection.ker = Q.subgroupOf terminal at hker
  let f : N →* SL2Two := projection.comp (Subgroup.inclusion inf_le_left)
  have hfker : f.ker = V.subgroupOf N := by
    ext x
    change projection ⟨(x : G), x.property.1⟩ = 1 ↔ (x : G) ∈ V
    rw [← MonoidHom.mem_ker, hker]
    constructor
    · intro hx
      exact hQN ▸ ⟨hx, x.property.2⟩
    · exact fun hx => hVQ hx
  have hVncard : Nat.card (V.subgroupOf N) = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv).trans hVcard
  have hfrange : Nat.card f.range = 6 := by
    have hh := f.ker.card_mul_index
    rw [Subgroup.index_ker, hfker, hVncard, hNcard] at hh
    omega
  have hfsur : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hfrange]
    exact (SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)).le
  let Un := U.subgroupOf N
  have hUN : U ≤ N := hUV.trans hVN
  let : Un.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).mpr inf_le_right
  let K := Subgroup.centralizer (Un : Set N)
  have hKnormal : K.Normal := inferInstance
  have hKno3 : ¬ 3 ∣ Nat.card K := by
    intro hdiv
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hdiv
    let a : G := x
    have ha3 : a ^ 3 = 1 := by
      have hpow : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      exact congrArg (fun v : K => ((v : N) : G)) hpow
    have haorder : orderOf a = 3 := by
      change orderOf ((x : N) : G) = 3
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hx
    have haT : a ∈ terminal := x.val.property.1
    have haE : a ∈ E := by
      have hm := cubic_mem_twoResidual terminal ⟨a, haT⟩ (Subtype.ext ha3)
      have he : E = (twoResidualSubgroup terminal).map terminal.subtype := by
        simp only [E, terminal, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
          GAt, CosetGraphContext.stabilizer, twoResidualIn, twoResidualAmbient]
        rfl
      rw [he]
      exact Subgroup.mem_map_of_mem terminal.subtype hm
    have hfix := (distance_one_vstar_residual_centralizer ctx hlength hfaithful hlocal hz).2
      a haE haorder
    have hUZ : U ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
      intro u hu
      apply hfix u (hUV hu)
      have hh := Subgroup.mem_centralizer_iff.mp x.property (⟨u, hUN hu⟩ : N) hu
      exact (congrArg Subtype.val hh).symm
    have hh := Subgroup.card_le_of_le hUZ
    rw [hUcard, hzcard] at hh
    omega
  have hKp : IsPGroup 2 K := by
    have hd : Nat.card K ∣ 192 := hNcard ▸ K.card_subgroup_dvd_card
    have hc : Nat.Coprime (Nat.card K) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hKno3).symm
    exact IsPGroup.of_card_dvd_pow (n := 6) (hc.dvd_mul_right.mp hd)
  let : (K.map f).Normal := hKnormal.map f hfsur
  have hKmap : K.map f = ⊥ := normal_two_subgroup_sl2_eq_bot _ (hKp.map f)
  have hKV : K ≤ V.subgroupOf N := by
    rw [← hfker]
    exact (Subgroup.map_eq_bot_iff K).mp hKmap
  refine ⟨hNcard, le_antisymm ?_ ?_⟩
  · intro x hx
    have hxN : x ∈ N := ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
    have hxK : (⟨x, hxN⟩ : N) ∈ K := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro u hu
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 u hu)
    exact hself ▸ ⟨hKV hxK, hx.2⟩
  · refine le_inf (hUV.trans hVT) ?_
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact setLike_mul_comm hy hx

end Stellmacher.SectionNine
