module

public import Stellmacher.MainDefs
public import FeitThompson.PCore.CentralizerControl

/-!
# Detecting a two-local odd core in an involution centralizer

In a finite N2 group, a two-local subgroup with nontrivial odd core supplies
an involution whose full centralizer also has nontrivial odd core. This is
the first reduction of alternative (e) in Stellmacher's Theorem 2 to the
global analysis of involution centralizers. It needs neither simplicity nor
an assumption on the normalizer of the Sylow center.

Write the two-local subgroup as U = N_G(Q), choose a central involution t
of the nontrivial two-group Q, and put L = C_G(t). The odd core of U
centralizes Q, so it lies in L and is normal in C_L(Q), since C_L(Q) lies
in U. Solvability of L follows from the N2 hypothesis. The proved
solvable-centralizer bound then sends the odd core of C_L(Q) into that of
L. Injectivity of the subgroup inclusions preserves nontriviality.

Source: Kurzweil–Stellmacher, The Theory of Finite Groups, §12.1.2 and
§8.2.13. The source's core-detection argument is used without the extra Z
hypothesis assumed for the later signalizer-functor reduction.
-/

namespace Stellmacher.Recognition

private theorem central_involution
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ∃ t : G, t ∈ Q ∧ t ∈ Subgroup.centralizer (Q : Set G) ∧ orderOf t = 2 := by
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  let : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hcenter : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
  have hdiv : 2 ∣ Nat.card (Subgroup.center Q) := by
    obtain ⟨n, hn, hcard⟩ := hcenter.nontrivial_iff_card.mp inferInstance
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  refine ⟨z.val.val, z.val.property, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg (fun x : Q => (x : G))
      ((Subgroup.mem_center_iff.mp z.property) ⟨q, hq⟩)
  · simpa only [Subgroup.orderOf_coe] using hz

/-- A nontrivial odd core of a two-local subgroup in an N2 group is detected
by the full centralizer of some involution. -/
public theorem exists_involution_bad_oddCore
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G)
    (hbad : ∃ U : Subgroup G, IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥) :
    ∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ := by
  classical
  obtain ⟨U, ⟨Q, hQne, hQp, hU⟩, hodd⟩ := hbad
  obtain ⟨t, htQ, htC, ht⟩ := central_involution Q hQp hQne
  let L := Subgroup.centralizer ({t} : Set G)
  have hLsolv : Group.IsSolvable L := by
    by_contra h
    have htp : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using ht)
    have htne : Subgroup.zpowers t ≠ ⊥ := by
      intro hbot
      have hone := Subgroup.zpowers_eq_bot.mp hbot
      simp [hone] at ht
    have hLN : L ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
      change Subgroup.centralizer ({t} : Set G) ≤ _
      rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
    let := hN _ ⟨Subgroup.zpowers t, htne, htp, rfl⟩
    exact h (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hLN))
  have hQU : Q ≤ U := hU ▸ Subgroup.le_normalizer
  have hQL : Q ≤ L := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp htC q hq
  let QL := Q.subgroupOf L
  let C := Subgroup.centralizer (QL : Set L)
  have hCU (c : C) : ((c : L) : G) ∈ U := by
    rw [hU]
    apply Subgroup.centralizer_le_normalizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg (fun x : L => (x : G))
      (Subgroup.mem_centralizer_iff.mp c.property ⟨q, hQL hq⟩ hq)
  let f : C →* U :=
    { toFun := fun c => ⟨c.val.val, hCU c⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : U => (x : G)) hab
  have hQnormal : (Q.subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by rw [hU])
  let := hQnormal
  have hoddCentral := pPrimeCore_le_centralizer_of_normal_pgroup 2
    (Q.subgroupOf U) hQp.comap_subtype
  refine ⟨t, ht, ?_⟩
  intro hLcore
  have hCcore : pPrimeCore 2 C = ⊥ := by
    have hle := pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable hLsolv 2
      QL hQp.comap_subtype
    rw [hLcore] at hle
    have hmap : (pPrimeCore 2 C).map C.subtype = ⊥ := le_bot_iff.mp hle
    exact Subgroup.map_injective C.subtype_injective (by simpa using hmap)
  let R : Subgroup C := (pPrimeCore 2 U).comap f
  have hRnormal : R.Normal := inferInstance
  have hRcop : Nat.Coprime 2 (Nat.card R) := by
    exact (pPrimeCore_coprime_card (G := U) (p := 2)).of_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ f hf)
  have hRbot : R = ⊥ := (pPrimeCore_eq_bot_iff.mp hCcore) R hRnormal hRcop
  apply hodd
  apply eq_bot_iff.mpr
  intro u hu
  have huQ : (u : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg (fun x : U => (x : G))
      (Subgroup.mem_centralizer_iff.mp (hoddCentral hu) ⟨q, hQU hq⟩ hq)
  have huL : (u : G) ∈ L := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp huQ t htQ).symm
  have huC : (⟨u, huL⟩ : L) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp huQ q hq
  have hmem : (⟨⟨u, huL⟩, huC⟩ : C) ∈ R := hu
  rw [hRbot] at hmem
  change (⟨⟨u, huL⟩, huC⟩ : C) = 1 at hmem
  change u = 1
  apply Subtype.ext
  exact congrArg (fun x : C => ((x : L) : G)) hmem

end Stellmacher.Recognition
