module

public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.PrimeRankNormalDetection
public import Theory.GroupTheory.Commutator.CoprimeQuadratic

/-!
# Three-rank of the actual tilded-plane centralizer

An elementary three-subgroup centralizing V₂/V₁ has [V₂,E] ≤ V₁.
The point normalizer centralizes V₁, so coprime quadratic action makes E
centralize V₂. Its intersection with I₂ therefore lies in O₂(I₂) and is
trivial. But I₂ is normal in G₂ and has order divisible by three: an
E₉ in this centralizer would force three-rank at least three in G₂.
Quasithinness excludes that possibility.

The centralizer is the literal preimage of the centralizer of the image
of V₂ under H → H/V₁, then included in G. The source consumer uses the
normality, action kernel and S₃ quotient of the actual I₂ from 12.8.9.
Those preceding sibling clauses remain explicit; no additional model
calculation or classification theorem is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.13(8), printed pp.855–856.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

@[expose] public def terminalTildePlaneCentralizer (F : InvariantFlag T V n) : Subgroup G :=
  ((centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)).comap
    (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))).map F.H.subtype

public theorem terminalTildePlaneCentralizer_le_H (F : InvariantFlag T V n) :
    F.terminalTildePlaneCentralizer ≤ F.H := map_subtype_le _

public theorem tildePlane_commutator_le_point (F : InvariantFlag T V n)
    (hVH : F.Vi 2 ≤ F.H) : ⁅F.Vi 2, F.terminalTildePlaneCentralizer⁆ ≤ F.Vi 1 := by
  apply commutator_le.mpr
  intro v hv x hx
  obtain ⟨x, hx, rfl⟩ := hx
  let vH : F.H := ⟨v, hVH hv⟩
  let q := QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H)
  have hvq : q vH ∈ F.tilde (F.Vi 2) := mem_map_of_mem q hv
  have hcomm := mem_centralizer_iff.mp hx (q vH) hvq
  have he : q ⁅vH, x⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hm : ⁅vH, x⁆ ∈ (F.Vi 1).subgroupOf F.H :=
    (QuotientGroup.eq_one_iff _).mp he
  exact hm

public theorem terminalTildePlaneCentralizer_le_G₂ (F : InvariantFlag T V n)
    (hVH : F.Vi 2 ≤ F.H) : F.terminalTildePlaneCentralizer ≤ F.Gi 2 := by
  apply le_normalizer_iff_commutator_le_left.mpr
  exact (F.tildePlane_commutator_le_point hVH).trans (F.monotone (by omega : 1 ≤ 2))

public theorem odd_elementary_centralizes_plane [Finite G]
    (F : InvariantFlag T V n) (hVH : F.Vi 2 ≤ F.H)
    (hpoint : Nat.card (F.Vi 1) = 2) (hplane : IsPGroup 2 (F.Vi 2))
    [IsMulCommutative (F.Vi 2)]
    (E : Subgroup G) [IsElementaryAbelian 3 E]
    (hEC : E ≤ F.terminalTildePlaneCentralizer) : E ≤ centralizer (F.Vi 2 : Set G) := by
  have hEP : E ≤ normalizer (F.Vi 2 : Set G) :=
    hEC.trans (F.terminalTildePlaneCentralizer_le_G₂ hVH)
  have hcomm : ⁅F.Vi 2, E⁆ ≤ F.Vi 1 :=
    (commutator_mono le_rfl hEC).trans (F.tildePlane_commutator_le_point hVH)
  have hEH : E ≤ F.H := hEC.trans F.terminalTildePlaneCentralizer_le_H
  have hfix : E ≤ centralizer (F.Vi 1 : Set G) :=
    hEH.trans (normalizer_le_centralizer_of_card_two _ hpoint)
  have hquad : ⁅⁅F.Vi 2, E⁆, E⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono hcomm le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hfix)).le
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (F.Vi 2)) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) E (F.Vi 2)
      (IsElementaryAbelian.isPGroup 3 E) hplane
  have htriv := commutator_eq_bot_of_coprime_quadratic (F.Vi 2) E hEP
    inferInstance hcop hquad
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp htriv)
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

public theorem lemma_12_8_13_eight (F : InvariantFlag T V n) [IsMulCommutative V]
    (hG : IsQuasithin G) (hn : 2 ≤ n) (L : Subgroup G)
    (hIG : F.I₂ L ≤ F.Gi 2) (hIN : ((F.I₂ L).subgroupOf (F.Gi 2)).Normal)
    (hIC : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hquo : Nonempty ((F.I₂ L ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))) :
    primeRank 3 F.terminalTildePlaneCentralizer ≤ 1 := by
  have hVH : F.Vi 2 ≤ F.H :=
    (F.le_seed 2).trans ((le_conjugateSpanBy V F.H).trans F.U_le_H)
  have hcard := F.card 2 hn
  have hp : IsPGroup 2 (F.Vi 2) := IsPGroup.of_card (n := 2) hcard
  have hne : F.Vi 2 ≠ ⊥ := by intro h; simp [h] at hcard
  have hG₂ : IsTwoLocal (F.Gi 2) := ⟨F.Vi 2, hne, hp, rfl⟩
  have hr : primeRank 3 (F.Gi 2) ≤ 2 :=
    (CFSG.Quasithin.isQuasithin_iff_twoLocal.mp hG) _ hG₂ 3 (by decide) (by decide)
  have hCG := F.terminalTildePlaneCentralizer_le_G₂ hVH
  let I := (F.I₂ L).subgroupOf (F.Gi 2)
  let C := F.terminalTildePlaneCentralizer.subgroupOf (F.Gi 2)
  let : I.Normal := hIN
  have hdiv : 3 ∣ Nat.card I := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hIG).toEquiv]
    have hcQ : Nat.card (F.I₂ L ⧸ pCore 2 (F.I₂ L)) = 6 := by
      obtain ⟨e⟩ := hquo
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    have hd : Nat.card (F.I₂ L ⧸ pCore 2 (F.I₂ L)) ∣ Nat.card (F.I₂ L) :=
      (pCore 2 (F.I₂ L)).index_dvd_card
    rw [hcQ] at hd
    exact dvd_trans (by decide : 3 ∣ 6) hd
  have hb : primeRank 3 C ≤ 1 := by
    apply Subgroup.primeRank_le_one_of_disjoint_normal hr I C hdiv
    intro E hEC hE
    let := hE
    let A := E.map (F.Gi 2).subtype
    let : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
    have hAC : A ≤ F.terminalTildePlaneCentralizer := by
      rintro x ⟨e, he, rfl⟩
      exact hEC he
    let : IsMulCommutative (F.Vi 2) := isMulCommutative_iff.mpr (by
      intro x y
      exact Subtype.ext (congrArg (fun v : V => (v : G))
        (mul_comm (⟨x, F.le_seed 2 x.property⟩ : V) (⟨y, F.le_seed 2 y.property⟩ : V))))
    have hAcent := F.odd_elementary_centralizes_plane hVH
      (by simpa using F.card 1 (by omega)) hp A hAC
    have hdis := IsPGroup.disjoint_of_ne 3 2 (by decide) A ((F.I₂ L).pCoreIn 2)
      (IsElementaryAbelian.isPGroup 3 A) (isPGroup_pCoreIn 2 (F.I₂ L))
    apply disjoint_def.mpr
    intro x hxE hxI
    apply Subtype.ext
    have hxA : (x : G) ∈ A := mem_map_of_mem (F.Gi 2).subtype hxE
    apply disjoint_def.mp hdis hxA
    rw [← hIC]
    exact ⟨hxI, hAcent hxA⟩
  rwa [Theory.GroupTheory.primeRank_equiv 3 (subgroupOfEquivOfLe hCG)] at hb
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
