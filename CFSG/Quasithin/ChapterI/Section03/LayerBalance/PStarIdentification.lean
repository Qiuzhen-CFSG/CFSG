module

public import Theory.GroupTheory.PStar.OddKernel
public import Theory.GroupTheory.PStar.Solvable
public import Theory.GroupTheory.GeneralizedFitting.SylowCentralizerSchreier
public import Theory.GroupTheory.CComponent.TwoComponent.LayerMaps
public import Theory.GroupTheory.PResidual.PrimeSetFiniteImage
public import FeitThompson.FinalTheorem

/-!
# The odd residual of the two-star core

Under the genuine two-Schreier condition on actual simple sections,
O^{2'}(O_{2*}(X)) is the canonical two-component layer.

First, the odd residual of a two-star group is its solvable residual:
its solvable quotient is two-star and hence odd, while every odd quotient
is solvable by the odd order theorem. Modulo the odd core, F(Y) is central
for Y = O_{2*}(X). The two-Schreier component-action argument makes a Sylow
centralizer of E(Y) solvable, so the defining supplement gives Y^∞ = E(Y).
The ordinary layer lies in the two-star core, identifying this with E(X).
Finally, odd-kernel transfer and the canonical two-component correspondence
give equal images modulo O_{2'}(X). Perfect subnormal subgroups with equal
images modulo a solvable normal subgroup coincide, giving the original
identity with its literal subtype map.

Source: GLS II, Chapter B, Proposition 5.16, second equality. No global
Schreier theorem, balance theorem, or general extension criterion is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.LayerBalance
variable {G : Type*} [Group G] [Finite G]

private theorem isPiGroup_odd_iff :
    IsPiGroup {q : Nat.Primes | q.val ≠ 2} G ↔ Odd (Nat.card G) := by
  rw [IsPiGroup_iff]
  constructor
  · intro h
    apply Nat.not_even_iff_odd.mp
    intro he
    exact h ⟨2, Nat.prime_two⟩ (even_iff_two_dvd.mp he) rfl
  · intro h q hq he
    exact h.not_two_dvd_nat (he ▸ hq)

/-- For two-star groups the odd residual is the terminal derived subgroup. -/
theorem oddResidual_eq_solvableResidual_of_isPStar (hG : IsPStar 2 G) :
    piResidual {q : Nat.Primes | q.val ≠ 2} G = solvableResidual G := by
  apply le_antisymm
  · exact sInf_le ⟨inferInstance, isPiGroup_odd_iff.mpr
      ((hG.quotient (solvableResidual G)).odd_card_of_solvable)⟩
  · apply le_sInf
    rintro N ⟨hN, hpi⟩
    let := hN
    let : Group.IsSolvable (G ⧸ N) := odd_order_theorem _ (isPiGroup_odd_iff.mp hpi)
    exact solvableResidual_le_of_solvable_quotient N

private theorem component_central_quotient_even {K : Subgroup G}
    (hK : IsComponent G K) : 2 ∣ Nat.card (K ⧸ center K) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  by_contra h
  let : Group.IsSolvable (K ⧸ center K) := odd_order_theorem _
    (Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he)))
  exact Group.IsPerfect.not_isSolvable (K ⧸ center K) inferInstance

/-- The source two-layer is the ordinary layer when the odd core is trivial. -/
theorem twoComponentLayer_eq_componentLayer_of_oddCore_eq_bot
    (ho : pPrimeCore 2 G = ⊥) : twoComponentLayer G = componentLayer G := by
  apply le_antisymm
  · exact sSup_le fun K hK => le_sSup (hK.isComponent_of_oddCore_eq_bot ho)
  · apply sSup_le
    intro K hK
    let : Group.IsSolvable (pPrimeCore 2 K) := odd_order_theorem _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    exact hK.isTwoComponent_of_solvable_oddCore.le_twoComponentLayer

/-- The component-action step of GLS II 5.16, after removal of the odd core. -/
theorem solvableResidual_eq_componentLayer_of_isPStar
    (hG : IsPStar 2 G) (hS : HasTwoSchreier G) (ho : pPrimeCore 2 G = ⊥) :
    solvableResidual G = componentLayer G := by
  have hF : fittingSubgroup G ≤ center G := by
    rw [Fitting_eq_pcore G 2 ho]
    exact hG.normal_pSubgroup_le_center _ pCore_isPGroup
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := componentLayer G)
  let E := componentLayer G
  let C := centralizer ((P : Subgroup E).map E.subtype : Set G)
  let : Group.IsSolvable C := solvable_centralizer_layer_sylow_of_twoSchreier hS
    (fun _ hK => component_central_quotient_even hK) hF P
  let q := QuotientGroup.mk' E
  have hC : C.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) (hG.2 E P)
    simpa [Subgroup.map_sup, q, C,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective E)] using h
  have hf : Function.Surjective (q.comp C.subtype) := MonoidHom.range_eq_top.mp (by
    simpa only [MonoidHom.range_comp, range_subtype] using hC)
  let : Group.IsSolvable (G ⧸ E) := Group.isSolvable_of_surjective hf
  let : Group.IsPerfect E := componentLayer_isPerfect
  exact le_antisymm (solvableResidual_le_of_solvable_quotient E)
    (le_solvableResidual_of_isPerfect E)

/-- GLS II 5.16 for a group with trivial odd core. -/
theorem oddResidual_twoStarCore_eq_twoLayer_of_oddCore_eq_bot
    (hS : HasTwoSchreier G) (ho : pPrimeCore 2 G = ⊥) :
    (piResidual {q : Nat.Primes | q.val ≠ 2} (pStarCore 2 G)).map
      (pStarCore 2 G).subtype = twoComponentLayer G := by
  let Y := pStarCore 2 G
  have hY : Y.IsSubnormal := (inferInstance : Y.Normal).isSubnormal
  rw [oddResidual_eq_solvableResidual_of_isPStar isPStar_twoStarCore,
    solvableResidual_eq_componentLayer_of_isPStar isPStar_twoStarCore
      (hS.subgroup Y) (hY.pPrimeCore_eq_bot ho),
    map_componentLayer_subtype_eq_of_le Y hY componentLayer_le_twoStarCore,
    twoComponentLayer_eq_componentLayer_of_oddCore_eq_bot ho]

/-- GLS II, Proposition 5.16, second equality: the residual for odd-order
quotients of the two-star core is the canonical source two-layer. -/
theorem oddResidual_twoStarCore_eq_twoLayer (hS : HasTwoSchreier G) :
    (piResidual {q : Nat.Primes | q.val != 2} (pStarCore 2 G)).map
      (pStarCore 2 G).subtype = twoComponentLayer G := by
  simp only [bne_iff_ne]
  let O := pPrimeCore 2 G
  let q := QuotientGroup.mk' O
  have hO : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let : Group.IsSolvable O := odd_order_theorem _ hO
  let Y := pStarCore 2 G
  let R := (solvableResidual Y).map Y.subtype
  let L := twoComponentLayer G
  have himage : R.map q = L.map q := by
    change ((solvableResidual Y).map Y.subtype).map q = (twoComponentLayer G).map q
    rw [← oddResidual_eq_solvableResidual_of_isPStar isPStar_twoStarCore,
      map_embedded_piResidual, map_twoStarCore_of_surjective_odd_kernel q
        (QuotientGroup.mk'_surjective O) (by simpa only [q, QuotientGroup.ker_mk'] using hO),
      oddResidual_twoStarCore_eq_twoLayer_of_oddCore_eq_bot
        (hS.of_surjective q (QuotientGroup.mk'_surjective O))
        (pPrimeCore_quotient_pPrimeCore_eq_bot 2),
      map_twoComponentLayer_odd_quotient O hO]
  have hsup : R ⊔ O = L ⊔ O := by
    simpa only [q, comap_map_eq, QuotientGroup.ker_mk'] using congrArg (comap q) himage
  let : Group.IsPerfect R := Group.IsPerfect.map Y.subtype
  let : Group.IsPerfect L := twoComponentLayer_isPerfect
  have hRn : R.IsSubnormal := (inferInstance : (solvableResidual Y).Normal).isSubnormal.trans'
    (inferInstance : Y.Normal).isSubnormal
  have hLn : L.IsSubnormal := (inferInstance : L.Normal).isSubnormal
  have hR : (solvableResidual (R ⊔ O : Subgroup G)).map (R ⊔ O).subtype = R :=
    hRn.solvableResidual_sup_eq O (by rw [normalizer_eq_top]; exact le_top)
  have hL : (solvableResidual (L ⊔ O : Subgroup G)).map (L ⊔ O).subtype = L :=
    hLn.solvableResidual_sup_eq O (by rw [normalizer_eq_top]; exact le_top)
  rw [oddResidual_eq_solvableResidual_of_isPStar isPStar_twoStarCore]
  change R = L
  rw [← hR, hsup, hL]

end CFSG.Quasithin.ChapterI.LayerBalance
