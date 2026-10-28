module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableAction
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Thompson
public import CFSG.Quasithin.Chapter13.Section05.A5Source.CrossModule
public import Theory.Representation.BinaryAlternatingFiveExtension.ResidualLift

/-!
# Two-core restrictions for the original nonsolvable A₅ pair

A core of order at most sixteen equals the residual Context's natural
module. Its full marked S₅ action therefore supplies an actual elementary
subgroup of O²(H) with image four under H → H/O₂(H).

The two original local cores have the same index eight in T. If either
contained the other, equality and the unique maximal two-local overgroup
would force H into N_G(L). Thus they are incomparable. If the original
natural modules commute, an abelian outside core would centralize both,
contradicting incomparability. Finally, a core of order at most thirty-two
is abelian, since its natural sixteen is central and has index at most two.

SourceAssembly/NonsolvableCores supplies every original input and applies
the lift to 5.2.3. Larger cores and the full 13.2.8(1) exclusion remain open.
Source: Aschbacher--Smith 1.2.7,13.2.4(2b),13.2.8(1), pp.506--507,879--880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- A small original kernel supplies the required lift through the literal quotient. -/
theorem residual_lift_of_core_le_sixteen
    {T : Sylow 2 G} {K W W₁ W₂ W₃ H : Subgroup G}
    (e : Context T K W W₁ W₂ W₃)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (hact : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hWQ : W ≤ H.pCoreIn 2) (hc : Nat.card (pCore 2 H) ≤ 16) :
    ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4 := by
  have hQ : H.pCoreIn 2 = W := (eq_of_le_of_card_ge hWQ (by
    rw [pCoreIn,card_map_of_injective H.subtype_injective]
    rwa [e.module_card])).symm
  have hkW : q.ker.map H.subtype = W := by rw [hk];exact hQ
  let f := e.flag.module.map
  let a := q.ker.equivMapOfInjective H.subtype H.subtype_injective
  let b := MonoidHom.ofInjective e.flag.module.injective
  let E : q.ker ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    a.trans ((MulEquiv.subgroupCongr (hkW.trans e.flag.module.range_eq.symm)).trans b.symm)
  have hcoord (v : q.ker) : f (E v) = ((v : H) : G) :=
    MonoidHom.apply_ofInjective_symm e.flag.module.injective _
  have he (g : H) (v : q.ker) : E (MulAut.conjNormal g v) =
      BinaryPermutation.AlternatingFiveExtension.coreAction (q g) (E v) := by
    apply e.flag.module.injective
    change f (E (MulAut.conjNormal g v)) = _
    rw [hcoord]
    change g.val * v.val.val * g.val⁻¹ = _
    rw [←hcoord v]
    exact hact g (E v).toAdd
  obtain ⟨A,hA,hAR,hcard⟩ :=
    BinaryPermutation.AlternatingFiveExtension.exists_residual_four_of_faithful_kernel q hq E he
  let bq : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) :=
    QuotientGroup.liftEquiv (pCore 2 H) hq hk.symm
  have hbq : bq.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) = q := by
    ext h
    rfl
  refine ⟨A,hA,hAR,?_⟩
  rw [←hbq,←map_map,card_map_of_injective (f := bq.toMonoidHom) bq.injective] at hcard
  exact hcard
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_card_of_symmetric_five_kernel
    {D : Type*} [Group D] [Finite D] (S : Sylow 2 D)
    (q : D →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 D) : Nat.card S = Nat.card (pCore 2 D) * 8 := by
  let P := S.mapSurjective hq
  have hc : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide +kernel
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (S : Subgroup D) q
  rw [hk,inf_of_le_right (pCore_isPGroup.le_sylow_of_normal S)] at hh
  exact hh.symm.trans (congrArg (Nat.card (pCore 2 D) * ·) hc)

/-- The two actual local two-cores have the same order. -/
theorem original_pair_core_cards
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hTH : (T : Subgroup G) ≤ H)
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H) :
    Nat.card (H.pCoreIn 2) = Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  have ha := sylow_card_of_symmetric_five_kernel (T.subtype hTH) q hq hk
  have hb := sylow_card_of_symmetric_five_kernel (T.subtype le_sup_right)
    d.localActor hd (d.localActor_kernel_eq_core d.normalizes_L)
  change Nat.card ((T : Subgroup G).subgroupOf H) = _ at ha
  change Nat.card ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))) = _ at hb
  rw [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv] at ha
  rw [Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).toEquiv] at hb
  rw [pCoreIn,pCoreIn,card_map_of_injective H.subtype_injective,
    card_map_of_injective (L ⊔ (T : Subgroup G)).subtype_injective]
  omega

/-- Neither of the two actual local two-cores contains the other. -/
theorem original_pair_cores_incomparable
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H) :
    ¬ H.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ H.pCoreIn 2 := by
  have hcard := original_pair_core_cards d hH.1.1.2 hd q hq hk
  have hne : H.pCoreIn 2 ≠ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    intro he
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    have hQne : Q ≠ ⊥ := by
      have hVQ : V ≤ Q := d.chosen.le_componentCore.trans
        (pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer d.normalizes_L))
      intro hb
      exact d.chosen.ne_bot (bot_unique (hVQ.trans_eq hb))
    have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))) hQne
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
    have hHN : H ≤ normalizer (Q : Set G) := by
      change H ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)
      rw [←he]
      exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    exact hH.1.2 (hHN.trans hN)
  exact ⟨fun h => hne (eq_of_le_of_card_ge h hcard.ge),
    fun h => hne (eq_of_le_of_card_ge h hcard.le).symm⟩

/-- If the original natural modules commute, the outside two-core is nonabelian. -/
theorem original_pair_commuting_core_nonabelian
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (hVW : V ≤ centralizer (W : Set G)) : ¬ IsMulCommutative (pCore 2 H) := by
  intro hab
  let := hab
  let : IsMulCommutative (H.pCoreIn 2) := Subgroup.map_isMulCommutative
    (H := pCore 2 H) (f := H.subtype)
  have hVQ : V ≤ H.pCoreIn 2 := by
    rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
    exact le_inf d.chosen.le_sylow hVW
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    exact map_le_iff_le_comap.mpr
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
  have hQV : H.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (le_centralizer (H.pCoreIn 2)).trans (centralizer_le hVQ)
  have hle : H.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [←d.sylow_centralizer d.normalizes_L]
    exact le_inf hQT hQV
  exact (original_pair_cores_incomparable d hH hd q hq hk).1 hle
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization


namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The original natural sixteen is central in the two-core. A core of order
at most thirty-two has cyclic quotient by this subgroup, hence is abelian. -/
theorem core_commutative_of_card_le_thirtyTwo
    {T : Sylow 2 G} {K W W₁ W₂ W₃ H : Subgroup G}
    (e : Context T K W W₁ W₂ W₃) (hjoin : K ⊔ (T : Subgroup G) = H)
    (hsmall : Nat.card (pCore 2 H) ≤ 32) : IsMulCommutative (pCore 2 H) := by
  let Q := H.pCoreIn 2
  have hWQ : W ≤ Q := by
    change W ≤ H.pCoreIn 2
    rw [←hjoin]
    exact e.chosen.le_componentCore.trans
      (pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer e.normalizes_L))
  have hQW : Q ≤ centralizer (W : Set G) := by
    change H.pCoreIn 2 ≤ _
    rw [←hjoin]
    exact e.chosen.core_centralizes
  let P := W.subgroupOf Q
  have hP : P ≤ center Q := by
    intro w hw
    rw [mem_center_iff]
    intro q
    exact Subtype.ext ((hQW q.property) w hw).symm
  let : P.Normal := ⟨fun w hw q => by
    rw [mem_center_iff.mp (hP hw) q,mul_inv_cancel_right]
    exact hw⟩
  have hcP : Nat.card P = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWQ).toEquiv).trans e.module_card
  have hcQ : Nat.card Q ≤ 32 := by
    change Nat.card (H.pCoreIn 2) ≤ 32
    rwa [pCoreIn,card_map_of_injective H.subtype_injective]
  have hh := card_eq_card_quotient_mul_card_subgroup P
  rw [hcP] at hh
  have hpos : 0 < Nat.card (Q ⧸ P) := Nat.card_pos
  have hq : Nat.card (Q ⧸ P) = 1 ∨ Nat.card (Q ⧸ P) = 2 := by omega
  let : IsCyclic (Q ⧸ P) := isCyclic_of_card_dvd_prime (p := 2) (by
    rcases hq with hq | hq
    · rw [hq]
      exact one_dvd 2
    · rw [hq])
  let : IsMulCommutative Q := (QuotientGroup.mk' P).isMulCommutative_of_isCyclic_of_ker_le_center
    (by simpa only [QuotientGroup.ker_mk'] using hP)
  have hcomm : ∀ x y : Q, x * y = y * x :=
    fun x y => IsMulCommutative.is_comm.comm x y
  let a := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  refine ⟨⟨fun x y => a.injective ?_⟩⟩
  simp only [map_mul]
  exact hcomm (a x) (a y)
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

