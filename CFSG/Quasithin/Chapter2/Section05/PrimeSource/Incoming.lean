module
public import CFSG.Quasithin.Chapter2.Section05.NativeZD
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NormalAtT
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import Theory.GroupTheory.ComponentInverterCyclicCentralizer

/-!
# The original prime crossing pair

The source involution z=t tˣ inverts the odd core of C_G(t). Since t
centralizes that group and tˣ belongs to its actual component, the odd core
vanishes. The proved component supplement and original disjoint crossing
cores then fill the literal prime-pair input. Its native ZD consumer gives
the contradiction once the preceding source argument supplies commutation.

Source: Aschbacher--Smith 2.5.18 and 2.5.21, printed pp.560,566--567.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Overcomponents
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The source centralizer's odd core vanishes when its central mark is t times
an involution of its actual component. -/
theorem MathieuSourceSetup.prime_marked_centralizer_oddCore
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t w : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hwK : w ∈ K) (hw : orderOf w = 2) (hz : z = t * w) :
    pPrimeCore 2 (centralizer ({t} : Set G)) = ⊥ := by
  let J := centralizer ({t} : Set G)
  obtain ⟨_,hJ,⟨P,hP⟩,_,_⟩ :=
    MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  have hKJ := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  have h115 := NonEnlargement.hypotheses115_of_same_sylow hG c.T c.maximal c.sylow_le
    c.unique (MathieuSourceSetup.sourceTuple c) hJ P hP
  let wJ : J := ⟨w,hKJ.1 hwK⟩
  apply oddCore_eq_bot_of_component_involution_inverts (K.subgroupOf J) hKJ.2 wJ hwK
    (by simpa only [wJ,Subgroup.orderOf_mk] using hw)
  intro u hu
  apply Subtype.ext
  have ha := h115.inverts_oddCore u hu
  rw [hz] at ha
  have htu : Commute t (u : G) :=
    (mem_centralizer_singleton_iff.mp u.property).symm
  change w * (u : G) * w⁻¹ = (u : G)⁻¹
  calc
    w * (u : G) * w⁻¹ = t⁻¹ * ((t*w) * (u : G) * (t*w)⁻¹) * t := by group
    _ = t⁻¹ * (u : G)⁻¹ * t := by rw [ha]
    _ = (u : G)⁻¹ := by
      rw [htu.inv_left.inv_right.eq,mul_assoc,inv_mul_cancel,mul_one]

/-- Actual prime-pair contradiction: the preceding source generation step
need only supply commutation of the literal crossing components. -/
theorem MathieuSourceSetup.prime_crossing_false_of_commuting
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2,ZMod p))
    (t x : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (htx : x⁻¹ * t * x ∈ K) (hz : z = t * (x⁻¹ * t * x))
    (hcomm : ⁅K,K.conjBy x⁻¹⁆ = ⊥) : False := by
  let Y := (S : Subgroup H).map H.subtype
  let J := centralizer ({t} : Set G)
  obtain ⟨hHJ,_,⟨P,hP⟩,_,hnf⟩ :=
    MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  have hKJ : K ≤ J := c.component_le.trans hHJ
  have hnorm := source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  have hcomp : (K.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKJ).mpr hnorm
  have hsup := source_normal_component_centralizer_supplement c hG hempty hgen hb hstar
    t ht htC htZ
  have hodd := MathieuSourceSetup.prime_marked_centralizer_oddCore c hG hempty hgen hb hstar
    t (x⁻¹*t*x) ht htC htZ htx
    (by simpa only [MulAut.conj_apply,inv_inv] using ((MulAut.conj x⁻¹).orderOf_eq t).trans ht) hz
  have hd := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hd
  let d : PSL2PairSource.Incoming KnownSimple.IsKnownSimple G p := {
    ambient := hG
    T := c.T
    H := H
    S := Y
    K := K
    t := t
    x := x
    z := z
    prime_ge := hp
    parameter := hfm
    model := eK
    sylow := P
    sylow_eq := hP
    s_le_t := c.sylow_lt.le
    t_mem := htZ.1
    t_order := ht
    x_mem := hxT
    x_normalizes := hxN
    x_square := hx2
    normalK := hcomp
    generated := by rw [hgen] at hsup; exact hsup
    h_eq := hgen
    oddCore := hodd
    crossing_mark := htx
    z_eq := hz
    nonfusion := hnf
    disjoint := hd.eq_bot
    commuting := hcomm }
  exact d.false_of_prime_crossing_pair_source

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
