module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleCubicInverter

public import Theory.SpecificGroups.Alternating.FiveCubicCentralizer
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# Trivial action of the original cubic lift on L/O₂(L)

A separating element in the prescribed Sylow centralizer of the cubic
lift acts oddly on the original five-point module. Indeed an even
Sylow element belongs to the Borel two-core, whose image centralizes
the left residual of the non-characteristic-two quotient vertex.

The permuting cubic Sylow join is solvable and preserves T∩L. Its actual
A₅ quotient action therefore fixes a point on five letters. The selected
cubic commutes with the separating odd element, so the four-letter
centralizer calculation makes its quotient action trivial. This also
bounds the literal commutator with L by O₂(L).

The original-source application supplies its own normalizer and inverter
from both Goldschmidt triples and the same O₃′ quotient. It does not
complete the normal-closure contradiction or the nonsolvable branch.
Source: Aschbacher--Smith 13.2.7, printed pp.883--884.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

private theorem even_sylow_mem_borel_core
    (t : (L ⊔ (T : Subgroup G) : Subgroup G))
    (ht : (t : G) ∈ (T : Subgroup G))
    (he : d.localActor t ∈ alternatingGroup (Fin 5)) :
    (t : G) ∈ (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let K := L ⊔ (T : Subgroup G)
  let B := borelResidual T L
  let P := B ⊔ (T : Subgroup G)
  let Q := K.pCoreIn 2
  let S := (T : Subgroup G) ⊓ L
  have hBB : B ≤ ChapterF.Source.borel L (T : Subgroup G) := by
    rw [show B = borelResidual T L from rfl,borelResidual_eq_point_residual d,
      d.borel_eq_point_centralizer]
    exact Section05.A5Source.ThirdSpace.residual_le_centralizer
  have hPK : P ≤ K := sup_le_sup (hBB.trans inf_le_left) le_rfl
  have hPS : P ≤ normalizer (S : Set G) := sup_le (hBB.trans inf_le_right)
    ((le_inf (T : Subgroup G).le_normalizer d.normalizes_L).trans inf_normalizer_le_normalizer_inf)
  have hSP : S ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans le_sup_right) hPS
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hQP : Q ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 K) (hQT.trans le_sup_right)
    ((hPK.trans K.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have him : d.localActor t ∈ (L.subgroupOf K).map d.localActor :=
    d.localActor_component_image.symm ▸ he
  obtain ⟨l,hl,hlf⟩ := him
  let z : K := t * l⁻¹
  have hz : z ∈ pCore 2 K := by
    rw [←d.localActor_kernel_eq_core d.normalizes_L]
    change d.localActor (t * l⁻¹) = 1
    rw [map_mul,map_inv,hlf,mul_inv_cancel]
  have hzQ : (z : G) ∈ Q := mem_map_of_mem K.subtype hz
  have hlT : (l : G) ∈ (T : Subgroup G) := by
    have hh := (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem (hQT hzQ)) ht
    change ((t : G) * (l : G)⁻¹)⁻¹ * (t : G) ∈ (T : Subgroup G) at hh
    simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  have hh := (P.pCoreIn 2).mul_mem (hQP hzQ) (hSP ⟨hlT,hl⟩)
  change (t : G) * (l : G)⁻¹ * (l : G) ∈ P.pCoreIn 2 at hh
  simpa only [inv_mul_cancel_right] using hh

/-- Movement of the original Borel residual image detects odd action on
L/O₂(L) by the same original Sylow element. -/
theorem single_separating_element_odd
    (c : SingleQuotientProduct T L H)
    (hg : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ChapterF.IsGoldschmidtTriple
        (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q)
        ((H.subgroupOf J).map q))
    (hz : pCore 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) = ⊥)
    (hTH : (T : Subgroup G) ≤ H)
    (t : (H ⊔ borelResidual T L : Subgroup G))
    (ht : (t : G) ∈ (T : Subgroup G))
    (hn : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      let A := ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q
      q t ∉ centralizer ((pResidual 2 A).map A.subtype : Set _)) :
    d.localActor ⟨t,mem_sup_right ht⟩ ∉ alternatingGroup (Fin 5) := by
  intro he
  let J := H ⊔ borelResidual T L
  let P := borelResidual T L ⊔ (T : Subgroup G)
  let P₀ := P.subgroupOf J
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  let A := P₀.map q
  have hc : (t : G) ∈ P.pCoreIn 2 := even_sylow_mem_borel_core d ⟨t,mem_sup_right ht⟩ ht he
  have hPJ : P ≤ J := sup_le le_sup_right (hTH.trans le_sup_left)
  have htcore : t ∈ P₀.pCoreIn 2 := (mem_map_iff_mem J.subtype_injective).mp (by
    rw [Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_subgroupOf_map hPJ]
    exact hc)
  have hqcore : q t ∈ A.pCoreIn 2 :=
    Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q P₀
      (mem_map_of_mem q htcore)
  exact hn (hg.local_core_centralizes_residual (c.selected.left_not_characteristic_two hg hz) hqcore)
omit d in
/-- The selected permuting cubic lift and the original Sylow have solvable join. -/
theorem single_cubic_join_solvable
    (c : SingleQuotientProduct T L H) (hTH : (T : Subgroup G) ≤ H) :
    Group.IsSolvable (c.cubic_lift.map (H ⊔ borelResidual T L).subtype ⊔
      (T : Subgroup G) : Subgroup G) := by
  let J := H ⊔ borelResidual T L
  let Y := c.cubic_lift.map J.subtype
  let X := Y ⊔ (T : Subgroup G)
  have hTJ : (T : Subgroup G) ≤ J := hTH.trans le_sup_left
  have hcY : Nat.card Y = 3 :=
    (card_map_of_injective J.subtype_injective).trans c.cubic_card
  have hp : (Y : Set G) * (T : Set G) = (T : Set G) * (Y : Set G) := by
    have hm := congrArg (Set.image J.subtype) c.cubic_permutes.symm
    rw [Set.image_mul,Set.image_mul] at hm
    change (Y : Set G) *
      (((T : Subgroup G).subgroupOf J).map J.subtype : Set G) =
      (((T : Subgroup G).subgroupOf J).map J.subtype : Set G) * (Y : Set G) at hm
    simpa only [map_subgroupOf_eq_of_le hTJ,Sylow.coe_coe] using hm
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (T : Subgroup G)) := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hcY,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hh := card_set_mul_mul_card_inf Y (T : Subgroup G)
  rw [(disjoint_of_coprime_natCard hcop).eq_bot,card_bot,mul_one,
    ←coe_sup_of_set_mul_comm Y T hp] at hh
  change Nat.card X = _ at hh
  have hi := ((T : Subgroup G).subgroupOf X).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show (T : Subgroup G) ≤ X from le_sup_right)).toEquiv,hh,hcY,mul_comm 3] at hi
  have hindex : (T : Subgroup G).relIndex X = 3 :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  exact (T : Subgroup G).isSolvable_of_relIndex_le_four X (by omega)

/-- The selected original cubic acts trivially on the actual marked A₅ quotient.
Its separating Sylow centralizer element is odd; the solvable cubic Sylow join
preserves the component Sylow, hence fixes a common point on five letters. -/
theorem single_cubic_quotient_action_eq_one
    (c : SingleQuotientProduct T L H)
    (hg : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ChapterF.IsGoldschmidtTriple
        (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q)
        ((H.subgroupOf J).map q))
    (hz : pCore 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) = ⊥)
    (hTH : (T : Subgroup G) ≤ H)
    (hYM : c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤ normalizer (L : Set G))
    (t : (H ⊔ borelResidual T L : Subgroup G))
    (ht : (t : G) ∈ (T : Subgroup G))
    (htY : (t : G) ∈ centralizer
      (c.cubic_lift.map (H ⊔ borelResidual T L).subtype : Set G))
    (hn : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      let A := ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q
      q t ∉ centralizer ((pResidual 2 A).map A.subtype : Set _)) :
    ∀ (y : G) (hy : y ∈ c.cubic_lift.map (H ⊔ borelResidual T L).subtype),
      d.quotientNormalizerAction ⟨y,hYM hy⟩ = 1 := by
  let J := H ⊔ borelResidual T L
  let Y := c.cubic_lift.map J.subtype
  let X := Y ⊔ (T : Subgroup G)
  have hXM : X ≤ normalizer (L : Set G) := sup_le hYM d.normalizes_L
  have hnS : X ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_rfl hXM).trans (source_overlap_normalizes_component_sylow d
      (show (T : Subgroup G) ≤ X from le_sup_right) (single_cubic_join_solvable c hTH))
  let q := d.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let a := d.quotientNormalizerAction.comp (inclusion hXM)
  have ha (x : X) (k : L) : a x (q k) =
      q (L.normalizerMonoidHom ⟨x,hXM x.property⟩ k) :=
    d.quotientNormalizerAction_mk _ _
  obtain ⟨S,hS⟩ := d.local_sylow
  let S' := S.mapSurjective (f := q) (d.quotient.surjective.comp (QuotientGroup.mk'_surjective _))
  have haS (x : X) : (S' : Subgroup (alternatingGroup (Fin 5))).map (a x).toMonoidHom = S' := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (a x).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change a x (q k) ∈ (S' : Subgroup (alternatingGroup (Fin 5)))
    rw [ha]
    apply mem_map_of_mem
    apply (mem_map_iff_mem L.subtype_injective).mp
    rw [hS]
    exact le_normalizer_iff.mp hnS x x.property k (hS ▸ mem_map_of_mem L.subtype hk)
  let e := Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv
  let f := e.symm.toMonoidHom.comp a
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveSylowRadical.sylow_stabilizer_fixes_point S'
  have hfix (x : X) : f x i = i := hi _ (haS x)
  let tx : X := ⟨t,mem_sup_right ht⟩
  have htact : f tx = d.localActor ⟨t,mem_sup_right ht⟩ := by
    apply e.injective
    change e (e.symm (a tx)) = _
    rw [e.apply_symm_apply,Theory.SpecificGroups.Alternating.symmetricAutEquiv_conjNormal]
    exact d.quotientNormalizerAction_eq_localActor ⟨t,mem_sup_right ht⟩
  have htodd : (f tx).sign ≠ 1 := by
    rw [htact]
    exact fun he => single_separating_element_odd d c hg hz hTH t ht hn
      (Equiv.Perm.mem_alternatingGroup.mpr he)
  intro y hy
  let yx : X := ⟨y,mem_sup_left hy⟩
  have hcY : Nat.card Y = 3 :=
    (card_map_of_injective J.subtype_injective).trans c.cubic_card
  have hy3 : yx ^ 3 = 1 := by
    apply Subtype.ext
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨y,hy⟩ : Y)))
    simpa only [Subgroup.coe_pow,hcY,Subgroup.coe_one] using hh
  have hc : f yx * f tx = f tx * f yx := by
    rw [←map_mul,←map_mul]
    congr 1
    exact Subtype.ext (htY y hy)
  have heq : f yx = 1 :=
    Theory.SpecificGroups.Alternating.cubic_eq_one_of_commutes_odd_fixed i _ _
      (hfix yx) (hfix tx) (by rw [←map_pow,hy3,map_one]) htodd hc
  apply e.symm.injective
  exact heq.trans (map_one e.symm).symm
/-- The quotient-action conclusion for the original single-factor source
inputs. The normalizer and inverter are supplied by the original construction. -/
theorem single_original_cubic_quotient_action
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (hqg : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ChapterF.IsGoldschmidtTriple
        (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q)
        ((H.subgroupOf J).map q))
    (hi : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q ⊓
        (H.subgroupOf J).map q = ((T : Subgroup G).subgroupOf J).map q)
    (hz : pCore 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) = ⊥)
    (c : SingleQuotientProduct T L H) :
    let hn := single_cubic_le_normalizer d hH hB hZ hg c
    ∀ (y : G) (hy : y ∈ c.cubic_lift.map (H ⊔ borelResidual T L).subtype),
      d.quotientNormalizerAction ⟨y,hn hy⟩ = 1 := by
  obtain ⟨_,t,ht,htD,htR,_⟩ := single_original_cubic_inverter hH.1.1.2 c hqg hi hz
  exact single_cubic_quotient_action_eq_one d c hqg hz hH.1.1.2
    (single_cubic_le_normalizer d hH hB hZ hg c) t ht htD htR

/-- Trivial quotient action bounds the literal original commutator by O₂(L). -/
theorem single_cubic_commutator_le_core
    (c : SingleQuotientProduct T L H)
    (hYM : c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤ normalizer (L : Set G))
    (ha : ∀ (y : G) (hy : y ∈ c.cubic_lift.map (H ⊔ borelResidual T L).subtype),
      d.quotientNormalizerAction ⟨y,hYM hy⟩ = 1) :
    ⁅L,c.cubic_lift.map (H ⊔ borelResidual T L).subtype⁆ ≤ L.pCoreIn 2 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro y hy l hl
  let l' : L := ⟨l,hl⟩
  let n : L := L.normalizerMonoidHom ⟨y,hYM hy⟩ l'
  let q := QuotientGroup.mk' (pCore 2 L)
  have hfix : q n = q l' := by
    apply d.quotient.injective
    rw [←d.quotientNormalizerAction_mk,ha y hy]
    rfl
  have hc : n * l'⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (n * l'⁻¹) = 1
    rw [map_mul,map_inv,hfix,mul_inv_cancel]
  exact mem_map_of_mem L.subtype hc

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
