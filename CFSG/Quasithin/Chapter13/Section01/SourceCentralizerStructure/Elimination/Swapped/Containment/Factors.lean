module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment

/-!
# The two order-p factors of the exchanged complement

After orbit containment, the actual odd complement embeds in the marked
quotient of the two conjugate C-components. The ambient odd-rank bound and
its source elementary/extraspecial alternative make it an elementary plane.
Each coordinate kernel is its intersection with the corresponding original
C-component: coprimality lifts through the orbit two-core. Conjugation by an
exchanger in N_{T_u}(P) gives two disjoint commuting nontrivial factors, whose
orders force them to generate the plane.

The assembly fills the factor and plane clauses of SwappedData. The subsequent
Inner and Rows modules discharge quotient containment and the model restrictions.
Source: Aschbacher--Smith, original 13.1.12(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding

private theorem second_eq_one_mem_sup {D Q : Type*} [Group D] [Group Q]
    (A N : Subgroup D) (q : D →* Q × Q) (hker : q.ker = N)
    (hA : ∀ a : Q, ∃ x : A, q x = (a,1))
    {x : D} (hx : (q x).2 = 1) : x ∈ A ⊔ N := by
  obtain ⟨a,ha⟩ := hA (q x).1
  have hn : (a : D)⁻¹ * x ∈ N := by
    rw [← hker]
    change q ((a : D)⁻¹ * x) = 1
    rw [map_mul,map_inv,ha]
    exact Prod.ext (by simp) (by simpa using hx)
  have hh := (A ⊔ N).mul_mem (mem_sup_left a.property) (mem_sup_right hn)
  simpa only [mul_inv_cancel_left] using hh

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

/-- The literal intersections with the two exchanged components split P.
The exchanger lies in N_{T_u}(P), with no irreducibility assumption on T_u. -/
theorem Context.swapped_factors_of_containment (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (hcontained : XiP p L ≤ componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))) :
    SwappedFactors ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      ((P : Subgroup (XiP p L)).map (XiP p L).subtype) K := by
  let H := centralizer ({u} : Set G)
  let S := (T : Subgroup G) ⊓ H
  let D := componentOrbit K S
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  have hPD : P₀ ≤ D := (map_subtype_le _).trans hcontained
  have hDH : D ≤ H := (componentOrbit_le_sup _ _).trans (sup_le e.component.1 inf_le_right)
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (h.involution s.mem s.ne_one)
  obtain ⟨t,ht,hm⟩ := h.exists_point_sylow_complement_exchange o s e hr P
  obtain ⟨a,_,_,_,he,hall⟩ := h.exists_component_exchange o s e hH hr
  have hKt : K.conjBy t ≠ K := fun hh => hm (mem_normalizer_iff_map_conj_eq.mpr hh)
  have hgenD : D = K ⊔ K.conjBy t := by
    rcases hall t ht.1.2 with hh | hh
    · exact (hKt hh).elim
    · rw [hh]
      exact he
  have hKD : K ≤ D := le_componentOrbit _ _
  have hCD : K.conjBy t ≤ D := le_iSup (fun b : S => K.conjBy (b : G)) ⟨t,ht.1⟩
  let A := K.subgroupOf D
  let B := (K.conjBy t).subgroupOf D
  have hA : A.IsCComponent := e.component.2.subgroupOf_of_le hKD hDH
  have hB : B.IsCComponent :=
    (SwappedFactorsProof.conjugate_component e.component ht.1.2).2.subgroupOf_of_le hCD hDH
  have hab : A ≠ B := by
    intro hh
    have hh' := congrArg (map D.subtype) hh
    rw [map_subgroupOf_eq_of_le hKD,map_subgroupOf_eq_of_le hCD] at hh'
    exact hKt hh'.symm
  have hgen : A ⊔ B = ⊤ := by
    change K.subgroupOf D ⊔ (K.conjBy t).subgroupOf D = ⊤
    rw [← subgroupOf_sup hKD hCD,← hgenD]
    exact subgroupOf_self D
  let a : A ≃* K := subgroupOfEquivOfLe hKD
  let c : K ≃* K.conjBy t := equivMapOfInjective K (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let b : B ≃* K := (subgroupOfEquivOfLe hCD).trans c.symm
  let aq : XiQuotient A ≃* XiQuotient K := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let bq : XiQuotient B ≃* XiQuotient K := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let : IsSimpleGroup (XiQuotient K) := h.swapped_component_simple o s e hr
  obtain ⟨q,hq,hker,hqa,hqb⟩ := exists_twoCore_product_of_simple_pair A B hA hB hab hgen aq bq
  let product : XiQuotient D ≃* XiQuotient K × XiQuotient K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hD : IsSQTK KnownSimple.IsKnownSimple D :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hDH)).mp (hH.subgroup (D.subgroupOf H))
  have hrank : primeRank p (XiQuotient K × XiQuotient K) ≤ 2 := by
    rw [← primeRank_congr p product]
    exact quotient_stronglyQuasithin hD.stronglyQuasithin p (Fact.out : p.Prime) h.odd
  have hshape := h.swapped_complement_shape P
  obtain ⟨plane⟩ := h.swapped_plane_of_product s e P hcontained product
  have hpCard : Nat.card P₀ = p ^ 2 := (Nat.card_congr plane.toEquiv).trans (plane_card p)
  let : IsMulCommutative P₀ := ⟨⟨fun x y => plane.injective (by
    rw [map_mul,map_mul,mul_comm'])⟩⟩
  let fP := q.comp (inclusion hPD)
  have hfP : Function.Injective fP := by
    apply (MonoidHom.ker_eq_bot_iff fP).mp
    apply bot_unique
    intro x hx
    have hc : inclusion hPD x ∈ q.ker := hx
    rw [hker] at hc
    have hcG : (x : G) ∈ D.pCoreIn 2 := mem_map_of_mem D.subtype hc
    exact Subtype.ext ((hshape.isPGroup.disjoint_of_coprime (isPGroup_pCoreIn 2 D)
      (Nat.coprime_two_right.mpr h.odd)).le_bot ⟨x.property,hcG⟩)
  have hfull : ∀ z : XiQuotient K, ∃ x : A, q x = (z,1) := by
    intro z
    obtain ⟨w,hw⟩ := aq.surjective z
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 A) w
    refine ⟨x,?_⟩
    rw [hqa,hx,hw]
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hKD).mpr
    (cComponentOrbit_le_normalizer e.component (show S ≤ H from inf_le_right))
  let f := (MonoidHom.snd (XiQuotient K) (XiQuotient K)).comp fP
  have hfker : f.ker = K.subgroupOf P₀ := by
    ext x
    change (q (inclusion hPD x)).2 = 1 ↔ (x : G) ∈ K
    constructor
    · intro hx
      have hxAN := second_eq_one_mem_sup A (pCore 2 D) q hker hfull hx
      have hxbar : QuotientGroup.mk' (pCore 2 D) (inclusion hPD x) ∈
          A.map (QuotientGroup.mk' (pCore 2 D)) := by
        have hm := mem_map_of_mem (QuotientGroup.mk' (pCore 2 D)) hxAN
        rwa [Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq] at hm
      exact SwappedFactorsProof.mem_normal_factor_of_quotient_mem h.odd A (pCore 2 D)
        (P₀.subgroupOf D) pCore_isPGroup hshape.isPGroup.comap_subtype
        (show inclusion hPD x ∈ P₀.subgroupOf D from x.property) hxbar
    · intro hx
      exact congrArg Prod.snd (hqa ⟨inclusion hPD x,hx⟩)
  have hne : P₀ ⊓ K ≠ ⊥ := by
    let : IsCyclic f.range := SwappedFactorsProof.cyclic_pSubgroup_of_product_rank h.odd
      hrank _ (hshape.isPGroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    intro hbot
    have hk : f.ker = ⊥ := by
      rw [hfker,← inf_subgroupOf_right K P₀,inf_comm K P₀,hbot,bot_subgroupOf]
    have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hk
    exact hshape.not_isCyclic (isCyclic_of_injective f.rangeRestrict
      (fun x y hh => hf (congrArg Subtype.val hh)))
  have hconj : (P₀ ⊓ K).conjBy t = P₀ ⊓ K.conjBy t := by
    change (P₀ ⊓ K).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective]
    change P₀.conjBy t ⊓ K.conjBy t = _
    rw [show P₀.conjBy t = P₀ from mem_normalizer_iff_map_conj_eq.mp ht.2]
  have hd : Disjoint (P₀ ⊓ K) ((P₀ ⊓ K).conjBy t) := by
    rw [hconj]
    apply disjoint_def.mpr
    intro x hx hy
    let xD : D := ⟨x,hPD hx.1⟩
    have hxa := hqa (⟨xD,hx.2⟩ : A)
    have hxb := hqb (⟨xD,hy.2⟩ : B)
    have hxq : q xD = 1 := Prod.ext
      (by simpa using congrArg Prod.fst hxb)
      (by simpa using congrArg Prod.snd hxa)
    exact congrArg Subtype.val (hfP (show fP ⟨x,hx.1⟩ = fP 1 by
      change q xD = q 1
      simpa only [map_one] using hxq))
  have hBP : (P₀ ⊓ K).conjBy t ≤ P₀ := hconj ▸ inf_le_left
  have hcentral : P₀ ⊓ K ≤ centralizer ((P₀ ⊓ K).conjBy t : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨b,hBP hb⟩ : P₀) (⟨a,ha.1⟩ : P₀))
  have hsizeA : p ≤ Nat.card (P₀ ⊓ K : Subgroup G) := by
    obtain ⟨n,hn⟩ := (hshape.isPGroup.to_le (show P₀ ⊓ K ≤ P₀ from inf_le_left)).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hz
      exact hne (card_eq_one.mp (by simpa [hz] using hn))
    rw [hn]
    exact (pow_one p).symm.trans_le (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega))
  have hsizeB : Nat.card ((P₀ ⊓ K).conjBy t) = Nat.card (P₀ ⊓ K : Subgroup G) :=
    (Nat.card_congr (equivMapOfInjective (P₀ ⊓ K) (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).toEquiv).symm
  obtain ⟨ep,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hcentral
  have hsize : Nat.card ((P₀ ⊓ K) ⊔ (P₀ ⊓ K).conjBy t : Subgroup G) =
      Nat.card (P₀ ⊓ K : Subgroup G) * Nat.card (P₀ ⊓ K : Subgroup G) := by
    rw [← Nat.card_congr ep.toEquiv,Nat.card_prod,hsizeB]
  refine ⟨h.component_moved_of_reducible o s e hH hr,t,ht,hm,?_,hd,
    commutator_eq_bot_iff_le_centralizer.mpr hcentral⟩
  apply (eq_of_le_of_card_ge (sup_le inf_le_left hBP) ?_).symm
  rw [hpCard,hsize,pow_two]
  exact Nat.mul_le_mul hsizeA hsizeA

/-- Quotient containment and the model row now supply all five source clauses.
The two remaining premises stay with this task's source assembly. -/
theorem Context.swapped_data_of_quotient_row (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (hquot : quotientImage (centralizer ({u} : Set G))
        ((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≤
      quotientImage (centralizer ({u} : Set G))
        (componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))))
    (hrow : SwappedRow p (XiQuotient K)) :
    SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) := by
  exact h.swapped_data_of_quotient_geometry o s e hr P hquot
    (fun contained => ⟨h.swapped_factors_of_containment o s e hr P contained,hrow⟩)

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
