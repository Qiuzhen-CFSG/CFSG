module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Normalizer
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.CharacteristicTwo.Core
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Rows
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OddStarModels
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SylowBlocks

/-!
# The characteristic-two exchanged-component pair

For the binary, Suzuki and J₁ quotient rows, solvable overgroups of the
literal orbit Sylow subgroup normalize it. Lifting through O₂ of that orbit
puts its Sylow subgroup in the point core R=O₂(XT_u); consequently R is
Sylow in KR. The genuine C.2.7 input then makes K a block. Distinct blocks
with quasisimple two-core quotient commute, so the residual-factor argument
constructs the actual normalizer-invariant pair of order-p lines.

For the odd-prime PSL₂ row, the actual star model leaves only orders 60 or
168. The image of XT_u intersect K is solvable and contains a Sylow
2-subgroup and the injective order-p axis, with p>3. Its index is at most
three, contradicting simplicity. This retains the actual quotient maps and
requires no irreducibility of T_u and no normality of K in C_G(u).

The small-order argument adapts ModelReduction.SmallQuotients; its coset
bound uses the attributed ATLAS port in Theory.AtlasPort.OtherSporadic.
Source: Aschbacher--Smith, original 13.1.12(3), printed pp.874--875;
C.1.9, C.2.7, and the swapped argument of 1.3.8, printed pp.513--514.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding Chapter1.RadicalExclusions
open Chapter1.XiEmbedding.SwappedSylow
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

/-- Quotient Borel normalization puts the literal orbit Sylow subgroup in O₂(XT_u). -/
theorem Context.swapped_orbit_sylow_le_core (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hn : ∀ (U : Sylow 2 (XiQuotient K × XiQuotient K))
      (A : Subgroup (XiQuotient K × XiQuotient K)),
      Group.IsSolvable (A ⊔ (U : Subgroup _) : Subgroup _) →
      A ≤ normalizer (U : Set (XiQuotient K × XiQuotient K))) :
    ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ⊓
      componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ≤
      (XiP p L ⊔ ((T : Subgroup G) ⊓ centralizer ({u} : Set G))).pCoreIn 2 := by
  let X := XiP p L
  let S := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let D := componentOrbit K S
  let P₀ := (P : Subgroup X).map X.subtype
  let q := QuotientGroup.mk' (pCore 2 D)
  let B := P₀.subgroupOf D
  obtain ⟨V,hV⟩ := h.swapped_orbit_sylow s e
  have hVeq : (V : Subgroup D) = S.subgroupOf D := by
    have hh := congrArg (fun Z : Subgroup G => Z.subgroupOf D) hV
    change ((V : Subgroup D).map D.subtype).comap D.subtype = _ at hh
    rw [comap_map_eq_self_of_injective D.subtype_injective] at hh
    change (V : Subgroup D) = (S ⊓ D).subgroupOf D at hh
    simpa only [inf_subgroupOf_right] using hh
  have hcore : pCore 2 D ≤ S.subgroupOf D := by
    rw [← hVeq]
    exact fitting_pCore_le_sylow V
  have hpre : ((S.subgroupOf D).map q).comap q = S.subgroupOf D := by
    apply comap_map_eq_self
    simpa only [q,QuotientGroup.ker_mk'] using hcore
  let Vbar := V.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hVbar : (Vbar : Subgroup (XiQuotient D)) = (S.subgroupOf D).map q := by
    rw [Sylow.coe_mapSurjective,hVeq]
  let J := X ⊔ S
  let C := B ⊔ S.subgroupOf D
  let := h.point_radical_join_solvable (u := u)
  have hCJ : C ≤ J.subgroupOf D := sup_le
    (fun x hx => (show P₀ ≤ J from (map_subtype_le _).trans le_sup_left) hx)
    (fun x hx => (show S ≤ J from le_sup_right) hx)
  let f : C →* J := (D.subtype.subgroupComap J).comp (inclusion hCJ)
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective (f := f) (by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : J => (x : G)) he)
  have hsol : Group.IsSolvable (B.map q ⊔ (Vbar : Subgroup (XiQuotient D)) : Subgroup _) := by
    rw [hVbar,← Subgroup.map_sup]
    exact Group.isSolvable_of_surjective (q.subgroupMap_surjective C)
  let := hsol
  obtain ⟨product⟩ := h.swapped_quotient_product o s e hr
  let U := Vbar.mapSurjective (f := product.toMonoidHom) product.surjective
  let A := (B.map q).map product.toMonoidHom
  have hsolA : Group.IsSolvable (A ⊔ (U : Subgroup (XiQuotient K × XiQuotient K)) : Subgroup _) := by
    change Group.IsSolvable (((B.map q).map product.toMonoidHom) ⊔
      (Vbar : Subgroup (XiQuotient D)).map product.toMonoidHom : Subgroup _)
    rw [← Subgroup.map_sup]
    exact Group.isSolvable_of_surjective (product.toMonoidHom.subgroupMap_surjective _)
  have hnorm : B.map q ≤ normalizer ((S.subgroupOf D).map q : Set (XiQuotient D)) := by
    apply (map_le_map_iff_of_injective (f := product.toMonoidHom) product.injective).mp
    rw [map_normalizer_eq_of_bijective _ product.bijective]
    have hh := hn U A hsolA
    change A ≤ normalizer ((Vbar : Subgroup (XiQuotient D)).map product.toMonoidHom : Set _) at hh
    rwa [hVbar] at hh
  have hPN : P₀ ≤ normalizer (S ⊓ D : Subgroup G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    let aD : D := ⟨a,(map_subtype_le (P : Subgroup X) |>.trans d.contained) ha⟩
    let xD : D := ⟨x,hx.2⟩
    have hc : q (aD * xD * aD⁻¹) ∈ (S.subgroupOf D).map q := by
      rw [map_mul,map_mul,map_inv]
      exact (mem_normalizer_iff.mp (hnorm (mem_map_of_mem q ha)) _).mp (mem_map_of_mem q hx.1)
    have hs : aD * xD * aD⁻¹ ∈ S.subgroupOf D := by
      rw [← hpre]
      exact hc
    exact ⟨hs,(aD * xD * aD⁻¹).property⟩
  have hSN : S ≤ normalizer (S ⊓ D : Subgroup G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨(mem_normalizer_iff.mp (S.le_normalizer ht) x).mp hx.1,
      (mem_normalizer_iff.mp (le_normalizer_componentOrbit K S ht) x).mp hx.2⟩
  have hXN : X ≤ normalizer (S ⊓ D : Subgroup G) := by
    change XiP p L ≤ normalizer (S ⊓ D : Subgroup G)
    rw [← Chapter1.RadicalActions.sylow_sup (Chapter1.RadicalNormalizers.XiP_quotient_isPGroup p h.odd L) P]
    exact sup_le ((h.radical_core_le_point_sylow s).trans hSN) hPN
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
    (inf_le_left.trans le_sup_right) (sup_le hXN hSN)

/-- The point core is Sylow in its join with K once it contains the orbit Sylow subgroup. -/
theorem Context.swapped_core_sylow_of_orbit_bound (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    (e : Escape T L p u K) (hr : ¬ ComponentNormalizerIrreducible L K p u)
    (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hb : ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ⊓
      componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) ≤
      (XiP p L ⊔ ((T : Subgroup G) ⊓ centralizer ({u} : Set G))).pCoreIn 2) :
    IsSylowIn 2 (centralizerCore T L p u) (K ⊔ centralizerCore T L p u) := by
  let R := centralizerCore T L p u
  let S := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  have hSR : S ⊓ K ≤ R := by
    rw [show R = _ from h.core_eq_local_join o s hnt]
    exact (inf_le_inf_left S (le_componentOrbit K S)).trans hb
  have hSK := isSylowIn_iff.mp (IndexTwo.isSylowIn_inf_of_subnormal e.full_sylow
    e.component.1 e.component.2.subnormal)
  have hR : IsPGroup 2 R := by
    rw [show R = _ from h.core_eq_local_join o s hnt]
    exact isPGroup_pCoreIn 2 _
  have hRK := h.swapped_core_normalizes o s hnt e hr P d
  refine isSylowIn_iff.mpr ⟨hR,le_sup_right,?_⟩
  intro U hU hRU hUKR
  have he : U ⊓ K = S ⊓ K := hSK.2.2 _ (hU.to_le inf_le_left)
    (le_inf (hSR.trans hRU) inf_le_right) inf_le_right
  apply le_antisymm _ hRU
  intro u hu
  have hprod : u ∈ (K : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K R hRK]
    exact hUKR hu
  obtain ⟨k,hk,r,hrR,hkr⟩ := hprod
  have hkU : k ∈ U := by
    have hh := U.mul_mem hu (U.inv_mem (hRU hrR))
    rwa [← hkr,mul_inv_cancel_right] at hh
  rw [← hkr]
  exact R.mul_mem (hSR (he ▸ (show k ∈ U ⊓ K from ⟨hkU,hk⟩))) hrR

omit [Fact p.Prime] in
/-- C.1.9 is applied inside the literal involution centralizer, then mapped back to G. -/
theorem Escape.exchanged_blocks_commute (e : Escape T L p u K)
    {t : G} (ht : t ∈ centralizer ({u} : Set G)) (hm : t ∉ normalizer (K : Set G))
    (hb : ChapterC.IsBlock (K.subgroupOf (centralizer ({u} : Set G)))) :
    ⁅K,K.conjBy t⁆ = ⊥ := by
  let H := centralizer ({u} : Set G)
  let A := K.subgroupOf H
  let B := A.conjBy (⟨t,ht⟩ : H)
  have hAm : A.map H.subtype = K := map_subgroupOf_eq_of_le e.component.1
  have hBm : B.map H.subtype = K.conjBy t := by
    change (A.map (MulAut.conj (⟨t,ht⟩ : H)).toMonoidHom).map H.subtype = _
    rw [map_map]
    change A.map ((MulAut.conj t).toMonoidHom.comp H.subtype) = _
    rw [← map_map,hAm]
    rfl
  have hB : ChapterC.IsBlock B := hb.map_equiv (MulAut.conj (⟨t,ht⟩ : H))
  let a : A ≃* K := subgroupOfEquivOfLe e.component.1
  let aq : XiQuotient A ≃* XiQuotient K := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hqA := e.quotient.of_mulEquiv aq.symm
  have hne : A ≠ B := by
    intro he
    have he := congrArg (Subgroup.map H.subtype) he
    rw [hAm,hBm] at he
    exact hm (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc := hb.commutator_eq_bot_of_quasisimple_quotient hB hqA hne
  have hc := congrArg (Subgroup.map H.subtype) hc
  rwa [map_commutator,hAm,hBm,Subgroup.map_bot] at hc

/-- The genuine Sylow case of C.2.7 gives the block and hence the two invariant axes. -/
theorem Context.swapped_line_pair_of_core_sylow (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p) (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    (e : Escape T L p u K) (hr : ¬ ComponentNormalizerIrreducible L K p u)
    (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hf : generalizedFitting K = pCore 2 K)
    (hs : IsSylowIn 2 (centralizerCore T L p u) (K ⊔ centralizerCore T L p u)) :
    Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) := by
  have hi := h.swapped_characteristic_two_input o c s hnt e hr P d hf
  have hb := (ChapterC.C27Source.source_chiZero_of_sylow_input hi hs).1
  have ht := Classical.choose_spec d.factors.2
  exact h.swapped_line_pair_of_commuting e P d
    (e.exchanged_blocks_commute ht.1.1.2 ht.2.1 hb)

private theorem prime_eq_of_dvd {p r a : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hp3 : 3 < p) (hdiv : p ∣ 2 ^ a * 3 * r) : p = r := by
  rcases hp.dvd_mul.mp hdiv with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have he := (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      omega
    · have he := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hp hr).mp h

private theorem no_small_solvable_sylow_overgroup {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : Nat.card Q = 60 ∨ Nat.card Q = 168)
    (S : Sylow 2 Q) (J : Subgroup Q) [Group.IsSolvable J]
    (hSJ : (S : Subgroup Q) ≤ J) (hpJ : p ∣ Nat.card J) : False := by
  have hpQ := hpJ.trans J.card_subgroup_dvd_card
  have hidx : J.index ≤ 3 := by
    have hj := J.card_mul_index
    rcases hq with hq | hq
    · have hp5 : p = 5 := prime_eq_of_dvd (a := 2) hp (by decide) hp3 (by simpa [hq] using hpQ)
      have hfour : 4 ∣ Nat.card J :=
        (S.pow_dvd_card_of_pow_dvd_card (n := 2) (by norm_num [hq])).trans (card_dvd_of_le hSJ)
      have h20 : 20 ∣ Nat.card J :=
        (show Nat.Coprime 4 5 by decide).mul_dvd_of_dvd_of_dvd hfour (hp5 ▸ hpJ)
      have hpos := Nat.card_pos (α := J)
      have hle := Nat.le_of_dvd hpos h20
      rw [hq] at hj
      nlinarith
    · have hp7 : p = 7 := prime_eq_of_dvd (a := 3) hp (by decide) hp3 (by simpa [hq] using hpQ)
      have height : 8 ∣ Nat.card J :=
        (S.pow_dvd_card_of_pow_dvd_card (n := 3) (by norm_num [hq])).trans (card_dvd_of_le hSJ)
      have h56 : 56 ∣ Nat.card J :=
        (show Nat.Coprime 8 7 by decide).mul_dvd_of_dvd_of_dvd height (hp7 ▸ hpJ)
      have hpos := Nat.card_pos (α := J)
      have hle := Nat.le_of_dvd hpos h56
      rw [hq] at hj
      nlinarith
  have he : J = ⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt J (by
    have hh := Nat.factorial_le hidx
    norm_num at hh
    rcases hq with hq | hq <;> omega)
  have hsolv : Group.IsSolvable Q := Group.isSolvable_of_surjective
    (f := J.subtype) (by rw [he]; exact topEquiv.surjective)
  exact Group.IsPerfect.not_isSolvable Q hsolv


private theorem Context.swapped_not_small_quotient_card (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype)) :
    Nat.card (XiQuotient K) ≠ 60 ∧ Nat.card (XiQuotient K) ≠ 168 := by
  let X := XiP p L
  let S₀ := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let P₀ := (P : Subgroup X).map X.subtype
  have hp3 : 3 < p := (XiP_oddQuotient_of_A36
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    h.maximal.1.1
    (uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2)
    h.nonquasisimple h.odd h.divides).1
  let _ := e.quotient
  let _ := h.swapped_component_simple o s e hr
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((X ⊔ S₀) ⊓ K).subgroupOf K
  let J := B.map q
  let A := (P₀ ⊓ K).subgroupOf K
  let _ := h.point_radical_join_solvable (u := u)
  let _ : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion (show (X ⊔ S₀) ⊓ K ≤ X ⊔ S₀ from inf_le_left)).comp
      (subgroupOfEquivOfLe (show (X ⊔ S₀) ⊓ K ≤ K from inf_le_right)).toMonoidHom)
    ((inclusion_injective inf_le_left).comp (subgroupOfEquivOfLe inf_le_right).injective)
  let _ : Group.IsSolvable J := Group.isSolvable_of_surjective (q.subgroupMap_surjective B)
  obtain ⟨U, hU⟩ := Section02.IndexTwo.isSylowIn_inf_of_subnormal e.full_sylow
    e.component.1 e.component.2.subnormal
  let S := U.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hS : (S : Subgroup (XiQuotient K)) ≤ J := by
    rw [Sylow.coe_mapSurjective]
    apply map_mono
    have hh : (U : Subgroup K) = (S₀ ⊓ K).subgroupOf K := by
      simpa only [Subgroup.subgroupOf, comap_map_eq_self_of_injective K.subtype_injective] using
        congrArg (fun Z : Subgroup G => Z.subgroupOf K) hU
    rw [hh]
    exact comap_mono (inf_le_inf_right K le_sup_right)
  have hA : Nat.card A = p :=
    (Nat.card_congr (subgroupOfEquivOfLe (show P₀ ⊓ K ≤ K from inf_le_right)).toEquiv).trans
      (ModelReduction.swapped_intersection_card d.plane d.factors)
  have hdis : Disjoint A (pCore 2 K) :=
    ((h.swapped_complement_shape P).isPGroup.to_le inf_le_left).comap_subtype.disjoint_of_coprime
      pCore_isPGroup (Nat.coprime_two_right.mpr h.odd)
  have hi : Function.Injective (q.comp A.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hh : (a : K) ∈ pCore 2 K := (QuotientGroup.eq_one_iff _).mp ha
    exact Subtype.ext (hdis.le_bot ⟨a.property, hh⟩)
  have hcard : Nat.card (A.map q) = p := by
    calc
      Nat.card (A.map q) = Nat.card (q.comp A.subtype).range := by
        rw [MonoidHom.range_comp, range_subtype]
      _ = Nat.card A := (Nat.card_congr (Equiv.ofInjective (q.comp A.subtype) hi)).symm
      _ = p := hA
  have hpJ : p ∣ Nat.card J := by
    rw [← hcard]
    exact card_dvd_of_le (map_mono (comap_mono (inf_le_inf_right K
      ((map_subtype_le (P : Subgroup X)).trans le_sup_left))))
  have hh : ¬ (Nat.card (XiQuotient K) = 60 ∨ Nat.card (XiQuotient K) = 168) :=
    fun hq => no_small_solvable_sylow_overgroup (Fact.out : p.Prime) hp3 hq S J hS hpJ
  exact not_or.mp hh

/-- The complete characteristic-two construction, covering all four source model rows. -/
theorem Context.characteristic_two_line_pair (h : Context T L p)
    (o : OrbitFacts T L p) (c : Control T L p) (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    (e : Escape T L p u K) (hr : ¬ ComponentNormalizerIrreducible L K p u)
    (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hf : generalizedFitting K = pCore 2 K) :
    Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) := by
  have hfinish (hn : ∀ (U : Sylow 2 (XiQuotient K × XiQuotient K))
      (A : Subgroup (XiQuotient K × XiQuotient K)),
      Group.IsSolvable (A ⊔ (U : Subgroup _) : Subgroup _) →
      A ≤ normalizer (U : Set (XiQuotient K × XiQuotient K))) :
      Nonempty (NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) := by
    have hbound := h.swapped_orbit_sylow_le_core o s e hr P d hn
    have hs := h.swapped_core_sylow_of_orbit_bound o s hnt e hr P d hbound
    exact h.swapped_line_pair_of_core_sylow o c s hnt e hr P d hf hs
  cases d.row with
  | linear_even n hn _ hm =>
    apply hfinish
    intro U A hsol
    let := hsol
    exact binary_model_prod_le_normalizer hn hm U A
  | suzuki m hm _ iso =>
    apply hfinish
    intro U A hsol
    let := hsol
    exact suzuki_model_prod_le_normalizer hm iso.some U A
  | janko _ iso =>
    apply hfinish
    intro U A hsol
    let := hsol
    exact janko_one_model_prod_le_normalizer iso.some U A
  | linear_prime r hp ho hm =>
    have hi := h.swapped_characteristic_two_input o c s hnt e hr P d hf
    have hc := ModelReduction.source_odd_prime_small_card hi hp ho hm
    have hn := h.swapped_not_small_quotient_card o s e hr P d
    exact (hc.elim hn.1 hn.2).elim


end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
