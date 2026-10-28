module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SmallRadicalEdges

/-!
# The full field-sized replacement group

When the replacement image has order q, its actual edge group factors as
T = Q Z' and [Q,Z'] = [Z,Z'] is central and elementary in T. Thus the third
lower commutators of T and Q agree, as do their fourth-power subgroups.
Each common subgroup is normal in both adjacent stabilizers, so the original
MS characteristic condition makes it trivial. The whole replacement radical
therefore has class at most two and exponent at most four. In particular,
these bounds include its complete component-fixed attachment.

In the proper nonsylow branch the original odd-index witness supplies |D|=q
and |R₀|=q³. The compatible replacement projection has its exact two-core
kernel in both subgroups, so the original radical restricted to the replacement
has index q² over the replacement radical. The final applications discharge
the field-sized premise using that same original witness. These are constraints
on the proper-root case, not a radical-saturation or field-degree conclusion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the critical-root calculation in (3.3), printed p.867, and the radical
comparison needed for (3.7), printed pp.872--877. The common-normal-subgroup
exclusion is source (2.1)(iii).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

private theorem normalized_commutator {G : Type*} [Group G]
    (S A B : Subgroup G) (hA : S ≤ normalizer (A : Set G))
    (hB : S ≤ normalizer (B : Set G)) : S ≤ normalizer ((⁅A,B⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hx),
    mem_normalizer_iff_map_conj_eq.mp (hB hx)]

private theorem normalized_sup {G : Type*} [Group G]
    (S A B : Subgroup G) (hA : S ≤ normalizer (A : Set G))
    (hB : S ≤ normalizer (B : Set G)) : S ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp (hA hx),
    mem_normalizer_iff_map_conj_eq.mp (hB hx)]

private theorem third_commutator_eq_of_central_supplement {G : Type*} [Group G]
    (T Q E : Subgroup G) (hjoin : Q ⊔ E = T)
    (hN : T ≤ normalizer (Q : Set G)) (hE : ⁅E,E⁆ = ⊥)
    (hcentral : ⁅Q,E⁆ ≤ centralizer (T : Set G)) :
    ⁅⁅T,T⁆,T⁆ = ⁅⁅Q,Q⁆,Q⁆ := by
  let W := ⁅Q,E⁆
  let D := ⁅Q,Q⁆
  let C := ⁅D,Q⁆
  have hQT : Q ≤ T := le_sup_left.trans_eq hjoin
  have hET : E ≤ T := le_sup_right.trans_eq hjoin
  have hWn : T ≤ normalizer (W : Set G) := by
    rw [←hjoin]
    exact sup_le (normalizer_commutator_ge_left Q E) (normalizer_commutator_ge_right Q E)
  have hDn : T ≤ normalizer (D : Set G) := normalized_commutator T Q Q hN hN
  have hCn : T ≤ normalizer (C : Set G) := normalized_commutator T D Q hDn hN
  have hDT : D ≤ T := (Subgroup.commutator_le_sup Q Q).trans ((sup_idem Q).le.trans hQT)
  have hWT : W ≤ T := (Subgroup.commutator_le_sup Q E).trans_eq hjoin
  have hWQ : ⁅W,Q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hcentral.trans (centralizer_le hQT))
  have hDE : ⁅D,E⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hWQ (by
    rw [commutator_comm E Q]
    exact hWQ)
  have hTQ : ⁅T,Q⁆ ≤ D ⊔ W := by
    rw [←hjoin]
    apply commutator_sup_le_of_relative_normal T Q E Q (D ⊔ W)
      (normalized_sup T D W hDn hWn) hQT hET le_sup_left
    rw [commutator_comm E Q]
    exact le_sup_right
  have hTE : ⁅T,E⁆ ≤ D ⊔ W := by
    rw [←hjoin]
    exact commutator_sup_le_of_relative_normal T Q E E (D ⊔ W)
      (normalized_sup T D W hDn hWn) hQT hET le_sup_right (hE.le.trans bot_le)
  have hTT : ⁅T,T⁆ ≤ D ⊔ W := by
    rw [←hjoin,commutator_comm]
    exact commutator_sup_le_of_relative_normal T Q E (Q ⊔ E) (D ⊔ W)
      (normalized_sup T D W hDn hWn) hQT hET
      (by rw [hjoin,commutator_comm]; exact hTQ)
      (by rw [hjoin,commutator_comm]; exact hTE)
  have hDTcomm : ⁅D,T⁆ ≤ C := by
    rw [commutator_comm,←hjoin]
    exact commutator_sup_le_of_relative_normal T Q E D C hCn hQT hET
      (by rw [commutator_comm])
      (by rw [commutator_comm,hDE]; exact bot_le)
  apply le_antisymm _ (commutator_mono (commutator_mono hQT hQT) hQT)
  exact (commutator_mono hTT le_rfl).trans
    (commutator_sup_le_of_relative_normal T D W T C hCn hDT hWT hDTcomm
      ((commutator_eq_bot_iff_le_centralizer.mpr hcentral).le.trans bot_le))

private theorem factor_of_relative_sup {G : Type*} [Group G]
    (T Q E : Subgroup G) (hjoin : Q ⊔ E = T)
    (hN : T ≤ normalizer (Q : Set G)) {x : G} (hx : x ∈ T) :
    ∃ q ∈ Q, ∃ e ∈ E, q * e = x := by
  have hQT : Q ≤ T := le_sup_left.trans_eq hjoin
  have hET : E ≤ T := le_sup_right.trans_eq hjoin
  let : (Q.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hN
  have hsup : Q.subgroupOf T ⊔ E.subgroupOf T = ⊤ := by
    rw [←subgroupOf_sup hQT hET,hjoin,subgroupOf_self]
  obtain ⟨q,hq,e,he,heq⟩ := mem_sup_of_normal_left.mp
    (hsup.symm ▸ (mem_top (⟨x,hx⟩ : T)))
  exact ⟨q.val,hq,e.val,he,congrArg Subtype.val heq⟩

private theorem fourth_power_mul {G : Type*} [Group G]
    (q e : G) (he : e^2=1) (hc : Commute q ⁅e,q⁆) (hc2 : ⁅e,q⁆^2=1) :
    (q*e)^4=q^4 := by
  have hs : (q*e)^2 = q^2*⁅e,q⁆ := by
    calc
      _ = q*(e*q*e⁻¹)*e^2 := by simp only [pow_two]; group
      _ = q*(⁅e,q⁆*q) := by rw [he,mul_one]; simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
      _ = q^2*⁅e,q⁆ := by rw [hc.symm.eq,pow_two,mul_assoc]
  rw [show (4:ℕ)=2*2 from rfl,pow_mul,hs,(hc.pow_left 2).mul_pow,hc2,mul_one,←pow_mul]

private def fourthPowers {G : Type*} [Group G] (A : Subgroup G) : Subgroup G :=
  (closure (Set.range fun a : A => a^4)).map A.subtype

private theorem fourthPowers_normalized {G : Type*} [Group G] (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (fourthPowers A : Set G) := by
  let : (closure (Set.range fun a : A => a^4)).Characteristic :=
    closure_range_pow_characteristic 4
  exact normalizer_le_normalizer_characteristic_image A _

private theorem mem_fourthPowers {G : Type*} [Group G] (A : Subgroup G)
    {a : G} (ha : a ∈ A) : a^4 ∈ fourthPowers A :=
  mem_map_of_mem A.subtype (show (⟨a,ha⟩ : A)^4 ∈ closure (Set.range fun x : A => x^4) from
    Subgroup.subset_closure ⟨⟨a,ha⟩,rfl⟩)

private theorem fourthPowers_le {G : Type*} [Group G] (A B : Subgroup G)
    (h : ∀ a ∈ A, a^4 ∈ B) : fourthPowers A ≤ B := by
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  rintro _ ⟨a,rfl⟩
  exact h a a.property

private theorem fourthPowers_eq_of_central_elementary_supplement {G : Type*} [Group G]
    (T Q E : Subgroup G) (hjoin : Q ⊔ E = T)
    (hN : T ≤ normalizer (Q : Set G))
    (hE : ∀ e ∈ E, e^2=1) (hcentral : ⁅Q,E⁆ ≤ centralizer (T : Set G))
    (hcomm : ∀ c ∈ ⁅Q,E⁆, c^2=1) : fourthPowers T = fourthPowers Q := by
  have hQT : Q ≤ T := le_sup_left.trans_eq hjoin
  apply le_antisymm
  · apply fourthPowers_le
    intro x hx
    obtain ⟨q,hq,e,he,rfl⟩ := factor_of_relative_sup T Q E hjoin hN hx
    have hc : ⁅e,q⁆ ∈ ⁅Q,E⁆ := by rw [commutator_comm]; exact commutator_mem_commutator he hq
    rw [fourth_power_mul q e (hE e he) (hcentral hc q (hQT hq)) (hcomm _ hc)]
    exact mem_fourthPowers Q hq
  · exact fourthPowers_le Q _ (fun q hq => mem_fourthPowers T (hQT hq))



open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full kernel displacement is central and elementary in the actual edge. -/
theorem replacement_field_sized_edge_displacement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅Q d.radical a,Z d.radical z⁆ ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
      ∀ x ∈ ⁅Q d.radical a,Z d.radical z⁆, x^2=1 := by
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have he := (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
  have hm := replacement_field_sized_whole_kernel_commutator h d path hb hat hzt hsize
  have hWa : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
    ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path
  have hWz : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical z := by
    apply le_normalizer_iff_commutator_le_right.mp
    apply (Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) ?_).trans
      (Z_normalized d.radical z)
    rw [path.critical.1]
  have hWQ := hWa.trans (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical a path.start_color))
  have hWE := hWz.trans (Z d.radical z).le_centralizer
  rw [hm]
  refine ⟨?_,?_⟩
  · rw [←he]
    exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hWQ) (le_centralizer_iff.mp hWE))
  · intro x hx
    exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Z d.radical z)) ⟨x,hWz hx⟩)

/-- MS3 eliminates the third lower commutator of the full edge group. -/
theorem replacement_field_sized_edge_class_two
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅⁅Q d.radical t,Q d.radical t⁆,Q d.radical t⁆ = ⊥ := by
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hTedge : Q d.radical t ≤ stabilizer d.radical a ⊓ stabilizer d.radical t := by
    rw [Q_h_eq_edge d.radical ht hat]
  have hnQ := hTedge.trans inf_le_left |>.trans (Q_normalized d.radical a)
  have he := third_commutator_eq_of_central_supplement
    (Q d.radical t) (Q d.radical a) (Z d.radical z)
    (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1 hnQ
    (commutator_self_eq_bot_iff.mpr inferInstance)
    (replacement_field_sized_edge_displacement h d path hb hat hzt hsize).1
  let N := ⁅⁅Q d.radical t,Q d.radical t⁆,Q d.radical t⁆
  have hNT : N ≤ Q d.radical t := (Q d.radical t).lowerCentralSeries_le_self 2
  apply no_common_normal_at_edge d.radical (replacement_characteristic h d) a t path.start_color hat N
    (hNT.trans hTedge)
  · apply normal_subgroupOf_of_le_normalizer
    dsimp only [N]
    rw [he]
    exact normalized_commutator _ _ _
      (normalized_commutator _ _ _ (Q_normalized d.radical a) (Q_normalized d.radical a))
      (Q_normalized d.radical a)
  · exact normal_subgroupOf_of_le_normalizer
      (normalized_commutator _ _ _
        (normalized_commutator _ _ _ (Q_normalized d.radical t) (Q_normalized d.radical t))
        (Q_normalized d.radical t))

/-- MS3 also eliminates every fourth power, including powers of the fixed factor. -/
theorem replacement_field_sized_edge_exponent_four
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ∀ x ∈ Q d.radical t, x^4=1 := by
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hTedge : Q d.radical t ≤ stabilizer d.radical a ⊓ stabilizer d.radical t := by
    rw [Q_h_eq_edge d.radical ht hat]
  have hnQ := hTedge.trans inf_le_left |>.trans (Q_normalized d.radical a)
  have hc := replacement_field_sized_edge_displacement h d path hb hat hzt hsize
  have he := fourthPowers_eq_of_central_elementary_supplement
    (Q d.radical t) (Q d.radical a) (Z d.radical z)
    (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1 hnQ
    (fun e he => congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Z d.radical z)) ⟨e,he⟩)) hc.1 hc.2
  have hNT : fourthPowers (Q d.radical t) ≤ Q d.radical t := map_subtype_le _
  have hzero : fourthPowers (Q d.radical t) = ⊥ := by
    apply no_common_normal_at_edge d.radical (replacement_characteristic h d) a t path.start_color hat
      _ (hNT.trans hTedge)
    · apply normal_subgroupOf_of_le_normalizer
      rw [he]
      exact (Q_normalized d.radical a).trans (fourthPowers_normalized _)
    · exact normal_subgroupOf_of_le_normalizer
        ((Q_normalized d.radical t).trans (fourthPowers_normalized _))
  intro x hx
  exact hzero.le (mem_fourthPowers _ hx)



/-- Class and exponent bounds for the literal replacement radical, not just its image. -/
theorem replacement_field_sized_radical_class_two_and_exponent_four
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅⁅d.radical,d.radical⁆,d.radical⁆ = ⊥ ∧ ∀ x ∈ d.radical, x^4=1 := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  have hc := replacement_field_sized_edge_class_two h d path hb hat hzt hsize
  have hp := replacement_field_sized_edge_exponent_four h d path hb hat hzt hsize
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hn
    cases he : color d.radical t
    · exact (hn he.symm).elim
    · rfl
  have hv : ∃ v, t = hVertex d.radical v := by
    cases t with
    | inl q => cases ht
    | inr q =>
      induction q using Quotient.inductionOn
      exact ⟨_,rfl⟩
  obtain ⟨v,rfl⟩ := hv
  let f := (MulAut.conj v⁻¹).toMonoidHom.comp (embedM d.radical)
  have hf : Function.Injective f := (MulAut.conj v⁻¹).injective.comp (embedM_injective d.radical)
  have hm : d.radical.map f = Q d.radical (hVertex d.radical v) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act]
    simp only [beta,act_hVertex,one_mul]
  refine ⟨?_,?_⟩
  · apply map_injective hf
    rw [map_commutator,map_commutator,hm,Subgroup.map_bot]
    exact hc
  · intro x hx
    apply hf
    rw [map_pow,map_one]
    exact hp (f x) (hm ▸ mem_map_of_mem f hx)

/-- The original odd-index witness discharges the field-sized premise in the
proper nonsylow branch; the entire retained fixed factor obeys these bounds. -/
theorem replacement_proper_nonsylow_radical_class_two_and_exponent_four
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ⁅⁅d.radical,d.radical⁆,d.radical⁆ = ⊥ ∧ ∀ x ∈ d.radical, x^4=1 :=
  replacement_field_sized_radical_class_two_and_exponent_four h d g hb
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)



/-- The original radical restriction is exactly q² above the proper replacement.
Both indices are taken before quotienting, with the full two-core retained. -/
theorem replacement_proper_nonsylow_index
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    d.radical.relIndex (R.subgroupOf d.overgroup) = 2^(2*n) := by
  let D := (d.ambient.subgroupOf K).map (componentProjection h)
  let B := (R.subgroupOf K).map (componentProjection h)
  have hDB : D ≤ B := map_mono (by
    intro x hx
    exact (map_subtype_le d.subgroup) hx)
  have hB : Nat.card B = (2^n)^3 := by
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    rcases original_marked_radical_alternatives h d with ⟨u,⟨hu,_⟩ | ⟨hu,_⟩⟩ | hs
    · rw [←Subgroup.card_map_of_injective (K := B)
        (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective,hu,←h.field_card]
      exact SymplecticConjugatePair.card_pointRadical
    · rw [←Subgroup.card_map_of_injective (K := B)
        (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective,hu,←h.field_card]
      exact SymplecticConjugatePair.card_planeRadical
    · exact (hnsyl hs).elim
  have hD : Nat.card D = 2^n := replacement_proper_nonsylow_card h d g hb hnsyl hne
  have hm := (D.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv,hD,hB] at hm
  have hi : D.relIndex B = 2^(2*n) := by
    change 2^n * D.relIndex B = (2^n)^3 at hm
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2^n by positivity)
    calc
      2^n * D.relIndex B = (2^n)^3 := hm
      _ = 2^n * 2^(2*n) := by rw [Nat.mul_comm 2 n,pow_mul]; ring
  obtain ⟨f,hf,hk,hmark,he⟩ := exists_replacement_marked_projection h d g (by omega)
  have hR := replacement_original_radical_map h d g (by omega) f hk hmark
  have hkT : f.ker ≤ d.radical := hk.trans_le (replacement_core_le h d)
  have hTR : d.radical ≤ R.subgroupOf d.overgroup := by
    intro x hx
    exact (map_subtype_le d.subgroup) hx
  have hi' := relIndex_map_map f d.radical (R.subgroupOf d.overgroup)
  rw [sup_of_le_left hkT,sup_of_le_left (hkT.trans hTR),he,hR] at hi'
  exact hi'.symm.trans hi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
