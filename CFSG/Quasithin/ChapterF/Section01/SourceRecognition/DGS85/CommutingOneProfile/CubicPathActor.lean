module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreEquality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearMarking
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Cubic path actors and the remaining mixed center orders

The two Sylow normalizers at an alpha turn map to point stabilizers in
A₅. A cubic in their intersection lifts to an order-three path actor.
At a cubic beta vertex, such an actor fixes the entire star; this uses
the full permutation kernel and does not identify it with the two-core.
The remote A₅ quotient preserves its order and embeds the intersection
layer. An order-two subgroup cannot be normalized by a cubic in A₅.

Together with the previously proved escape and index-two statements,
this reduces the beta-center order to two or eight. The exclusion of
eight and the literal original mixed-pair application are separate steps.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6), printed pp.172--174, especially the Cartan action on p.173.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
private abbrev A5 := alternatingGroup (Fin 5)
private theorem a5_two_points (i j : Fin 5) :
    ∃ x : A5, x.val i = i ∧ x.val j = j ∧ x ^ 3 = 1 ∧ x ≠ 1 := by
  revert i j
  decide +kernel

private theorem normalizer_pair_three {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* A5) (T R : Sylow 2 H) :
    ∃ x : H, x ∈ normalizer (T : Set H) ∧ x ∈ normalizer (R : Set H) ∧ orderOf x = 3 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let T' := T.mapSurjective hq
  let R' := R.mapSurjective hq
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer T'
  obtain ⟨j,hj⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R'
  obtain ⟨x,hxi,hxj,hxp,hxn⟩ := a5_two_points i j
  have hx3 : orderOf x = 3 := orderOf_eq_prime hxp hxn
  let D := normalizer (T : Set H) ⊓ normalizer (R : Set H)
  let E := normalizer (T' : Set A5) ⊓ normalizer (R' : Set A5)
  have ht : (normalizer (T' : Set A5)).comap q = normalizer (T : Set H) := by
    change (normalizer ((T : Subgroup H).map q : Set A5)).comap q = _
    rw [←T.normalizer_map_surjective q hq,comap_map_eq]
    exact sup_eq_left.mpr (hk ▸ (pCore_isPGroup.le_sylow_of_normal T).trans (T : Subgroup H).le_normalizer)
  have hr : (normalizer (R' : Set A5)).comap q = normalizer (R : Set H) := by
    change (normalizer ((R : Subgroup H).map q : Set A5)).comap q = _
    rw [←R.normalizer_map_surjective q hq,comap_map_eq]
    exact sup_eq_left.mpr (hk ▸ (pCore_isPGroup.le_sylow_of_normal R).trans (R : Subgroup H).le_normalizer)
  have hDE : E.comap q = D := by rw [comap_inf,ht,hr]
  have hmap : D.map q = E := by rw [←hDE,map_comap_eq_self_of_surjective hq]
  have hxE : x ∈ E := ⟨hi ▸ hxi,hj ▸ hxj⟩
  have hdiv : 3 ∣ Nat.card D := by
    have hh : 3 ∣ Nat.card E := by
      have hh := orderOf_dvd_natCard (⟨x,hxE⟩ : E)
      rwa [←Subgroup.orderOf_coe,hx3] at hh
    rw [←hmap] at hh
    exact hh.trans (card_map_dvd _ q)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 hdiv
  exact ⟨z,z.property.1,z.property.2,(Subgroup.orderOf_coe z).trans hz⟩

private theorem a5_cubic_normalized_ne_two (A : Subgroup A5)
    (t : A5) (ht : orderOf t = 3) (hn : t ∈ normalizer (A : Set A5)) : Nat.card A ≠ 2 := by
  intro hc
  obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  have htc : t ∈ centralizer (A : Set A5) := by
    intro x hx
    by_cases hx1 : x = 1
    · simp only [hx1,mul_one,one_mul]
    · have hm := (mem_normalizer_iff.mp hn x).mp hx
      have hne : t * x * t⁻¹ ≠ 1 := by
        intro he
        apply hx1
        exact (MulAut.conj t).injective (he.trans (map_one (MulAut.conj t)).symm)
      have he : t * x * t⁻¹ = x := congrArg Subtype.val
        ((hz ⟨_,hm⟩ (fun he => hne (congrArg Subtype.val he))).trans
          (hz ⟨x,hx⟩ (fun he => hx1 (congrArg Subtype.val he))).symm)
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hle : A ≤ centralizer (zpowers t : Set A5) :=
    le_centralizer_iff.mp (zpowers_le.mpr htc)
  have hcard := alternatingGroup.FiveLocalGeometry.cubic_centralizer_card
    (MulEquiv.refl A5) (zpowers t) ((Nat.card_zpowers t).trans ht)
  have hd := card_dvd_of_le hle
  rw [hc,hcard] at hd
  norm_num at hd

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- An order-three actor fixes both edges of every alpha turn. -/
theorem source_a5_turn_cubic (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b b' : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hab' : (graph (family P)).Adj a b')
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5)) :
    ∃ t : G, t ∈ stabilizer (family P) a ∧ t ∈ stabilizer (family P) b ∧
      t ∈ stabilizer (family P) b' ∧ orderOf t = 3 := by
  let := finite_endpoints h
  let H := stabilizer (family P) a
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  obtain ⟨R,hR⟩ := source_edge_vertex_sylow h hS hab'
  have hTeq := sylow_image_eq_edge_core H _ inf_le_left
    (source_edge_core_sylow h hB hab) T hT
  have hReq := sylow_image_eq_edge_core H _ inf_le_left
    (source_edge_core_sylow h hB hab') R hR
  obtain ⟨t,htT,htR,ht3⟩ := normalizer_pair_three e T R
  have htN := (T : Subgroup H).le_normalizer_map H.subtype (mem_map_of_mem H.subtype htT)
  have hrN := (R : Subgroup H).le_normalizer_map H.subtype (mem_map_of_mem H.subtype htR)
  rw [hTeq] at htN
  rw [hReq] at hrN
  have htE := (source_edge_core_normalizer h hB hab).le ⟨t.property,htN⟩
  have hrE := (source_edge_core_normalizer h hB hab').le ⟨t.property,hrN⟩
  exact ⟨t,t.property,htE.2,hrE.2,(Subgroup.orderOf_coe t).trans ht3⟩

private theorem cubic_perm_fixed {X : Type*} [Finite X] (hX : Nat.card X = 3)
    (f : Equiv.Perm X) (hf : f ^ 3 = 1) (x : X) (hx : f x = x) : f = 1 := by
  let e := Finite.equivFinOfCardEq hX
  let c := Equiv.permCongrHom e
  have cert : ∀ p : Equiv.Perm (Fin 3), p ^ 3 = 1 → ∀ i : Fin 3, p i = i → p = 1 := by
    decide +kernel
  apply c.injective
  rw [map_one]
  apply cert (c f) (by rw [←map_pow,hf,map_one]) (e x)
  change e (f (e.symm (e x))) = e x
  rw [e.symm_apply_apply,hx]

/-- A cubic element fixing one edge at a cubic vertex fixes its whole star.
The conclusion concerns the full local kernel, not its two-core. -/
theorem source_cubic_actor_in_kernel (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (t : G) (hta : t ∈ stabilizer (family P) a) (htb : t ∈ stabilizer (family P) b)
    (ht3 : orderOf t = 3) : t ∈ U (family P) b := by
  let := finite_endpoints h
  let := Nat.finite_of_card_ne_zero (show Nat.card ((graph (family P)).neighborSet b) ≠ 0 by omega)
  let f := localAction (family P) b
  let z : stabilizer (family P) b := ⟨t,htb⟩
  have hp : z ^ 3 = 1 := Subtype.ext (ht3 ▸ pow_orderOf_eq_one t)
  have hf : f z = 1 := cubic_perm_fixed hcard (f z) (by rw [←map_pow,hp,map_one])
    ⟨a,hab.symm⟩ (Subtype.ext hta)
  have hm : z ∈ f.ker := hf
  rw [←U_eq_localAction_kernel] at hm
  exact hm

/-- The intersection layer on an alpha turn cannot have order two. The cubic
path actor is preserved in the remote A₅ quotient. -/
theorem source_cubic_a5_layer_card_ne_two (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b b' d : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (hab' : (graph (family P)).Adj a b') (hbb' : b ≠ b')
    (hb'd : (graph (family P)).Adj b' d) (had : a ≠ d) :
    Nat.card (neighborCoreIntersection (family P) b ⊓ Q (family P) b' : Subgroup G) ≠ 2 := by
  let := finite_endpoints h
  let J := neighborCoreIntersection (family P) b ⊓ Q (family P) b'
  let H := stabilizer (family P) d
  have hJH : J ≤ H := inf_le_right.trans ((source_Z_Q_U h b').2.trans
    ((ballKernel_one_le_edge _ hb'd).trans inf_le_right))
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hga,hgb⟩ := locally_transitive (family P) hab hab'
  have hcard' : Nat.card ((graph (family P)).neighborSet b') = 3 := by
    rw [←hgb]
    exact (Nat.card_congr ((Subgroup.CosetGeometry.translationGraphIso (family P) g).mapNeighborSet b)).symm.trans hcard
  obtain ⟨t,hta,htb,htb',ht3⟩ := source_a5_turn_cubic h hB hS hab hab' e
  have htU := source_cubic_actor_in_kernel h hab' hcard' t hta htb' ht3
  have htd : t ∈ H := ((ballKernel_one_le_edge _ hb'd).trans inf_le_right) htU
  have hnJ : t ∈ normalizer (J : Set G) := inf_normalizer_le_normalizer_inf
    ⟨neighborCoreIntersection_normalized (family P) b htb,
      ((stabilizer (family P) b').le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) b')))) htb'⟩
  have hsep := source_cubic_a5_neighbor_intersection_separated_at_turn h hB hS hc hb hcard e
    hab' hbb' hb'd had
  obtain ⟨r,_,hra⟩ := locally_transitive (family P) hab'.symm hb'd
  have hs : H = (stabilizer (family P) a).map (MulAut.conj r).toMonoidHom := by
    change stabilizer (family P) d = _
    rw [←hra,stabilizer_translate]
  let es : H ≃* stabilizer (family P) a := (MulEquiv.subgroupCongr hs).trans
    ((stabilizer (family P) a).equivMapOfInjective
      (MulAut.conj r).toMonoidHom (MulAut.conj r).injective).symm
  let ed := (QuotientGroup.congr _ _ es (pCore_map_iso 2 es)).trans e
  let q : H →* alternatingGroup (Fin 5) := ed.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let f := q.comp (inclusion hJH)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxQ : (x : G) ∈ Q (family P) d := by
      have he : ed ((QuotientGroup.mk' (pCore 2 H)) (inclusion hJH x)) = 1 := hx
      rw [map_eq_one_iff ed ed.injective] at he
      exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp he)
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hsep ▸ (show (x : G) ∈ neighborCoreIntersection (family P) b ⊓
      Q (family P) d from ⟨x.property.1,hxQ⟩))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ ed.injective,QuotientGroup.ker_mk']
  have htq : orderOf (q ⟨t,htd⟩) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker (hk ▸ pCore_isPGroup) ⟨t,htd⟩
      (by rw [←Subgroup.orderOf_coe,ht3]; decide)).trans
        ((Subgroup.orderOf_coe (⟨t,htd⟩ : H)).symm.trans ht3)
  let A := (J.subgroupOf H).map q
  have hqN : q ⟨t,htd⟩ ∈ normalizer (A : Set (alternatingGroup (Fin 5))) := by
    apply (J.subgroupOf H).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq hJH]
    exact hnJ
  have hA : Nat.card A = Nat.card J := by
    have he : A = f.range := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨⟨y,hy⟩,rfl⟩
      · rintro ⟨y,rfl⟩
        exact ⟨inclusion hJH y,y.property,rfl⟩
    rw [he]
    exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv |>.symm
  rw [←hA]
  exact a5_cubic_normalized_ne_two A _ htq hqN

/-- Cubic escape and the cubic path actor reduce the beta-center order to
2 or 8. No center-layer vanishing hypothesis is used. -/
theorem source_cubic_a5_center_card_two_or_eight (h : LocallyRankOneTriple P B)
    (hB : ∃ R : Sylow 2 B, (R : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (e : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃*
      alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (Z (family P) b) = 2 ∨ Nat.card (Z (family P) b) = 8 := by
  let := finite_endpoints h
  obtain ⟨t,hta,htb,hesc⟩ := source_cubic_a5_center_escape h hB hS hc hb hcomm hbc hac hcard e
    g hga hgb
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (t • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) t).map_adj_iff.mpr hab
    change (graph (family P)).Adj (t • a) (t • b) at hh
    rwa [show t • a = a from hta] at hh
  have hbc' : (graph (family P)).Adj (t • b) (t • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) t).map_adj_iff.mpr hbc
  have hac' : a ≠ t • c := by
    intro he
    apply hac
    have hh := congrArg (fun v => t⁻¹ • v) he
    rwa [←show t • a = a from hta,inv_smul_smul,inv_smul_smul] at hh
  have hcard' : Nat.card ((graph (family P)).neighborSet (t • b)) = 3 :=
    (Nat.card_congr ((Subgroup.CosetGeometry.translationGraphIso (family P) t).mapNeighborSet b)).symm.trans hcard
  have hZi := source_commuting_one_center_le_neighbor_intersection h hB hS hc hb hcomm
  have hp : IsPGroup 2 (Z (family P) b) := (isPGroup_pCoreIn 2 _).to_le
    (hZi.trans (neighborCoreIntersection_le _ hab))
  have hZG : Z (family P) b ≤ stabilizer (family P) (t • b) :=
    (hZi.trans (neighborCoreIntersection_le _ hab)).trans ((source_Z_Q_U h a).2.trans
      ((ballKernel_one_le_edge _ hab').trans inf_le_right))
  have hSyl := source_kernel_sylow h hB hS (t • b)
  have hindex := source_cubic_two_subgroup_index h (t • b) (Z (family P) b) hp hZG
    (fun hh => hesc (CommutingTrivial.two_subgroup_le_Q (family P) (t • b) hSyl hp hh)) hcard' hSyl
  have hlayer := (source_cubic_a5_intersection_layer h hB hS hc hb hcard e hab'
    (Ne.symm htb) hbc' hac').2
  have hnot := source_cubic_a5_layer_card_ne_two h hB hS hc hb hcard e hab'
    (Ne.symm htb) hbc' hac'
  rw [source_cubic_a5_neighbor_intersection_eq_center h hB hS hc hb hcomm hbc hac hcard e
    g hga hgb] at hlayer hnot
  let J := Z (family P) b ⊓ Q (family P) (t • b)
  let : Finite J := Finite.of_injective
    (inclusion (inf_le_right.trans (Q_le_stabilizer _ (t • b)))) (inclusion_injective _)
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) J (Z (family P) b) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex] at hcount
  obtain ⟨n,hn⟩ := (hp.to_le (show J ≤ Z (family P) b from inf_le_left)).exists_card_eq
  have hnle : n ≤ 2 := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp
    (hn ▸ hlayer : 2^n ≤ 2^2)
  have hJ : Nat.card J = 1 ∨ Nat.card J = 4 := by
    have hnot' : Nat.card J ≠ 2 := hnot
    interval_cases n
    · exact Or.inl (by simpa using hn)
    · exact (hnot' (by simpa using hn)).elim
    · exact Or.inr (by simpa using hn)
  rcases hJ with hJ | hJ
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
