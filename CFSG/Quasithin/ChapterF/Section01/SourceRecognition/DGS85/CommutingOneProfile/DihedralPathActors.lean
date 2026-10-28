module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.DihedralCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicPathActor
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Cubic actors in the dihedral beta candidate

An automorphism of D10 whose cube is one is trivial. This is checked on
its rotation and reflection generators, with a certificate over only
100 generator-image pairs. A cubic in the full vertex stabilizer therefore
normalizes every edge Sylow and fixes every neighbor. The full kernel
is kept distinct from its two-core.

With a genuine full A5 alpha quotient, the alpha-turn cubic reaches the
remote alpha vertex. Its order survives that vertex's two-core quotient,
where it cannot normalize the injective image of an order-two intersection
layer. The earlier local data and actual quotient markings remain explicit.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6), printed pp.172--174, Cartan argument on p.173; (11.7), p.175.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
private def dihedralEval (x y : DihedralGroup 5) : DihedralGroup 5 → DihedralGroup 5
  | .r i => x ^ i.val
  | .sr i => y * x ^ i.val

private theorem dihedral_hom_eval (e : MulAut (DihedralGroup 5)) (z : DihedralGroup 5) :
    e z = dihedralEval (e (.r 1)) (e (.sr 0)) z := by
  cases z with
  | r i =>
    change e (.r i) = e (.r 1) ^ i.val
    rw [←map_pow,DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
  | sr i =>
    change e (.sr i) = e (.sr 0) * e (.r 1) ^ i.val
    rw [←map_pow,←map_mul,DihedralGroup.r_one_pow,ZMod.natCast_zmod_val]
    simp

private theorem dihedral_cubic_aut (e : MulAut (DihedralGroup 5)) (he : e ^ 3 = 1) : e = 1 := by
  have cert : ∀ x y : DihedralGroup 5,
      x ^ 5 = 1 → y ^ 2 = 1 →
      dihedralEval x y (dihedralEval x y x) = .r 1 →
      dihedralEval x y (dihedralEval x y y) = .sr 0 →
      x = .r 1 ∧ y = .sr 0 := by decide +kernel
  have hc (z : DihedralGroup 5) : e (e (e z)) = z := by
    have hh := DFunLike.congr_fun he z
    simpa only [pow_succ,pow_zero,mul_one,MulAut.mul_apply,MulAut.one_apply] using hh
  have hr := hc (.r 1)
  have hs := hc (.sr 0)
  rw [dihedral_hom_eval e (e (e (.r 1))),dihedral_hom_eval e (e (.r 1))] at hr
  rw [dihedral_hom_eval e (e (e (.sr 0))),dihedral_hom_eval e (e (.sr 0))] at hs
  obtain ⟨hr,hs⟩ := cert (e (.r 1)) (e (.sr 0))
    (by rw [←map_pow,DihedralGroup.r_one_pow_n,map_one]) (by rw [←map_pow]; simp [pow_two]) hr hs
  apply MulEquiv.ext
  intro z
  rw [dihedral_hom_eval,hr,hs]
  cases z with
  | r i => simp [dihedralEval]
  | sr i => simp [dihedralEval]

open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A cubic fixing a dihedral local vertex fixes its whole star. -/
theorem source_dihedral_cubic_fixes_neighbors (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5)
    (t : G) (htv : t ∈ stabilizer (family P) v) (ht3 : t ^ 3 = 1)
    {w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    t ∈ stabilizer (family P) w := by
  let := finite_endpoints h
  let L := d.localGroup v
  have htN : t ∈ normalizer (L : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (d.conjugate t v).symm.trans (congrArg d.localGroup htv)
  let tN : normalizer (L : Set G) := ⟨t,htN⟩
  let f := (quotientAut (pCore 2 L)).comp L.normalizerMonoidHom
  let α := (MulAut.congr e).toMonoidHom.comp f
  have hp : tN ^ 3 = 1 := Subtype.ext ht3
  have he : f tN = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact dihedral_cubic_aut (α tN) (by rw [←map_pow,hp,map_one])
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  let q := QuotientGroup.mk' (pCore 2 L)
  have hq (x : L) : q (L.normalizerMonoidHom tN x) = q x := by
    have hh := DFunLike.congr_fun he (q x)
    simpa only [f,MonoidHom.comp_apply,q,quotientAut_apply_mk,MulAut.one_apply] using hh
  have hNR : t ∈ normalizer ((R : Subgroup L).map L.subtype : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hmap : (R : Subgroup L).map (L.normalizerMonoidHom tN).toMonoidHom = R := by
      have hr : (R : Subgroup L) = ((R : Subgroup L).map q).comap q := by
        rw [comap_map_eq,show q.ker = pCore 2 L from QuotientGroup.ker_mk' _,
          sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal R)]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        rw [hr]
        change q (L.normalizerMonoidHom tN y) ∈ (R : Subgroup L).map q
        rw [hq]
        exact mem_map_of_mem q hy
      · intro hx
        refine ⟨(L.normalizerMonoidHom tN).symm x,?_,(L.normalizerMonoidHom tN).apply_symm_apply x⟩
        rw [hr]
        change q ((L.normalizerMonoidHom tN).symm x) ∈ (R : Subgroup L).map q
        rw [←hq ((L.normalizerMonoidHom tN).symm x),(L.normalizerMonoidHom tN).apply_symm_apply]
        exact mem_map_of_mem q hx
    have hm := congrArg (map L.subtype) hmap
    rw [map_map] at hm
    change (R : Subgroup L).map ((MulAut.conj t).toMonoidHom.comp L.subtype) = _ at hm
    rwa [←map_map] at hm
  exact ((source_edge_local_normalizer h d hvw (.dihedral ⟨e⟩) R hR).1.le ⟨htv,hNR⟩).2

private abbrev A5 := alternatingGroup (Fin 5)
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


open scoped MatrixGroups
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- With a full A₅ alpha marking, the dihedral beta branch has no
order-two intersection layer. -/
theorem source_dihedral_a5_layer_card_ne_two (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5)
    (ef : (stabilizer (family P) a ⧸ pCore 2 (stabilizer (family P) a)) ≃* alternatingGroup (Fin 5))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b) :
    Nat.card (neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b) : Subgroup G) ≠ 2 := by
  let := finite_endpoints h
  let J := neighborCoreIntersection (family P) b ⊓ Q (family P) (g • b)
  let H := stabilizer (family P) (g • c)
  have hbc' : (graph (family P)).Adj (g • b) (g • c) :=
    (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hbc
  have hJH : J ≤ H := inf_le_right.trans ((source_Z_Q_U h (g • b)).2.trans
    ((ballKernel_one_le_edge _ hbc').trans inf_le_right))
  have hab := source_critical_one_adjacent hc hb
  have hab' : (graph (family P)).Adj a (g • b) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hab
    change (graph (family P)).Adj (g • a) (g • b) at hh
    rwa [show g • a = a from hga] at hh
  obtain ⟨t,hta,htb,htb',ht3⟩ := source_a5_turn_cubic h hB hS hab hab' ef
  let eL := (MulEquiv.subgroupCongr (d.conjugate g b)).trans
    ((d.localGroup b).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  let eb' := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans eb
  have htd : t ∈ H := source_dihedral_cubic_fixes_neighbors h hB d (g • b) eb' t htb'
    (ht3 ▸ pow_orderOf_eq_one t) hbc'
  have hnJ : t ∈ normalizer (J : Set G) := inf_normalizer_le_normalizer_inf
    ⟨neighborCoreIntersection_normalized (family P) b htb,
      ((stabilizer (family P) (g • b)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) (g • b))))) htb'⟩
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .dihedral ⟨eb⟩
  obtain ⟨hprod,hcore⟩ := source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea
  have hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
    rw [sup_comm]
    exact alpha_supplement_of_pair_generation _ _ _ _ _ hprod hcore
      ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hsep := source_rankOne_neighbor_intersection_separated h hB d hc hb hbc hac
    Ma Mb hsupp g hga hgb
  obtain ⟨r,_,hra⟩ := locally_transitive (family P) hab'.symm hbc'
  have hs : H = (stabilizer (family P) a).map (MulAut.conj r).toMonoidHom := by
    change stabilizer (family P) (g • c) = _
    rw [←hra,stabilizer_translate]
  let es : H ≃* stabilizer (family P) a := (MulEquiv.subgroupCongr hs).trans
    ((stabilizer (family P) a).equivMapOfInjective
      (MulAut.conj r).toMonoidHom (MulAut.conj r).injective).symm
  let ed := (QuotientGroup.congr _ _ es (pCore_map_iso 2 es)).trans ef
  let q : H →* alternatingGroup (Fin 5) := ed.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let f := q.comp (inclusion hJH)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxQ : (x : G) ∈ Q (family P) (g • c) := by
      have he : ed ((QuotientGroup.mk' (pCore 2 H)) (inclusion hJH x)) = 1 := hx
      rw [map_eq_one_iff ed ed.injective] at he
      exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp he)
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hsep ▸ (show (x : G) ∈ neighborCoreIntersection (family P) b ⊓
      Q (family P) (g • c) from ⟨x.property.1,hxQ⟩))
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
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
