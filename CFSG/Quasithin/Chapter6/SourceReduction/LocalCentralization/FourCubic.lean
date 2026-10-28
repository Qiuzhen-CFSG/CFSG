module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FourThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SylowActors
public import Theory.Representation.BinaryAlternatingSevenControl.CartanNormalizer

/-!
# The original cubic normalizes the four-space Thompson subgroup

The right Hall and escaping cubic form a three-plane in K. The literal
four-space action is onto A₇ with kernel O₂(KT), so that plane injects.
The original left Cartan intersection has odd cyclic image containing
the cubic image; seven-letter cycle lengths make these images equal.
Both Hall product identities therefore make the plane permute with the
full Sylow image. The A₇ Hall-plane theorem normalizes the unique offender,
and recovery through O₂(KT) lifts normalization to the original J(T).

The genuine symmetric-five left row makes the same cubic fail to normalize
J(T), so it is excluded here. The remaining left-row conclusion is precisely
Thompson containment and whole-Borel normalization, with no degree restriction.
The source applications are in the companion CartanLocalComparison module.

Source: Aschbacher–Smith 5.1.13, printed p.637, using B.4.2(7).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The prescribed right Hall subgroup permutes with the original Sylow. -/
theorem CartanPair.right_permutes_sylow
    {T : Sylow 2 G} {L H A B : Subgroup G} (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (hTH : (T : Subgroup G) ≤ H) :
    (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) := by
  let P := normalizer (L : Set G) ⊓ H
  have hTP : (T : Subgroup G) ≤ P := le_inf hTL hTH
  have hc := c.sylow_complement hTL hTH
  apply Set.Subset.antisymm
  · rintro _ ⟨b,hb,t,ht,rfl⟩
    obtain ⟨⟨t',b'⟩,he⟩ := hc.2 ⟨b*t,P.mul_mem (c.right_le hb) (hTP ht)⟩
    exact ⟨t'.val,t'.property,b'.val,b'.property,congrArg P.subtype he⟩
  · rintro _ ⟨t,ht,b,hb,rfl⟩
    obtain ⟨⟨b',t'⟩,he⟩ := hc.symm.2 ⟨t*b,P.mul_mem (hTP ht) (c.right_le hb)⟩
    exact ⟨b'.val,b'.property,t'.val,t'.property,congrArg P.subtype he⟩

omit [Finite G] in
/-- Restriction and an actual quotient map preserve permuting products. -/
theorem map_subgroupOf_permutes {M E P : Subgroup G}
    (hEM : E ≤ M) (hPM : P ≤ M)
    {Q : Type*} [Group Q] (f : M →* Q)
    (he : (E : Set G) * (P : Set G) = (P : Set G) * (E : Set G)) :
    ((E.subgroupOf M).map f : Set Q) * ((P.subgroupOf M).map f : Set Q) =
      ((P.subgroupOf M).map f : Set Q) * ((E.subgroupOf M).map f : Set Q) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_,⟨e,he',rfl⟩,_,⟨p,hp,rfl⟩,rfl⟩
    have hh0 : (e : G) * (p : G) ∈ (P : Set G) * (E : Set G) := he ▸ Set.mul_mem_mul (show (e : G) ∈ E from he') (show (p : G) ∈ P from hp)
    obtain ⟨p',hp',e',he'',hh⟩ := hh0
    refine ⟨f ⟨p',hPM hp'⟩,mem_map_of_mem f hp',f ⟨e',hEM he''⟩,mem_map_of_mem f he'',?_⟩
    exact (f.map_mul _ _).symm.trans ((congrArg f (Subtype.ext hh)).trans (f.map_mul _ _))
  · rintro _ ⟨_,⟨p,hp,rfl⟩,_,⟨e,he',rfl⟩,rfl⟩
    have hh0 : (p : G) * (e : G) ∈ (E : Set G) * (P : Set G) := he.symm ▸ Set.mul_mem_mul (show (p : G) ∈ P from hp) (show (e : G) ∈ E from he')
    obtain ⟨e',he'',p',hp',hh⟩ := hh0
    refine ⟨f ⟨e',hEM he''⟩,mem_map_of_mem f he'',f ⟨p',hPM hp'⟩,mem_map_of_mem f hp',?_⟩
    exact (f.map_mul _ _).symm.trans ((congrArg f (Subtype.ext hh)).trans (f.map_mul _ _))


/-- In the original four-space case, the escaping cubic and right Hall
normalize J(T). The right Hall and the actual two-kernel are essential. -/
theorem LocalA7Configuration.four_cubic_normalizes_thompson
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    B ⊔ D ⊔ (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  obtain ⟨q,hq,hk,hcore⟩ := a.four_action h hc
  have hUT : U ≤ P :=
    (show U ≤ pCore 2 M from le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans
      (pCore_isPGroup.le_sylow_of_normal P)
  have hPmap : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hjmap : (elementaryAbelianMaxJ (P : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hPmap]
  have hj : ¬ elementaryAbelianMaxJ (P : Subgroup M) ≤ q.ker := by
    rw [hk]
    intro hj
    apply a.right_thompson_moves
    rw [←hjmap]
    rintro _ ⟨x,hx,rfl⟩ u hu
    exact congrArg M.subtype (hj hx ⟨u,a.reduced.1 hu⟩ hu)
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = Nat.card (ZMod 2)^Module.finrank (ZMod 2) (Additive U) at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv,hc,Nat.card_zmod] at hh
    exact hh.symm
  obtain ⟨J,hJP,hJ,hJq,_⟩ :=
    ChapterC.RankOne.Alternating.SevenSource.exceptional_thompson_baumann_images U q hq hk hd P hUT hj
  obtain ⟨he,hcard,hle,_⟩ := d.hall_cubic_plane h hH hgen c
  have hEM : B ⊔ D ≤ M := hle.trans (a.contains.trans le_sup_left)
  let E := (B ⊔ D).subgroupOf M
  have hEc : Nat.card E = 9 := (Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv).trans hcard
  have hdis : Disjoint E q.ker :=
    (IsPGroup.of_card (p := 3) (n := 2) hEc).disjoint_of_coprime
      (hcore.symm ▸ pCore_isPGroup) (by decide)
  have hqi : Function.Injective (q.subgroupMap E) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp (hdis.le_bot ⟨x.property,congrArg Subtype.val (show q.subgroupMap E x = 1 from hx)⟩)
  have hEq : Nat.card (E.map q) = 9 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap E)
      ⟨hqi,q.subgroupMap_surjective E⟩).toEquiv).symm.trans hEc
  have hDM : D ≤ M := le_sup_right.trans hEM
  have hDqcard : Nat.card ((D.subgroupOf M).map q) = 3 := by
    have hi : Function.Injective (q.subgroupMap (D.subgroupOf M)) := by
      intro x y hxy
      have hxy' : q x.val = q y.val :=
        congrArg (fun z : (D.subgroupOf M).map q => (z : alternatingGroup (Fin 7))) hxy
      have hh : (⟨x.val,(show D ≤ B ⊔ D from le_sup_right) x.property⟩ : E) =
          ⟨y.val,(show D ≤ B ⊔ D from le_sup_right) y.property⟩ := hqi (Subtype.ext hxy')
      exact Subtype.ext (congrArg (fun z : E => (z : M)) hh)
    exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap (D.subgroupOf M))
      ⟨hi,q.subgroupMap_surjective _⟩).toEquiv).symm.trans
        ((Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv).trans d.cubic_card)
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let j : A.subgroupOf M →* A := {
    toFun x := ⟨x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hji : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun a : A => (a : G)) hh))
  let : IsCyclic (A.subgroupOf M) := isCyclic_of_injective j hji
  let : IsCyclic ((A.subgroupOf M).map q) :=
    isCyclic_of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
  have hAo : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hAqo : Odd (Nat.card ((A.subgroupOf M).map q)) :=
    (hAo.of_dvd_nat (card_dvd_of_injective j hji)).of_dvd_nat (card_map_dvd _ q)
  have hDAq : (D.subgroupOf M).map q ≤ (A.subgroupOf M).map q :=
    map_mono (comap_mono (d.cubic_le.trans inf_le_left))
  have hAqcard := Representation.BinaryAlternatingSevenControl.Cartan.odd_cyclic_card_three
    ((A.subgroupOf M).map q) hAqo (hDqcard ▸ card_dvd_of_le hDAq)
  have hDAqe : (D.subgroupOf M).map q = (A.subgroupOf M).map q :=
    eq_of_le_of_card_ge hDAq (by rw [hDqcard,hAqcard])
  have hDperm := c.image_intersection_permutes_sylow h.sylow_normalizes
    (show (T : Subgroup G) ≤ M from le_sup_right) q
  rw [←hDAqe] at hDperm
  change ((D.subgroupOf M).map q : Set (alternatingGroup (Fin 7))) * ((P : Subgroup M).map q : Set _) =
    ((P : Subgroup M).map q : Set _) * ((D.subgroupOf M).map q : Set _) at hDperm
  have hBM : B ≤ M := le_sup_left.trans hEM
  have hBperm := map_subgroupOf_permutes hBM (show (T : Subgroup G) ≤ M from le_sup_right) q
    (c.right_permutes_sylow h.sylow_normalizes hH.1.1.2)
  change ((B.subgroupOf M).map q : Set (alternatingGroup (Fin 7))) * ((P : Subgroup M).map q : Set _) =
    ((P : Subgroup M).map q : Set _) * ((B.subgroupOf M).map q : Set _) at hBperm
  have hBD : (B.subgroupOf M).map q ≤ normalizer ((D.subgroupOf M).map q : Set _) := by
    have hb : B ≤ normalizer (D : Set G) :=
      c.right_normalizes_left.trans (normalizer_le_normalizer_of_le_cyclic D A (d.cubic_le.trans inf_le_left))
    have hb' : B.subgroupOf M ≤ normalizer (D.subgroupOf M : Set M) := by
      intro b hbmem
      exact mem_normalizer_iff.mpr (fun x => mem_normalizer_iff.mp (hb hbmem) x.val)
    exact (map_mono hb').trans ((D.subgroupOf M).le_normalizer_map q)
  have hperm : (E.map q : Set (alternatingGroup (Fin 7))) * ((P : Subgroup M).map q : Set _) =
      ((P : Subgroup M).map q : Set _) * (E.map q : Set _) := by
    have heq : E.map q = (B.subgroupOf M).map q ⊔ (D.subgroupOf M).map q := by
      rw [←Subgroup.map_sup,←subgroupOf_sup hBM hDM]
    rw [heq,coe_mul_of_left_le_normalizer_right _ _ hBD]
    rw [mul_assoc,hDperm,←mul_assoc,hBperm,mul_assoc]
  have hn := Representation.BinaryAlternatingSevenControl.Cartan.permuting_plane_normalizes_best
    (NormalElementaryQuotient.representation U q hq hk)
    (NormalElementaryQuotient.representation_injective U q hq hk) hd
    (P.mapSurjective (f := q) hq) J (E.map q) hJP hJ hEq hperm
  have hN : normalizer (elementaryAbelianMaxJ (P : Subgroup M) : Set M) =
      (normalizer (J : Set (alternatingGroup (Fin 7)))).comap q := by
    rw [normalizer_maxJ_eq_comap_of_ker_le (P : Subgroup M) q
      (hcore.symm ▸ pCore_isPGroup.le_sylow_of_normal P),hJq]
  have hEN : E ⊔ (P : Subgroup M) ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup M) : Set M) := by
    rw [hN]
    apply map_le_iff_le_comap.mp
    rw [Subgroup.map_sup]
    exact hn
  have hfinal := (map_mono (f := M.subtype) hEN).trans
    ((elementaryAbelianMaxJ (P : Subgroup M)).le_normalizer_map M.subtype)
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hEM,hPmap,hjmap] at hfinal

/-- The symmetric-five left row is incompatible with the original right
four-space. Thus its natural-left Thompson containment and Borel control hold. -/
theorem LocalA7Configuration.four_left_thompson_natural
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    localBorel T L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  rcases a.left_thompson_cubic_dichotomy h c d with hn | ⟨_,_,_,hnot⟩
  · exact hn
  · exact (hnot ((le_sup_right.trans le_sup_left).trans
      (a.four_cubic_normalizes_thompson h hH hgen c d hc))).elim

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
