module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPairedPrime
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.JankoLocal
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.OddNormalizer
public import Theory.GroupTheory.PGroup.IndexTwoElementaryConjugate

/-!
# The actual paired J₁ quotient and its odd Cartan action

In the remaining nonnormal containing row, the index-two normalizer gives
an element of the original Sylow interchanging the two containing factors.
Both survive in Y/O₂(Y) as actual J₁ components. They commute, intersect
trivially, and their multiplication map identifies the image of the entire
containing orbit with their direct product. No involutory lift is assumed.

Restrict the original solvable mixed join of A∩Y, T and B to the selected
component normalizer. Since every J₁ automorphism is inner, conjugation
maps this normalizer onto Aut(J₁), and the original Sylow intersection maps
to a full Sylow. The certified solvable-overgroup criterion makes the mixed
action normalize this Sylow. Faithfulness of odd actors on its elementary
eight bounds their order by 21. The left image is cyclic, and the original
right Hall plane has image of order dividing three.

The source constructor adds these proved facts to the original seed
reduction, retaining all earlier exclusions and both prescribed Hall
conditions. The independent cubic actions and interchange must still be
coupled to exclude the seven-part and lift normalization of the whole
original residual. This module does not exclude the paired J₁ row.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--637, particularly the
paired J₁ paragraph on p.636 (`refs/quasithin.pdf`); GLS3 Table 5.3f.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original mixed action on a paired J₁ component, through its literal
image in Y/O₂(Y). The Sylow is the image of the intersection with the
component normalizer. -/
@[expose] def PairedJankoAction (T : Sylow 2 G) (A B Y : Subgroup G) (C : Subgroup Y) : Prop :=
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let N := normalizer (Cbar : Set (Y ⧸ pCore 2 Y))
  let D := (A.subgroupOf Y).map q
  let E := (B.subgroupOf Y).map q
  let P := ((T : Subgroup G).subgroupOf Y).map q
  let J := (D ⊔ P) ⊔ E
  let f := Cbar.normalizerMonoidHom
  D ⊔ E ≤ N ∧
    ∃ Q : Sylow 2 (MulAut Cbar),
      (Q : Subgroup (MulAut Cbar)) = (P.subgroupOf N).map f ∧
      (J.subgroupOf N).map f ≤ normalizer (Q : Set (MulAut Cbar)) ∧
      Nat.card (((D ⊔ E).subgroupOf N).map f) ∣ 21 ∧
      IsCyclic ((D.subgroupOf N).map f) ∧
      Nat.card ((E.subgroupOf N).map f) ∣ 3

/-- Both literal quotient factors of the original containing orbit, with
the full Sylow exchanger and their multiplication map. -/
@[expose] def PairedJankoPlacement (T : Sylow 2 G) (Y : Subgroup G) (C : Subgroup Y) : Prop :=
    ∃ t : Y, (t : G) ∈ (T : Subgroup G) ∧
      let q := QuotientGroup.mk' (pCore 2 Y)
      let R := C.map q
      IsComponent (Y ⧸ pCore 2 Y) R ∧
      Nonempty (R ≃* Janko1.Model) ∧
      Nonempty (R.conjBy (q t) ≃* Janko1.Model) ∧
      Disjoint R (R.conjBy (q t)) ∧ ⁅R,R.conjBy (q t)⁆ = ⊥ ∧
      q t ∉ normalizer (R : Set (Y ⧸ pCore 2 Y)) ∧
      (R.conjBy (q t)).conjBy (q t) = R ∧
      ∃ e : R × R.conjBy (q t) ≃*
          (componentOrbit C ((T : Subgroup G).subgroupOf Y)).map q,
        ∀ x y, (e (x,y) : Y ⧸ pCore 2 Y) = (x : Y ⧸ pCore 2 Y) * y

namespace LocalSieve

/-- The nonnormal J₁ container has two genuine commuting quotient factors,
with the original Sylow mover and the original multiplication map. -/
theorem nonnormal_janko_quotient_pair
    {T : Sylow 2 G} {Y : Subgroup G} (hTY : (T : Subgroup G) ≤ Y)
    (C : Subgroup Y) (hC : C.IsCComponent)
    (hi : (normalizer (C : Set Y)).index = 2)
    (a : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    PairedJankoPlacement T Y C := by
  let S := T.subtype hTY
  have hn : ¬ (S : Subgroup Y) ≤ normalizer (C : Set Y) := by
    intro hle
    have hd := index_dvd_of_le hle
    rw [hi] at hd
    exact S.not_dvd_index hd
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  have hm : C.conjBy t ≠ C := fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he)
  let : (C ⊔ C.conjBy t).Normal := sup_conjugate_normal_of_normalizer_index_two C hi t htn
  let : IsSimpleGroup (C ⧸ pCore 2 C) := a.isSimpleGroup
  have hd : 2 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr a.toEquiv,Janko1.card_model]
    decide
  obtain ⟨hc,_,_,_,hec,_,_,hdis,hcomm,_,hout,e,he⟩ :=
    simpleCore_pair_quotient_structure C hC t hm.symm hd
  let q := QuotientGroup.mk' (pCore 2 Y)
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let R := C.map q
  let eR := (cComponentTwoCoreQuotientEquiv hC).symm.trans a
  let ec := R.equivMapOfInjective (MulAut.conj (q t)).toMonoidHom (MulAut.conj (q t)).injective
  have horbit : componentOrbit C ((T : Subgroup G).subgroupOf Y) = C ⊔ C.conjBy t := by
    apply le_antisymm
    · apply iSup_le
      intro x
      rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm (x : Y) with he | he
      · exact he.le.trans le_sup_left
      · exact he.le.trans le_sup_right
    · exact sup_le (le_componentOrbit _ _)
        (le_iSup (fun x : (T : Subgroup G).subgroupOf Y => C.conjBy (x : Y)) ⟨t,ht⟩)
  have hp : (componentOrbit C ((T : Subgroup G).subgroupOf Y)).map q = R ⊔ R.conjBy (q t) := by
    rw [horbit,Subgroup.map_sup,hec]
  have hsq : (R.conjBy (q t)).conjBy (q t) = R := by
    have ht2 := mul_self_mem_of_index_two hi t
    have hn := mem_normalizer_iff_map_conj_eq.mp ht2
    have he : (R.conjBy (q t)).conjBy (q t) = R.conjBy (q (t*t)) := by
      change (R.map (MulAut.conj (q t)).toMonoidHom).map (MulAut.conj (q t)).toMonoidHom = _
      rw [map_map,map_mul]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev]
      group
    rw [he]
    have hq := congrArg (map q) hn
    change (C.map (MulAut.conj (t*t)).toMonoidHom).map q = C.map q at hq
    change (C.map q).map (MulAut.conj (q (t*t))).toMonoidHom = C.map q
    have hf : q.comp (MulAut.conj (t*t)).toMonoidHom =
        (MulAut.conj (q (t*t))).toMonoidHom.comp q := by
      ext x
      simp [MulAut.conj_apply]
    rw [map_map,hf,←map_map] at hq
    exact hq
  refine ⟨t,ht,hc,⟨eR⟩,⟨ec.symm.trans eR⟩,hdis,hcomm,hout,hsq,
    e.trans (MulEquiv.subgroupCongr hp.symm),?_⟩
  exact he

private def jankoInnerEquiv : Janko1.Model ≃* MulAut Janko1.Model := by
  have hc : center Janko1.Model = ⊥ :=
    (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp he))
  exact MulEquiv.ofBijective _ ⟨conj_injective_of_center_eq_bot hc,Janko1.OuterCertificate.aut_inner⟩

omit [Finite G] in
private theorem odd_le_index_two (E N : Subgroup G)
    (ho : Odd (Nat.card E)) (hi : N.index = 2) : E ≤ N := by
  let : N.Normal := N.normal_of_index_eq_two hi
  rw [←relIndex_eq_one]
  apply Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr ho)
  · simpa only [hi] using N.relIndex_dvd_index_of_normal E
  · exact N.relIndex_dvd_card E

private theorem janko_factor_action (S : Sylow 2 G) (C J E : Subgroup G)
    (e : C ≃* Janko1.Model) (hi : (normalizer (C : Set G)).index = 2)
    [Group.IsSolvable J] (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J)
    (ho : Odd (Nat.card E)) :
    E ≤ normalizer (C : Set G) ∧
      ∃ Q : Sylow 2 (MulAut C),
        (Q : Subgroup (MulAut C)) =
          ((S : Subgroup G).subgroupOf (normalizer (C : Set G))).map C.normalizerMonoidHom ∧
        (J.subgroupOf (normalizer (C : Set G))).map C.normalizerMonoidHom ≤
          normalizer (Q : Set (MulAut C)) ∧
        Nat.card ((E.subgroupOf (normalizer (C : Set G))).map C.normalizerMonoidHom) ∣ 21 := by
  let N := normalizer (C : Set G)
  let a : MulAut C ≃* Janko1.Model := (MulAut.congr e).trans jankoInnerEquiv.symm
  let f := C.normalizerMonoidHom
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨c,hc⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e z)
    refine ⟨⟨e.symm c,C.le_normalizer (e.symm c).property⟩,?_⟩
    apply (MulAut.congr e).injective
    have he : f ⟨e.symm c,C.le_normalizer (e.symm c).property⟩ = MulAut.conj (e.symm c) := by
      ext x
      rfl
    rw [he,MulAut.congr_conj,e.apply_symm_apply]
    exact hc
  let : N.Normal := N.normal_of_index_eq_two hi
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal N
  let Q := P.mapSurjective hf
  let U := Q.mapSurjective (f := a.toMonoidHom) a.surjective
  let JN := J.subgroupOf N
  let EN := E.subgroupOf N
  let g := a.toMonoidHom.comp f
  let : Group.IsSolvable JN := Group.isSolvable_of_isSolvable_injective
    (f := N.subtype.subgroupComap J) (by
      intro x y hh
      exact Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : G)) hh)))
  let : Group.IsSolvable (JN.map g) := Group.isSolvable_of_surjective (g.subgroupMap_surjective JN)
  have hUN : (U : Subgroup Janko1.Model) ≤ JN.map g := by
    change ((P : Subgroup N).map f).map a.toMonoidHom ≤ _
    rw [map_map,hP]
    exact map_mono (comap_mono hSJ)
  have hEN := odd_le_index_two E N ho hi
  have hodd : Odd (Nat.card (EN.map g)) :=
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv]; exact ho : Odd (Nat.card EN)).of_dvd_nat
      (card_map_dvd _ _)
  obtain ⟨hn,hcard⟩ := Janko1.LocalStructure.odd_solvable_overgroup_card_dvd_twenty_one
    U (JN.map g) (EN.map g) hUN (map_mono (comap_mono hEJ)) hodd
  refine ⟨hEN,Q,?_,?_,?_⟩
  · change (P : Subgroup N).map f = _
    rw [hP]
  · apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    change (JN.map f).map a.toMonoidHom ≤ (normalizer ((Q : Subgroup (MulAut C)) : Set (MulAut C))).map a.toMonoidHom
    rw [map_equiv_normalizer_eq,map_map]
    exact hn
  · rw [←map_map,card_map_of_injective a.injective] at hcard
    exact hcard

/-- The original paired J₁ branch yields a genuine Sylow-normalizing
factor action whose odd order divides 21. -/
theorem nonnormal_janko_action
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : ¬ C.Normal)
    (hKC : K ≤ C.map Y.subtype) (e : (C ⧸ pCore 2 C) ≃* Janko1.Model) :
    PairedJankoAction T A B Y C := by
  have hmoved := nonnormal_container_seed_moved h.qtke hKH hH.1.1.2 hKL hY C hC hKC hCn
  have hlin := moved_seed_linear_four_of_escape h.qtke hKL hKT horbit hmoved hY hescape
  obtain ⟨hB,hBc⟩ := moved_seed_right_hall_plane h hH hgen c hKH hK hqs hKT horbit hmoved hlin
  have hTY := hH.1.1.2.trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let N := normalizer (Cbar : Set (Y ⧸ pCore 2 Y))
  let D := (A.subgroupOf Y).map q
  let E := (B.subgroupOf Y).map q
  let P := (T.subtype hTY).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let JY := (A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y) ⊔ B.subgroupOf Y
  let J := JY.map q
  have hi : N.index = 2 := by
    rw [cComponent_normalizer_index_quotient hC]
    exact (nonnormal_container_models h.qtke hKH hH.1.1.2 hKL horbit hY hescape C hC hKC hCn).1
  have hoddD : Odd (Nat.card D) := by
    have hoA : Odd (Nat.card A) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
      exact OddHall.odd_hall_odd c.left_hall
    have hoAY : Odd (Nat.card (A.subgroupOf Y)) := by
      rw [←inf_subgroupOf_right A Y,Nat.card_congr
        (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
      exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
    exact hoAY.of_dvd_nat (card_map_dvd _ q)
  have hEc : Nat.card E ∣ 9 := by
    have hd := card_map_dvd (B.subgroupOf Y) q
    rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hd
    exact hd
  have hED : E ≤ normalizer (D : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  have hodd : Odd (Nat.card (D ⊔ E : Subgroup (Y ⧸ pCore 2 Y))) := by
    have hh := hoddD.mul ((by decide : Odd 9).of_dvd_nat hEc)
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes D E hED] at hh
    exact hh.of_dvd_nat (dvd_mul_left _ _)
  have hLH : ¬ L ≤ H := by
    intro hh
    exact hescape (inf_le_left.trans ((c.left_le.trans (inf_le_left.trans hh)).trans
      (le_normalizer_residual H)))
  have prep := cartanPreparation_of_not_le h hH hgen hLH
  let M := normalizer (L : Set G) ⊓ H
  let V := localBorel T L ⊔ M
  let : Group.IsSolvable (localBorel T L) := prep.borel_solvable
  let : Group.IsSolvable M := prep.intersection_solvable
  let : Group.IsSolvable V := Group.isSolvable_sup_of_normalizes _ _ prep.intersection_normalizes
  have hJV : JY.map Y.subtype ≤ V := by
    rw [Subgroup.map_sup,Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTY,
      map_subgroupOf_eq_of_le hBY]
    exact sup_le (sup_le ((inf_le_left.trans c.left_le).trans le_sup_left)
      ((le_inf h.sylow_normalizes hH.1.1.2).trans le_sup_right))
      (c.right_le.trans le_sup_right)
  let : Group.IsSolvable JY := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hJV).comp
      (JY.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    ((inclusion_injective hJV).comp (JY.equivMapOfInjective Y.subtype Y.subtype_injective).injective)
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (q.subgroupMap_surjective JY)
  let eC := (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  obtain ⟨hEN,Q,hQ,hn,hcard⟩ := janko_factor_action P Cbar J (D ⊔ E) eC hi
    (map_mono (show (T : Subgroup G).subgroupOf Y ≤ JY from le_sup_right.trans le_sup_left))
    (sup_le (map_mono (le_sup_left.trans le_sup_left)) (map_mono le_sup_right)) hodd
  refine ⟨hEN,Q,hQ,?_,hcard,?_,?_⟩
  · simpa only [J,JY,Subgroup.map_sup] using hn
  · let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
    let i : A.subgroupOf Y →* A := {
      toFun x := ⟨x.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hi : Function.Injective i := by
      intro x y hh
      exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) hh))
    let : IsCyclic (A.subgroupOf Y) := isCyclic_of_injective i hi
    let : IsCyclic D := isCyclic_of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _)
    let : IsCyclic (D.subgroupOf N) :=
      (subgroupOfEquivOfLe (le_sup_left.trans hEN)).isCyclic.mpr inferInstance
    exact isCyclic_of_surjective (Cbar.normalizerMonoidHom.subgroupMap _)
      (Cbar.normalizerMonoidHom.subgroupMap_surjective _)
  · have h9 : Nat.card ((E.subgroupOf N).map Cbar.normalizerMonoidHom) ∣ 9 := by
      have hd := card_map_dvd (E.subgroupOf N) Cbar.normalizerMonoidHom
      rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_right.trans hEN)).toEquiv] at hd
      exact hd.trans hEc
    have h21 : Nat.card ((E.subgroupOf N).map Cbar.normalizerMonoidHom) ∣ 21 :=
      (card_dvd_of_le (map_mono (comap_mono (show E ≤ D ⊔ E from le_sup_right)))).trans hcard
    exact Nat.dvd_gcd h9 h21

end LocalSieve

open Chapter1.Section02.LocalModels
/-- The original seed reduction retains all earlier exclusions and constructs
the actual J₁ factor action in the nonnormal branch. -/
theorem localCartan_escape_seed_pairedJanko_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
          PairedJankoAction T A B Y C ∧ PairedJankoPlacement T Y C)) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hcase⟩ :=
    localCartan_escape_seed_pairedPrime_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,?_⟩
  by_cases hCn : C.Normal
  · exact Or.inl hCn
  obtain ⟨hi,hKlt,hlin,hB,hBc,⟨e⟩⟩ := hcase.resolve_left hCn
  exact Or.inr ⟨hi,hKlt,hlin,hB,hBc,⟨e⟩,
    LocalSieve.nonnormal_janko_action h hH hgen c hKH hK hqs hKT hKL hR hY hescape C hC hCn hKC e,
    LocalSieve.nonnormal_janko_quotient_pair (hH.1.1.2.trans hY.2) C hC hi e⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
