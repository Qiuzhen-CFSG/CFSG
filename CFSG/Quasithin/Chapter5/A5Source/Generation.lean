module
public import CFSG.Quasithin.Chapter5.A5Source.RecognitionEndgame
public import Theory.GroupTheory.FiveCoreConjugateGeneration
/-!
# Generating conjugate cores in the original A5 Baumann argument

The actual marked Baumann action has kernel Q=O₂(L Baum(T)), and the full
Sylow image normalizes and exchanges its two support transpositions.
If Q and an escaping elementary conjugate W fail to generate Baum(T), the
fixed-hyperplane argument makes W and its Sylow conjugate generate it.
Conjugating this pair back to Q supplies the required replacement conjugator.
The same generated pair proves centrality of C_{Baum(T)}(L), preserving
its containment in the replacement core for the dihedral endgame.

The point-centralizer control used to obtain the initial elementary crossing
remains the genuine earlier source 4.3.2 input.
Source: Aschbacher–Smith 5.1.7(1), printed pp.633–634.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

private theorem baumann_marking_sylow_image
    (q : normalizer (V : Set G) →* Equiv.Perm (Fin 5))
    (hq : Function.Surjective q)
    (himage : ((baumann (T : Subgroup G)).subgroupOf (normalizer (V : Set G))).map q = Offenders.D 5)
    (hcard : Nat.card (normalizer (Offenders.D 5 : Set (Equiv.Perm (Fin 5)))) = 8) :
    ((T : Subgroup G).subgroupOf (normalizer (V : Set G))).map q =
      normalizer (Offenders.D 5 : Set (Equiv.Perm (Fin 5))) := by
  let N := normalizer (V : Set G)
  let S := baumann (T : Subgroup G)
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hn : (T : Subgroup G).subgroupOf N ≤ normalizer (S.subgroupOf N : Set N) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro s
    change (s:G) ∈ S ↔ (t:G) * (s:G) * (t:G)⁻¹ ∈ S
    exact mem_normalizer_iff.mp (hTS ht) (s:G)
  have hle : ((T : Subgroup G).subgroupOf N).map q ≤ normalizer (Offenders.D 5 : Set _) := by
    rw [←himage]
    exact (map_mono hn).trans (le_normalizer_map q)
  apply eq_of_le_of_card_ge hle
  let R := (T.subtype d.flag.T_normalizes).mapSurjective hq
  have hr : (R : Subgroup (Equiv.Perm (Fin 5))) = ((T : Subgroup G).subgroupOf N).map q := rfl
  rw [←hr,R.card_eq_multiplicity,hcard,Nat.card_perm,Nat.card_fin]
  decide +kernel


private theorem baumann_marking_kernel
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (q : normalizer (V : Set G) →* Equiv.Perm (Fin 5))
    (m : Multiplicative (BinaryPermutation.core (Fin 5)) →* G)
    (hm : Function.Injective m) (hr : m.range = V)
    (he : ∀ (n : normalizer (V : Set G)) (x : BinaryPermutation.core (Fin 5)),
      (n:G) * m (Multiplicative.ofAdd x) * (n:G)⁻¹ =
        m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q n) x))) :
    (q.comp (inclusion (show baumann (T : Subgroup G) ≤ normalizer (V : Set G) from
      inf_le_left.trans d.flag.T_normalizes))).ker =
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).subgroupOf (baumann (T : Subgroup G)) := by
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let p := q.comp (inclusion (show S ≤ normalizer (V : Set G) from inf_le_left.trans d.flag.T_normalizes))
  have hker : Q = S ⊓ centralizer (V : Set G) := baumann_core_centralizer_of_escape d hout
  change p.ker = Q.subgroupOf S
  rw [hker]
  ext s
  change p s = 1 ↔ (s:G) ∈ S ∧ (s:G) ∈ centralizer (V : Set G)
  constructor
  · intro hh
    refine ⟨s.property,?_⟩
    intro x hx
    obtain ⟨y,rfl⟩ := hr.symm ▸ hx
    have hv := he (inclusion (show S ≤ normalizer (V : Set G) from inf_le_left.trans d.flag.T_normalizes) s) y.toAdd
    change _ = m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) y.toAdd)) at hv
    rw [hh,map_one] at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  · intro hh
    apply BinaryPermutation.FivePair.core_injective
    apply LinearMap.ext
    intro x
    apply Multiplicative.ofAdd.injective
    apply hm
    change m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) = m (Multiplicative.ofAdd x)
    have heq := he (inclusion (show S ≤ normalizer (V : Set G) from inf_le_left.trans d.flag.T_normalizes) s) x
    change _ = m (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) at heq
    rw [←heq]
    exact mul_inv_eq_iff_eq_mul.mpr (hh.2 _ (hr.le ⟨_,rfl⟩)).symm


private theorem replacement_conjugate_of_exchanged_generation
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hQ : IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2))
    (g : G) (hg : g ∈ normalizer (baumann (T : Subgroup G) : Set G))
    (t : G) (ht : t ∈ (T : Subgroup G))
    (hcross : baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom)
    (hgen : ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom ⊔
      (((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj t).toMonoidHom = baumann (T : Subgroup G)) :
    ∃ h ∈ normalizer (baumann (T : Subgroup G) : Set G),
      baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
        ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom ∧
      (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ⊔
        ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj h⁻¹).toMonoidHom =
          baumann (T : Subgroup G) := by
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let C := S ⊓ centralizer (L : Set G)
  let W := Q.map (MulAut.conj g⁻¹).toMonoidHom
  let Wt := W.map (MulAut.conj t).toMonoidHom
  change W ⊔ Wt = S at hgen
  change C ≤ W at hcross
  let := hQ
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 Wt := IsElementaryAbelian.map _
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf hTS (d.normalizes_L.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hCt : C ≤ Wt := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hcross
    exact (mem_normalizer_iff_map_conj_eq.mp (hTC ht)).ge.trans hh
  have hCS : C ≤ centralizer (S : Set G) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    apply sup_le
    · intro w hw c hc
      exact congrArg Subtype.val (mul_comm (⟨c,hcross hc⟩ : W) ⟨w,hw⟩)
    · intro w hw c hc
      exact congrArg Subtype.val (mul_comm (⟨c,hCt hc⟩ : Wt) ⟨w,hw⟩)
  let h := g * t⁻¹ * g⁻¹
  have hh : h ∈ normalizer (S : Set G) :=
    mul_mem (mul_mem hg ((normalizer (S:Set G)).inv_mem (hTS ht)))
      ((normalizer (S:Set G)).inv_mem hg)
  refine ⟨h,hh,?_,?_⟩
  · have hVQ : V ≤ Q := by
      rw [show Q=V⊔C from baumann_core_product_of_escape d hout]
      exact le_sup_left
    have hVS : V ≤ S := hVQ.trans (baumann_core_le_of_escape d hout)
    have hVhS : V.map (MulAut.conj h⁻¹).toMonoidHom ≤ S :=
      (map_mono hVS).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (S:Set G)).inv_mem hh))
    have he := CrossingPair.sylow_centralizer_crossing V S h hh
    rw [←baumann_core_centralizer_of_escape d hout] at he
    change C ≤ Q.map (MulAut.conj h⁻¹).toMonoidHom
    change S ⊓ centralizer (V.map (MulAut.conj h⁻¹).toMonoidHom : Set G) = Q.map (MulAut.conj h⁻¹).toMonoidHom at he
    rw [←he]
    exact le_inf inf_le_left (hCS.trans (centralizer_le hVhS))
  · have hm := congrArg (fun A : Subgroup G => A.map (MulAut.conj g).toMonoidHom) hgen
    have he1 : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    have he2 : (MulAut.conj g).toMonoidHom.comp
        ((MulAut.conj t).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) =
          (MulAut.conj h⁻¹).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply,h,mul_assoc]
    change Q ⊔ Q.map (MulAut.conj h⁻¹).toMonoidHom = S
    have hgS : S.map (MulAut.conj g).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp hg
    simpa only [Subgroup.map_sup,Wt,W,map_map,he1,map_id,he2,hgS] using hm


theorem exists_baumann_generated_elementary_core
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hc : ∀ x ∈ baumann (T : Subgroup G) ⊓ centralizer (L : Set G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    ∃ g ∈ normalizer (baumann (T : Subgroup G) : Set G),
      IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2) ∧
      baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
        ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom ∧
      (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ⊔
        ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom =
          baumann (T : Subgroup G) := by
  obtain ⟨g,hg,_,hmv,hcross,hQ⟩ := exists_baumann_elementary_conjugate_core d hout hc
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let C := S ⊓ centralizer (L : Set G)
  let W := Q.map (MulAut.conj g⁻¹).toMonoidHom
  let := hQ
  have hQC : Q = V ⊔ C := baumann_core_product_of_escape d hout
  have hQS : Q ≤ S := baumann_core_le_of_escape d hout
  have hVS : V ≤ S := (le_sup_left.trans hQC.ge).trans hQS
  have hWS : W ≤ S := (map_mono hQS).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer (S:Set G)).inv_mem hg))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (W.subgroupOf S) := IsElementaryAbelian.subgroupOf hWS
  have hSN : S ≤ normalizer (V : Set G) := inf_le_left.trans d.flag.T_normalizes
  have hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) :=
    fun hh => hout (baumann_normalizer_of_thompson_centralizes d hh)
  obtain ⟨q,m,hq,hm,hr,he,himage⟩ := exists_baumann_action_marking d hJ
  let p := q.comp (inclusion hSN)
  have hp : p.range = BinaryPermutation.FivePairFixedSpaces.pairClosure := by
    have hD : Offenders.D 5 = BinaryPermutation.FivePairFixedSpaces.pairClosure := by
      apply congrArg Subgroup.closure
      ext a
      constructor
      · rintro ⟨i,_,rfl⟩
        fin_cases i <;> simp [Offenders.pairSwap,BinaryPermutation.FivePairFixedSpaces.first,
          BinaryPermutation.FivePairFixedSpaces.second]
      · intro ha
        rcases ha with rfl | ha
        · exact ⟨0,by decide,rfl⟩
        · exact ⟨1,by decide,ha⟩
    rw [←hD,←himage]
    ext a
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨inclusion hSN s,s.property,rfl⟩
    · rintro ⟨s,hs,rfl⟩
      exact ⟨⟨s,hs⟩,rfl⟩
  have hker : p.ker = (V.subgroupOf S) ⊔ (C.subgroupOf S) := by
    rw [show p.ker = Q.subgroupOf S from baumann_marking_kernel d hout q m hm hr he,
      hQC,subgroupOf_sup hVS inf_le_left]
  let m0 : Multiplicative (BinaryPermutation.core (Fin 5)) →* V.subgroupOf S := {
    toFun := fun x => ⟨⟨m x,hVS (hr.le ⟨x,rfl⟩)⟩,hr.le ⟨x,rfl⟩⟩
    map_one' := Subtype.ext (Subtype.ext (map_one m))
    map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul m x y)) }
  have hmi : Function.Injective m0 := fun x y hh => hm
    (congrArg (fun z : V.subgroupOf S => ((z:S):G)) hh)
  have hms : Function.Surjective m0 := by
    intro v
    obtain ⟨x,hx⟩ := hr.ge v.property
    exact ⟨x,Subtype.ext (Subtype.ext hx)⟩
  let f := MulEquiv.ofBijective m0 ⟨hmi,hms⟩
  have hfe : ∀ (s:S) (x : BinaryPermutation.core (Fin 5)),
      (f (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (p s) x)) : S) =
        s * (f (Multiplicative.ofAdd x) : S) * s⁻¹ := by
    intro s x
    apply Subtype.ext
    exact (he (inclusion hSN s) x).symm
  have hd : Disjoint (V.subgroupOf S) (C.subgroupOf S) := by
    rw [disjoint_def]
    intro x hx hy
    exact Subtype.ext (disjoint_def.mp (baumann_core_disjoint_of_escape d hout) hx hy)
  have hCW : C.subgroupOf S ≤ W.subgroupOf S := fun _ hx => hcross hx
  have hcard : Nat.card (W.subgroupOf S) =
      Nat.card ((V.subgroupOf S) ⊔ (C.subgroupOf S) : Subgroup S) := by
    rw [←subgroupOf_sup hVS inf_le_left,←hQC]
    rw [Nat.card_congr (subgroupOfEquivOfLe hWS).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv]
    exact card_map_of_injective (MulAut.conj g⁻¹).injective
  have hWq : (W.subgroupOf S).map p ≠ ⊥ := by
    intro hz
    have hle : W ≤ Q := by
      intro w hw
      have hh : (⟨w,hWS hw⟩ : S) ∈ p.ker :=
        (Subgroup.map_eq_bot_iff _).mp hz hw
      rw [hker,←subgroupOf_sup hVS inf_le_left,←hQC] at hh
      exact hh
    apply hmv
    exact (map_mono (show V ≤ Q from hQC ▸ le_sup_left)).trans hle
  have hD : Offenders.D 5 = BinaryPermutation.FivePairFixedSpaces.pairClosure := by
    rw [←hp,←himage]
    ext a
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨⟨s,hs⟩,rfl⟩
    · rintro ⟨s,rfl⟩
      exact ⟨inclusion hSN s,s.property,rfl⟩
  have hTimage := baumann_marking_sylow_image d q hq himage (by
    rw [hD]
    exact BinaryPermutation.FivePairFixedSpaces.card_pairNormalizer)
  have hk := BinaryPermutation.FivePairFixedSpaces.exchange_mem_pairNormalizer
  rw [←hD,←hTimage] at hk
  obtain ⟨tn,ht,hkt⟩ := hk
  let t : G := tn
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  let e := S.normalizerMonoidHom ⟨t,hTS ht⟩
  have heV : (V.subgroupOf S).map e.toMonoidHom = V.subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hVS]
    have hcomp : S.subtype.comp e.toMonoidHom = (MulAut.conj t).toMonoidHom.comp S.subtype := rfl
    rw [hcomp,←map_map,map_subgroupOf_eq_of_le hVS]
    exact mem_normalizer_iff_map_conj_eq.mp (d.flag.T_normalizes ht)
  have heq : ∀ s, p (e s) = BinaryPermutation.FivePairFixedSpaces.exchange * p s *
      BinaryPermutation.FivePairFixedSpaces.exchange⁻¹ := by
    intro s
    change q (tn * inclusion hSN s * tn⁻¹) = _
    rw [map_mul,map_mul,map_inv,hkt]
    rfl
  rcases FiveCoreConjugateGeneration.generation (V.subgroupOf S) (C.subgroupOf S)
      (W.subgroupOf S) hd hCW hcard p hp hker hWq f hfe e heV
      BinaryPermutation.FivePairFixedSpaces.exchange heq
      BinaryPermutation.FivePairFixedSpaces.exchange_mem_pairNormalizer
      BinaryPermutation.FivePairFixedSpaces.exchange_not_mem_pairClosure with hgen | hgen
  · refine ⟨g,hg,hQ,hcross,?_⟩
    have h := congrArg (fun A : Subgroup S => A.map S.subtype) hgen
    change Q ⊔ W = S
    have hCSmap : (C.subgroupOf S).map S.subtype = C := map_subgroupOf_eq_of_le inf_le_left
    simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hVS,
      hCSmap,map_subgroupOf_eq_of_le hWS,
      ←MonoidHom.range_eq_map,range_subtype,←hQC] using h
  · have hgen' : W ⊔ W.map (MulAut.conj t).toMonoidHom = S := by
      have h := congrArg (fun A : Subgroup S => A.map S.subtype) hgen
      have hcomp : S.subtype.comp e.toMonoidHom = (MulAut.conj t).toMonoidHom.comp S.subtype := rfl
      rw [Subgroup.map_sup,map_map,hcomp,←map_map,
        map_subgroupOf_eq_of_le hWS] at h
      simpa only [←MonoidHom.range_eq_map,range_subtype] using h
    obtain ⟨h,hh,hc,hgen⟩ := replacement_conjugate_of_exchanged_generation d hout hQ g hg t ht hcross hgen'
    exact ⟨h,hh,hQ,hc,hgen⟩

end CFSG.Quasithin.Chapter5.A5Source
