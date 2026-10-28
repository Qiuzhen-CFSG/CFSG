module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.HallTorus
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
public import Theory.GroupTheory.IndexTwoNormalizer

/-!
# The whole paired Hall subgroup in the original overlap

The index-two component normalizer makes the join of the two component
intersections normal in the overlap. The original E.2.2 maximal product
shows that its quotient is a two-group, so the given odd Hall subgroup
lies in that join. Hall restriction and projection through either normal
factor split this very Hall subgroup into its two literal intersections.
Their disjointness and mutual normalization give the multiplication
isomorphism. The cyclic-factor theorem identifies the whole subgroup as
abelian of order (2^f-1)^2 at the independent model exponent f.

The original counterexample application constructs the Hall subgroup and
retains its actual Sylow exchange element. No field exponent is relabelled
as the generation minimum, and exchange does not assert that the square
centralizes a factor. FixedPoints supplies that step at a suitably chosen
prime using the original natural marking. Recognition remains with this
owner; qt-d-1222-shadow-linear-geometry discharges the preceding source
inputs in the final assembly.
Source: Aschbacher--Smith, E.2.2 and 11.3.5(2), pp.215--216,771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem hall_map_surjective {Y : Type*} [Group Y] [Finite Y]
    (A : Subgroup X) (hA : IsHallSubgroup OddHall.oddPrimes A)
    (f : X →* Y) (hf : Function.Surjective f) :
    IsHallSubgroup OddHall.oddPrimes (A.map f) :=
  ⟨fun p hp => hA.p_in_pi_of_p_dvd_card p (hp.trans (A.card_map_dvd f)),
    fun p hp => hA.p_in_pi_of_p_dvd_index p (hp.trans (index_map_dvd (H := A) hf))⟩

private theorem hall_split_normal (A B C : Subgroup X)
    (hA : IsHallSubgroup OddHall.oddPrimes A) [B.Normal] [C.Normal]
    (hBC : B ⊔ C = ⊤) : A = (A ⊓ B) ⊔ (A ⊓ C) := by
  let q := QuotientGroup.mk' B
  have hC : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf C) :=
    OddHall.hall_restrict_of_normalizes (hA.subgroupOf le_top) le_top le_top
      (by rw [normalizer_eq_top]; exact le_top)
  have hqC : Function.Surjective (q.comp C.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    have hh := congrArg (map q) hBC
    rw [Subgroup.map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective B),
      show B.map q = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']), bot_sup_eq] at hh
    exact hh
  have he : (A ⊓ C).map q = A.map q := by
    have hh := hall_map_surjective _ hC _ hqC
    rw [←map_map,subgroupOf_map_subtype] at hh
    exact hh.eq_of_le (hall_map_surjective A hA q (QuotientGroup.mk'_surjective B))
      (map_mono inf_le_left)
  apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro a ha
  have hqa : q a ∈ (A ⊓ C).map q := he.symm ▸ mem_map_of_mem q ha
  obtain ⟨c,hc,hca⟩ := hqa
  have hb : a*c⁻¹ ∈ B := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a*c⁻¹) = 1
    rw [map_mul,map_inv,hca,mul_inv_cancel]
  have hz : a*c⁻¹ ∈ (A ⊓ B) ⊔ (A ⊓ C) :=
    (show A ⊓ B ≤ (A ⊓ B) ⊔ (A ⊓ C) from le_sup_left)
      ⟨A.mul_mem ha (A.inv_mem hc.1),hb⟩
  simpa only [inv_mul_cancel_right] using
    ((A ⊓ B) ⊔ (A ⊓ C)).mul_mem hz
      ((show A ⊓ C ≤ (A ⊓ B) ⊔ (A ⊓ C) from le_sup_right) hc)

private theorem hall_split_relative (M A B C : Subgroup X)
    (hAM : A ≤ M) (hBM : B ≤ M) (hCM : C ≤ M)
    (hA : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf M))
    (hAN : A ≤ B ⊔ C)
    (hBC : C ≤ normalizer (B : Set X)) (hCB : B ≤ normalizer (C : Set X)) :
    A = (A ⊓ B) ⊔ (A ⊓ C) := by
  let R := B ⊔ C
  let : (B.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le B.le_normalizer hBC)
  let : (C.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le hCB C.le_normalizer)
  have hAR : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf R) :=
    OddHall.hall_restrict_of_normalizes hA hAM (sup_le hBM hCM)
      (hAN.trans R.le_normalizer)
  have he := hall_split_normal (A.subgroupOf R) (B.subgroupOf R) (C.subgroupOf R) hAR
    (by rw [← subgroupOf_sup (show B ≤ R from le_sup_left) (show C ≤ R from le_sup_right),subgroupOf_self])
  have hh := congrArg (map R.subtype) he
  have hmap : (A.subgroupOf R).map R.subtype = A := map_subgroupOf_eq_of_le hAN
  simpa only [Subgroup.map_sup,Subgroup.map_inf _ _ _ R.subtype_injective,
    hmap,
    map_subgroupOf_eq_of_le (show B ≤ R from le_sup_left),
    map_subgroupOf_eq_of_le (show C ≤ R from le_sup_right)] using hh

omit [Finite X] in
private theorem hall_le_normal_sylow_supplement (M A R P : Subgroup X)
    (hAM : A ≤ M) (hRM : R ≤ M) (hPM : P ≤ M)
    (hA : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf M))
    (hR : M ≤ normalizer (R : Set X)) (hP : IsPGroup 2 P)
    (hgen : R ⊔ P = M) : A ≤ R := by
  let N := R.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer hR
  let q := QuotientGroup.mk' N
  let P' := P.subgroupOf M
  have hqP : Function.Surjective (q.comp P'.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    have hg : N ⊔ P' = ⊤ := by rw [←subgroupOf_sup hRM hPM,hgen,subgroupOf_self]
    have hh := congrArg (map q) hg
    rw [Subgroup.map_sup, map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
      show N.map q = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),bot_sup_eq] at hh
    exact hh
  have hquot : IsPGroup 2 (M ⧸ N) := (hP.comap_subtype).of_surjective _ hqP
  have hh := hall_le_normal_of_two_quotient N (A.subgroupOf M) hquot hA
  exact fun a ha => hh (show (⟨a,hAM ha⟩ : M) ∈ A.subgroupOf M from ha)

/-- Split the actual Hall subgroup using the original index-two component
normalizer and the original maximal product. -/
private theorem original_hall_split
    (P : Sylow 2 X) (M J : Subgroup X) (hPM : (P : Subgroup X) ≤ M)
    (hJ : J.IsCComponent) (hi : (normalizer (J : Set X)).index = 2)
    (hprod : ∃ u ∈ (P : Subgroup X), J ≠ J.conjBy u⁻¹ ∧
      (M : Set X) = (M ⊓ J : Subgroup X) *
        (((M ⊓ J).conjBy u⁻¹ : Subgroup X) : Set X) * (P : Set X))
    (A : Subgroup X) (hAM : A ≤ M)
    (hA : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf M))
    (t : X) (ht : t ∈ (P : Subgroup X))
    (htA : t ∈ normalizer (A : Set X)) (htJ : t ∉ normalizer (J : Set X)) :
    A = (A ⊓ J) ⊔ (A ⊓ J).map (MulAut.conj t).toMonoidHom := by
  let B := M ⊓ J
  let E := B.map (MulAut.conj t).toMonoidHom
  let C := J.map (MulAut.conj t).toMonoidHom
  have hMmap : M.map (MulAut.conj t).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hPM ht))
  have hE : E = M ⊓ C := by dsimp only [E,B,C]; rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective,hMmap]
  have hEM : E ≤ M := hE ▸ inf_le_left
  have hCJ : C ≤ normalizer (J : Set X) :=
    (le_cComponentLayer (hJ.map_equiv (MulAut.conj t))).trans (cComponentLayer_le_normalizer hJ)
  have hJC : J ≤ normalizer (C : Set X) :=
    (le_cComponentLayer hJ).trans (cComponentLayer_le_normalizer (hJ.map_equiv (MulAut.conj t)))
  have hEB : E ≤ normalizer (B : Set X) :=
    (le_inf (hEM.trans M.le_normalizer) ((hE ▸ inf_le_right).trans hCJ)).trans
      inf_normalizer_le_normalizer_inf
  have hBE : B ≤ normalizer (E : Set X) := by
    rw [hE]
    exact (le_inf (inf_le_left.trans M.le_normalizer) (inf_le_right.trans hJC)).trans
      inf_normalizer_le_normalizer_inf
  have hNM : (M ⊓ normalizer (J : Set X)).relIndex M = 2 :=
    normalizer_relIndex_eq_two_of_index_two_overgroup M ⊤ (normalizer (J : Set X)) J
      le_top (by simpa using hi) le_rfl ⟨t,hPM ht,htJ⟩
  have hNR : M ≤ normalizer ((B ⊔ E : Subgroup X) : Set X) :=
    index_two_normalizes_conjugate_join (M ⊓ normalizer (J : Set X)) M B inf_le_left hNM
      ((le_inf (inf_le_left.trans M.le_normalizer) inf_le_right).trans inf_normalizer_le_normalizer_inf)
      t (hPM ht) (fun hh => htJ hh.2)
  have hgen : (B ⊔ E) ⊔ (P : Subgroup X) = M := by
    apply le_antisymm (sup_le (sup_le inf_le_left hEM) hPM)
    obtain ⟨u,hu,hne,hm⟩ := hprod
    have huN : u⁻¹ ∉ normalizer (J : Set X) := fun hh =>
      hne (mem_normalizer_iff_map_conj_eq.mp hh).symm
    have hconj := map_conj_eq_of_index_two (normalizer (J : Set X)) J hi le_rfl u⁻¹ t huN htJ
    have he : (M ⊓ J).conjBy u⁻¹ = E := by
      change (M ⊓ J).map (MulAut.conj u⁻¹).toMonoidHom = E
      have hmmap : M.map (MulAut.conj u⁻¹).toMonoidHom = M :=
        mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hPM (P.inv_mem hu)))
      rw [Subgroup.map_inf _ _ _ (MulAut.conj u⁻¹).injective,hconj,hmmap]
      exact hE.symm
    intro x hx
    have hx' : x ∈ (B : Set X) * (E : Set X) * (P : Set X) := by
      change x ∈ (M : Set X) at hx
      rw [hm,he] at hx
      exact hx
    obtain ⟨z,⟨b,hb,e,he,rfl⟩,v,hv,rfl⟩ := hx'
    exact ((B ⊔ E) ⊔ (P : Subgroup X)).mul_mem
      ((show B ⊔ E ≤ (B ⊔ E) ⊔ (P : Subgroup X) from le_sup_left)
        ((B ⊔ E).mul_mem ((show B ≤ B ⊔ E from le_sup_left) hb)
          ((show E ≤ B ⊔ E from le_sup_right) he)))
      ((show (P : Subgroup X) ≤ (B ⊔ E) ⊔ (P : Subgroup X) from le_sup_right) hv)
  have hAR := hall_le_normal_sylow_supplement M A (B ⊔ E) (P : Subgroup X)
    hAM (sup_le inf_le_left hEM) hPM hA hNR P.isPGroup' hgen
  have hh := hall_split_relative M A B E hAM inf_le_left hEM hA hAR hEB hBE
  have hAB : A ⊓ B = A ⊓ J := by dsimp only [B]; rw [←inf_assoc,inf_eq_left.mpr hAM]
  have hAE : A ⊓ E = (A ⊓ J).map (MulAut.conj t).toMonoidHom := by
    have hamap : A.map (MulAut.conj t).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp htA
    rw [hE,←inf_assoc,inf_eq_left.mpr hAM,Subgroup.map_inf _ _ _ (MulAut.conj t).injective,hamap]
  rwa [hAB,hAE] at hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}
private theorem overlap_eq_maximal (h : Hypothesis1131At D S U₁ H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype h.outside.1.1.2) ⊤) :
    (normalizer (L : Set G)).subgroupOf H =
      ChapterB.minimalParabolicMax (T.subtype h.outside.1.1.2) hP := by
  let B := H ⊓ normalizer (L : Set G)
  have hi := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component h.outside
  have hBne : B.subgroupOf H ≠ ⊤ := by
    intro he
    have hm := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map,range_subtype] at hm
    exact hi.2.1.lt.ne hm
  have hcoat : IsCoatom (B.subgroupOf H) := by
    refine ⟨hBne,?_⟩
    intro Y hY
    have hy : B < Y.map H.subtype := by
      rw [←map_subgroupOf_eq_of_le (show B ≤ H from inf_le_left)]
      exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hY
    have he := (hi.2.1.eq_or_eq hy.le (map_subtype_le Y)).resolve_left hy.ne'
    apply map_injective H.subtype_injective
    rw [he,←MonoidHom.range_eq_map,range_subtype]
  have hle : B.subgroupOf H ≤ ChapterB.minimalParabolicMax (T.subtype h.outside.1.1.2) hP := by
    apply hP.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec _ hP).2,
        (ChapterB.minimalParabolicMax_spec _ hP).1.covBy_top⟩
    · intro x hx
      exact ⟨x.property,D.sylow_normalizes_component hx⟩
    · exact hcoat.lt_top
  have he := (hcoat.le_iff.mp hle).resolve_left (ChapterB.minimalParabolicMax_spec _ hP).1.ne_top
  simpa only [B,inf_subgroupOf_left] using he.symm



/-- The whole odd Hall subgroup is the product of its two actual component
intersections, with the same chosen exchange element. -/
theorem ComponentSeed.paired_hall_sup (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G))
    (htK : (t : G) ∉ normalizer (K : Set G)) :
    A = (A ⊓ K) ⊔ (A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom := by
  let P := T.subtype h.outside.1.1.2
  let J := K.subgroupOf H
  let M := (normalizer (L : Set G)).subgroupOf H
  let A' := A.subgroupOf H
  let t' : H := ⟨t,h.outside.1.1.2 t.property⟩
  have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  have hsolv := counterexample_not_solvable h pr hc hs
  have hM := overlap_eq_maximal h hP
  have hqJ : IsQuasisimple (J ⧸ pCore 2 J) := by
    let := s.quasisimple
    exact IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  have hprod := ChapterE.Structure.source_original_exchanged_product
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (outside_sqtk h) P hP hsolv s.component.2 hqJ
    (s.intrinsic_supplement h.outside.1.1.2) hn
  rw [← hM] at hprod
  have hAM : A' ≤ M := fun x hx => (hA hx).2
  have hmapM : M.map H.subtype = H ⊓ normalizer (L : Set G) :=
    (subgroupOf_map_subtype _ _).trans (inf_comm _ _)
  have hmapA : A'.map H.subtype = A := map_subgroupOf_eq_of_le (hA.trans inf_le_left)
  have hhall : IsHallSubgroup OddHall.oddPrimes (A'.subgroupOf M) := by
    let e := (M.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hmapM)
    have he : (A'.subgroupOf M).map e.toMonoidHom = A.subgroupOf (H ⊓ normalizer (L : Set G)) := by
      ext x
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ha
      · intro hx
        exact ⟨⟨⟨x,(hA hx).1⟩,x.property.2⟩,hx,Subtype.ext rfl⟩
    have hh := Paired.hall_map_surjective _ hHall e.symm.toMonoidHom e.symm.surjective
    rwa [←he,map_map,show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ from
      MonoidHom.ext (fun x => e.symm_apply_apply x),map_id] at hh
  have htJ : t' ∉ normalizer (J : Set H) := by
    rw [←subgroupOf_normalizer_eq s.component.1]
    exact htK
  have htA' : t' ∈ normalizer (A' : Set H) := by
    rw [←subgroupOf_normalizer_eq (hA.trans inf_le_left)]
    exact htA
  have he := Paired.original_hall_split P M J (fun x hx => D.sylow_normalizes_component hx)
    s.component.2 (s.paired_normalizer_index h pr hc hs hn) hprod A' hAM hhall
    t' t.property htA' htJ
  have hh := congrArg (map H.subtype) he
  have hAJ : (A' ⊓ J).map H.subtype = A ⊓ K := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,hmapA,
      map_subgroupOf_eq_of_le s.component.1]
  have hconj : ((A' ⊓ J).map (MulAut.conj t').toMonoidHom).map H.subtype =
      (A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom := by
    rw [map_map]
    change (A' ⊓ J).map ((MulAut.conj (t : G)).toMonoidHom.comp H.subtype) = _
    rw [←map_map,hAJ]
  simpa only [hmapA,Subgroup.map_sup,hAJ,hconj] using hh

/-- The multiplication isomorphism for the entire original Hall subgroup.
The second copy uses conjugation by the very same Sylow element. -/
theorem ComponentSeed.paired_hall_product (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G))
    (htK : (t : G) ∉ normalizer (K : Set G)) :
    ∃ e : (A ⊓ K : Subgroup G) × (A ⊓ K : Subgroup G) ≃* A,
      ∀ x y, (e (x,y) : G) = (x : G) * ((t : G) * (y : G) * (t : G)⁻¹) := by
  let B := A ⊓ K
  let C := B.map (MulAut.conj (t : G)).toMonoidHom
  have ho : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd hHall
    rwa [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv] at hh
  have hAN := s.paired_odd_normalizes h pr hc hs hn A (hA.trans inf_le_left) ho
  have hAB : A ≤ normalizer (B : Set G) :=
    (le_inf A.le_normalizer hAN).trans inf_normalizer_le_normalizer_inf
  have hAC : A ≤ normalizer (C : Set G) := by
    have hh := (map_mono (f := (MulAut.conj (t : G)).toMonoidHom) hAB).trans
      (B.le_normalizer_map _)
    have hamap : A.map (MulAut.conj (t : G)).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp htA
    rwa [hamap] at hh
  have hCA : C ≤ A := (map_mono (show B ≤ A from inf_le_left)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp htA)
  have hd := s.paired_odd_factors_disjoint h pr hc hs A ho t
    (h.outside.1.1.2 t.property) htK
  have hcomm : B ≤ centralizer (C : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (le_inf
      (le_normalizer_iff_commutator_le_left.mp (hCA.trans hAB))
      (le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hAC))).trans hd.eq_bot.le
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B C hd hcomm
  have hsup := s.paired_hall_sup h pr hc hs hn A hA hHall t htA htK
  let d : B ≃* C := B.equivMapOfInjective (MulAut.conj (t : G)).toMonoidHom
    (MulAut.conj (t : G)).injective
  exact ⟨((MulEquiv.refl B).prodCongr d).trans (e.trans (MulEquiv.subgroupCongr hsup.symm)),
    fun x y => he x (d y)⟩

/-- At its literal PSL₂ exponent f, the original Hall subgroup is abelian
of order (2^f-1)^2. No recognition at the generation minimum is assumed. -/
theorem ComponentSeed.paired_hall_abelian_card (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (t : T) (htA : (t : G) ∈ normalizer (A : Set G))
    (htK : (t : G) ∉ normalizer (K : Set G)) :
    IsMulCommutative A ∧ Nat.card A = (2 ^ f - 1) ^ 2 := by
  obtain ⟨hcyc,hcard⟩ := s.paired_hall_factor_cyclic_card h pr hc hs hn hf hm A hA hHall
  let := hcyc
  obtain ⟨e,_⟩ := s.paired_hall_product h pr hc hs hn A hA hHall t htA htK
  refine ⟨.of_comm fun x y => e.symm.injective (by simp only [map_mul,mul_comm]),?_⟩
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hcard,pow_two]

/-- Construct the source Hall subgroup with its full cyclic product,
retaining the actual exchange element and every ambient inclusion. -/
theorem ComponentSeed.exists_paired_hall_product_of_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
      Odd (Nat.card A) ∧ IsMulCommutative A ∧
      IsCyclic (A ⊓ K : Subgroup G) ∧ Nat.card (A ⊓ K : Subgroup G) = 2 ^ f - 1 ∧
      Nat.card A = (2 ^ f - 1) ^ 2 ∧
      ∃ t : T, (t : G) ∈ normalizer (A : Set G) ∧
        (t : G) ∉ normalizer (K : Set G) ∧
        ∃ e : (A ⊓ K : Subgroup G) × (A ⊓ K : Subgroup G) ≃* A,
          ∀ x y, (e (x,y) : G) = (x : G) * ((t : G) * (y : G) * (t : G)⁻¹) := by
  obtain ⟨A,hA,hHall,ho,t,htA,htK,_⟩ :=
    s.paired_linear_hall_exchange_of_model h pr hc hs hn hf hm
  obtain ⟨hcyc,hcard⟩ := s.paired_hall_factor_cyclic_card h pr hc hs hn hf hm A hA hHall
  obtain ⟨hab,hAcard⟩ := s.paired_hall_abelian_card h pr hc hs hn hf hm A hA hHall t htA htK
  exact ⟨A,hA,hHall,ho,hab,hcyc,hcard,hAcard,t,htA,htK,
    s.paired_hall_product h pr hc hs hn A hA hHall t htA htK⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
