module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearCoverage
public import Theory.GroupTheory.LocalSylowNormalizerImage
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
/-!
# An actual cubic Cartan in the selected paired component

The original paired quotient identifies the Baumann image with two Sylow
coordinates. Its first Borel normalizes that image. The action kernel inside
the selected local join lies in its Sylow Baumann subgroup, so the full
Borel order lifts to the actual component-normalizer intersection. At field
order four Cauchy's theorem gives an actual cubic there, together with the
same selected-component coverage, localV, and positive alpha fixed subgroup.
Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746--747.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
theorem action_kernel_in_sylow_join
    (q : G →* H) (hq : IsPGroup 2 q.ker)
    (K B : Subgroup G) (hS : Chapter1.IsSylowIn 2 B (K ⊔ B)) :
    q.ker ⊓ (K ⊔ B) ≤ B := by
  obtain ⟨P,hP⟩ := hS
  have hh : q.ker.subgroupOf (K ⊔ B) ≤ (P : Subgroup (K ⊔ B : Subgroup G)) :=
    hq.comap_subtype.le_sylow_of_normal P
  have hm := map_mono (f := (K ⊔ B).subtype) hh
  rwa [subgroupOf_map_subtype,hP] at hm

private theorem pair_sylow_coordinates {A : Type*} [Group A] [Finite A]
    (R : Sylow 2 (A × A)) :
    ∃ P Q : Sylow 2 A, (R : Subgroup (A × A)) = (P : Subgroup A).prod Q := by
  let P := R.mapSurjective (f := MonoidHom.fst A A) (fun g => ⟨(g,1),rfl⟩)
  let Q := R.mapSurjective (f := MonoidHom.snd A A) (fun g => ⟨(1,g),rfl⟩)
  have hp : IsPGroup 2 (P × Q) := by
    obtain ⟨m,hm⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := Q.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := m+n) (by rw [Nat.card_prod,hm,hn,pow_add])
  refine ⟨P,Q,(R.is_maximal' (hp.of_equiv ((P : Subgroup A).prodEquiv (Q : Subgroup A)).symm) ?_).symm⟩
  intro x hx
  exact ⟨mem_map_of_mem (MonoidHom.fst A A) hx,mem_map_of_mem (MonoidHom.snd A A) hx⟩

set_option backward.isDefEq.respectTransparency false in
theorem paired_source_selected_cartan_divisor
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hkt : IsPGroup 2 q.ker)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (K : Subgroup G)
    (hK : K.map q = d.first.map
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (K ⊔ baumann (T : Subgroup G))) :
    Nat.card F.Carrier - 1 ∣
      Nat.card (K ⊓ normalizer (baumann (T : Subgroup G) : Set G) : Subgroup G) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  let A := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  let B := baumann (T : Subgroup G)
  obtain ⟨_,_,_,_,⟨_,hB⟩,_⟩ := source_images_and_fixedSpace T hP U hU hJ q hq hk d F c hexchange
  obtain ⟨R,hR⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal Y
  obtain ⟨P,Q,hPQ⟩ := pair_sylow_coordinates
    (R.mapSurjective (f := c.action.groupEquiv.toMonoidHom) c.action.groupEquiv.surjective)
  have hBQ : B.map q = ((P : Subgroup A).prod Q).map j := by
    rw [hB]
    change (T.mapSurjective hq : Subgroup H) ⊓ Y = _
    rw [←hR,←hPQ]
    change (R : Subgroup Y).map Y.subtype =
      ((R : Subgroup Y).map c.action.groupEquiv.toMonoidHom).map j
    rw [Subgroup.map_map]
    congr 1
    ext x
    change (x:H) = (c.action.groupEquiv.symm (c.action.groupEquiv x):H)
    rw [c.action.groupEquiv.symm_apply_apply]
  have hKA : K.map q = ((⊤ : Subgroup A).prod ⊥).map j := by
    rw [hK]
    change d.first.map Y.subtype = _
    rw [←c.first_eq,Subgroup.map_map]
  have hd := first_axis_normalizer_card_dvd q K B
    (action_kernel_in_sylow_join q hkt K B hS) j
    (Y.subtype_injective.comp c.action.groupEquiv.symm.injective)
    (P : Subgroup A) (Q : Subgroup A) hKA hBQ
  rw [Matrix.SpecialLinearGroup.card_sylow_normalizer_even P] at hd
  exact (dvd_mul_left _ _).trans hd

/-- Recover the intrinsic Sylow witness of the literal local-class inclusion. -/
theorem localClass_inclusion_sylow (K B : Subgroup G)
    (h : ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right))) :
    Chapter1.IsSylowIn 2 B (K ⊔ B) := by
  obtain ⟨P,hP,_⟩ := h.sylow
  refine ⟨P,?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [←hP] at hy
    obtain ⟨b,hb⟩ := hy
    exact (congrArg (K ⊔ B : Subgroup G).subtype hb) ▸ b.property
  · intro hx
    exact ⟨⟨x,(show B ≤ K ⊔ B from le_sup_right) hx⟩,
      hP ▸ (show (⟨x,(show B ≤ K ⊔ B from le_sup_right) hx⟩ : (K ⊔ B : Subgroup G)) ∈
        (inclusion (show B ≤ K ⊔ B from le_sup_right)).range from ⟨⟨x,hx⟩,rfl⟩),rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem first_component_localClass_with_cubic
    {C : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hkc : q.ker = pCore 2 G)
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (hF : Nat.card F.Carrier = 4) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
    let B := baumann (T : Subgroup G)
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = d.first.map Y.subtype ∧
      (solvableResidual (factorPreimage q Y d.first)).map (factorPreimage q Y d.first).subtype = L ∧
      U ≤ normalizer (L : Set G) ∧ B ≤ normalizer (L : Set G) ∧
      GlaubermanNiles.InLocalClass (inclusion (show B ≤ L ⊔ B from le_sup_right)) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ L ⊔ B from le_sup_right))).map (L ⊔ B).subtype =
        (⁅U,L⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧
      (∃ t ∈ (T : Subgroup G), pResidual 2 G = L ⊔ L.map (MulAut.conj t).toMonoidHom) ∧
      ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = 3 ∧
        A ≤ normalizer (baumann (T : Subgroup G) : Set G) := by
  obtain ⟨K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover⟩ :=
    first_component_localClass_with_coverage h36 hG T hP U hU hJ q hq hk hkc hs hfit d F c hexchange
  have hS := localClass_inclusion_sylow K (baumann (T : Subgroup G)) hlocal
  have hd := paired_source_selected_cartan_divisor T hP U hU hJ q hq hk
    (hkc.symm ▸ (pCore_isPGroup : IsPGroup 2 (pCore 2 G))) d F c hexchange K hi hS
  have h3 : 3 ∣ Nat.card (K ⊓ normalizer (baumann (T : Subgroup G) : Set G) : Subgroup G) := by
    simpa only [hF] using hd
  let I := K ⊓ normalizer (baumann (T : Subgroup G) : Set G)
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := I) 3 h3
  let A := (zpowers b).map I.subtype
  have hAI : A ≤ I := map_subtype_le _
  have hA : Nat.card A = 3 := by
    rw [show A=(zpowers b).map I.subtype from rfl,card_map_of_injective I.subtype_injective,Nat.card_zpowers,hb]
  exact ⟨K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,
    A,hAI.trans inf_le_left,hA,hAI.trans inf_le_right⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
