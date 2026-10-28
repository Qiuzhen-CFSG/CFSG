module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Quadratic
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors.Alignment

/-!
# Excluding order-four images of the original Delta offenders

The actual chief coordinates place every original Delta image in the paired
wreath base. A base four-group has a conjugate meeting the specified Sylow
image in order two. The finite calculation uses only the eight-element
standard Sylow and its coordinate conjugate; surjectivity then selects an
actual conjugating element of H.

For the resulting original offender A, put B = A intersect O₂(H) and
P = A intersect T. Both B and P act quadratically on V, with the same
nontrivial order-two image. Thus C_A(V) has index four in A, while
C_V(A) = C_V(B) has order four. Since V has order sixteen,
D = C_A(V)V is elementary and has at least the maximum order of A.
Its literal image modulo O₂(H) has order two and lies in A's image.
The original inclusion-minimality contradicts this proper nontrivial image.
No chief quotient is treated as an internal subgroup, and no involution is
lifted through a quotient.

Completion applies the resulting order-two theorem to the uniform chief
transvections and all marked generator identities. The only preceding
source premises are produced by qt-e-152-small-parabolic and finally
discharged by qt-e-152-plane-geometry.

Source: Aschbacher--Smith 15.1.12(2), Notation 15.2.9 and 15.2.10--11,
printed pp.1090,1110--1111; refs/quasithin.pdf. The replacement is the
maximum-elementary counting argument of B.2.4 and B.2.8--9, applied to V.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
private theorem actor_card_index {M V D : Subgroup G}
    (hn : M ≤ normalizer (V : Set G)) (hDM : D ≤ M) :
    Nat.card (actor M V D hn) = (centralizer (V : Set G)).relIndex D := by
  rw [actor, ←Subgroup.relIndex_ker, MonoidHom.ker_rangeRestrict, actionHom_ker]
  exact relIndex_subgroupOf hDM

omit [Finite G] in
private theorem image_card_index {H A : Subgroup G} (hAH : A ≤ H) :
    Nat.card (offenderImage H A) = (twoCoreIn H).relIndex A := by
  rw [offenderImage, ←Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  have hh := relIndex_map_map_of_injective (pCore 2 H) (A.subgroupOf H) H.subtype_injective
  rw [map_subgroupOf_eq_of_le hAH] at hh
  exact hh.symm

omit [Finite G] in
private theorem card_inf_index (P Q : Subgroup G) :
    Nat.card (P ⊓ Q : Subgroup G) * P.relIndex Q = Nat.card Q := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (P ⊓ Q) Q bot_le inf_le_right

/-- Replacement in the original four-space retains maximum elementary order
and reduces the literal quotient image from order four to order two. -/
theorem ChosenSmallSource.delta_four_local_lift
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A ∈ delta H) (hfour : Nat.card (offenderImage H A)=4)
    (hidx : (T : Subgroup G).relIndex A=2) :
    let D := (A ⊓ centralizer (V : Set G)) ⊔ V
    D ∈ elementaryAbelianMaxSubgroups H ∧
      Nat.card (offenderImage H D)=2 ∧ offenderImage H D ≤ offenderImage H A := by
  let := h.prepared.elementary
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let B := A ⊓ twoCoreIn H
  let P := A ⊓ (T : Subgroup G)
  let C := A ⊓ centralizer (V : Set G)
  let D := C ⊔ V
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (inf_le_left : B ≤ A)
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_le (inf_le_left : P ≤ A)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (inf_le_left : C ≤ A)
  have hVQ := h.prepared.inside_core H hH
  have hVH := hVQ.trans (twoCore_le H)
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hQT : twoCoreIn H ≤ (T : Subgroup G) := by
    have hh := map_mono (f := H.subtype)
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
    change (pCore 2 H).map H.subtype ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hBP : B ≤ P := inf_le_inf_left A hQT
  have hNV := (h.wreath_intersections hH he).2
  have hCT : C ≤ (T : Subgroup G) := by
    rw [←hNV]
    exact le_inf (inf_le_left.trans hA.1.1)
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hfix : V ⊓ centralizer (A : Set G) = V ⊓ centralizer (B : Set G) := by
    have hh := congrArg (fun X : Subgroup G => V ⊓ X) (h.delta_fixed hH hA)
    simpa only [←inf_assoc,inf_eq_left.mpr hVU] using hh
  have hmove : ¬ B ≤ centralizer (V : Set G) := by
    intro hc
    have hVA : V ≤ centralizer (A : Set G) := by
      rw [←inf_eq_left,hfix]
      exact inf_eq_left.mpr (le_centralizer_iff.mp hc)
    have hAT : A ≤ (T : Subgroup G) := by
      rw [←hNV]
      exact le_inf hA.1.1 ((le_centralizer_iff.mp hVA).trans (Subgroup.centralizer_le_normalizer _))
    have hh := relIndex_eq_one.mpr hAT
    omega
  have hBT : B ≤ (T : Subgroup G) := hBP.trans inf_le_right
  have hBM := hBT.trans h.maximal.1.2
  have hPM : P ≤ M := inf_le_right.trans h.maximal.1.2
  have hquad := h.delta_quadratic hH he hA
  have hBq := actor_quadratic (D := B) h.prepared.normalized hVU inf_le_left hquad
  have hPq := actor_quadratic (D := P) h.prepared.normalized hVU inf_le_left hquad
  have hBi : IsElementaryTwo (actor M V B h.prepared.normalized) :=
    ⟨actor_nontrivial _ hBM hmove,actor_elementary _ hBM⟩
  have hPi : IsElementaryTwo (actor M V P h.prepared.normalized) :=
    ⟨actor_nontrivial _ hPM (fun hc => hmove (hBP.trans hc)),actor_elementary _ hPM⟩
  have hBc : (centralizer (V : Set G)).relIndex B=2 := by
    rw [←actor_card_index h.prepared.normalized hBM]
    exact (Cyclic.quadratic_fixed_eq_moved h _ hBi hBq).1
  have hPc : (centralizer (V : Set G)).relIndex P=2 := by
    rw [←actor_card_index h.prepared.normalized hPM]
    exact (Cyclic.quadratic_fixed_eq_moved h _ hPi hPq).1
  have hVC : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G)=4 := by
    rw [hfix,Cyclic.ambient_fixed_eq_commutator h hBM hBi hBq]
    exact (h.quadratic_actor_plane ha hBT hmove hBq).2.1
  have hCA : (centralizer (V : Set G)).relIndex A=4 := by
    have hh := relIndex_inf_mul_relIndex (centralizer (V : Set G)) (T : Subgroup G) A
    rw [inf_comm (T : Subgroup G) A,hPc,hidx] at hh
    have hi : (centralizer (V : Set G) ⊓ (T : Subgroup G)).relIndex A =
        (centralizer (V : Set G)).relIndex A := by
      rw [←inf_relIndex_right _ A,←inf_relIndex_right (centralizer (V : Set G)) A]
      congr 1
      ext x
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,hCT ⟨hx.2,hx.1⟩⟩,hx.2⟩⟩
    rw [hi] at hh
    exact hh.symm
  have hCV : C ≤ centralizer (V : Set G) := inf_le_right
  have hDe : IsElementaryAbelian 2 D := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp hCV)
  have hDH : D ≤ H := sup_le (inf_le_left.trans hA.1.1) hVH
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes C V
    ((le_centralizer_iff.mp hCV).trans (Subgroup.centralizer_le_normalizer _))
  have hI : Nat.card (C ⊓ V : Subgroup G) ≤ 4 := by
    rw [←hVC]
    apply Nat.card_le_card_of_injective _ (inclusion_injective (show C ⊓ V ≤
      V ⊓ centralizer (A : Set G) from le_inf inf_le_right
        ((inf_le_left.trans inf_le_left).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))))
  have hAc : Nat.card C * 4 = Nat.card A := by
    simpa only [hCA,inf_comm] using card_inf_index (centralizer (V : Set G)) A
  have hsize : Nat.card A ≤ Nat.card D := by
    rw [h.card_eq_sixteen] at hprod
    have hh := Nat.mul_le_mul_right (Nat.card D) hI
    change Nat.card C * 16 = Nat.card (C ⊓ V : Subgroup G) * Nat.card D at hprod
    nlinarith
  have hDm : D ∈ elementaryAbelianMaxSubgroups H :=
    ⟨hDH,hDe,fun E hEH hEe => (hA.1.2.2 E hEH hEe).trans hsize⟩
  have hBC : Nat.card (C ⊓ twoCoreIn H : Subgroup G) * 2 = Nat.card B := by
    have hh := card_inf_index (centralizer (V : Set G)) B
    rw [hBc] at hh
    have hi : centralizer (V : Set G) ⊓ B = C ⊓ twoCoreIn H := by
      dsimp [B,C]; ac_rfl
    rwa [hi] at hh
  have hAB : Nat.card B * 4 = Nat.card A := by
    rw [image_card_index hA.1.1] at hfour
    simpa only [hfour,inf_comm] using card_inf_index (twoCoreIn H) A
  have hCimage : Nat.card (offenderImage H C)=2 := by
    rw [image_card_index (inf_le_left.trans hA.1.1)]
    have hh := card_inf_index (twoCoreIn H) C
    rw [inf_comm (twoCoreIn H) C] at hh
    have hp : 0 < Nat.card (C ⊓ twoCoreIn H : Subgroup G) := Nat.card_pos
    nlinarith
  have hDCimage : offenderImage H D = offenderImage H C := by
    apply le_antisymm
    · apply (offenderImage_le_iff hDH (inf_le_left.trans hA.1.1)).mpr
      exact sup_le le_sup_left (hVQ.trans le_sup_right)
    · exact (offenderImage_le_iff (inf_le_left.trans hA.1.1) hDH).mpr
        (le_sup_left.trans le_sup_left)
  exact ⟨hDm,(by rw [hDCimage]; exact hCimage),
    (offenderImage_le_iff hDH hA.1.1).mpr (sup_le
      (inf_le_left.trans le_sup_left) (hVQ.trans le_sup_right))⟩

end CFSG.Quasithin.Chapter15.Section02


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath
private instance : DecidableEq Actor := fun x y =>
  decidable_of_iff (x.left=y.left ∧ x.right=y.right) RegularWreathProduct.ext_iff.symm
private abbrev model := wreathTwoDihedralHom
private def baseFour : Subgroup Actor := model.range ⊓ base
private def mover : Actor := coordinate 1 ⟨!![0,1;1,1],by decide⟩

private theorem baseFour_card : Nat.card baseFour=4 := by
  let F := {x : DihedralGroup 4 // (model x).right=1}
  let f : F → baseFour := fun x => ⟨model x,⟨x,rfl⟩,x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (wreathTwoDihedralHom_injective (congrArg Subtype.val h))
    · rintro ⟨x,⟨y,rfl⟩,hy⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_eq_fintype_card]
  decide +kernel

private theorem moved_baseFour_inf_card :
    Nat.card ((baseFour.map (MulAut.conj mover).toMonoidHom) ⊓ model.range : Subgroup Actor)=2 := by
  let F := {x : DihedralGroup 4 // (model x).right=1 ∧
    ∃ y : DihedralGroup 4, model y=mover*model x*mover⁻¹}
  let f : F → ((baseFour.map (MulAut.conj mover).toMonoidHom) ⊓ model.range : Subgroup Actor) :=
    fun x => ⟨mover*model x*mover⁻¹,
      ⟨model x,⟨⟨x,rfl⟩,x.property.1⟩,rfl⟩,x.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply wreathTwoDihedralHom_injective
      exact (MulAut.conj mover).injective (congrArg Subtype.val h)
    · rintro ⟨x,⟨u,⟨⟨a,rfl⟩,ha⟩,rfl⟩,hx⟩
      exact ⟨⟨a,ha,hx⟩,rfl⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_eq_fintype_card]
  decide +kernel

/-- A four-subgroup of the paired base has a conjugate meeting any specified
Sylow two-subgroup in order two. -/
theorem four_base_conjugate_half_sylow (E : Subgroup Actor) (hp : IsPGroup 2 E)
    (hb : E ≤ base) (hc : Nat.card E=4) (S : Sylow 2 Actor) :
    ∃ g : Actor, Nat.card (E.map (MulAut.conj g).toMonoidHom ⊓ (S : Subgroup Actor) : Subgroup Actor)=2 := by
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq Actor P wreathTwoSylow
  have haP : (P : Subgroup Actor).map (MulAut.conj a).toMonoidHom=model.range := by
    rw [←wreathTwoSylow_coe]
    exact congrArg (fun Q : Sylow 2 Actor => (Q : Subgroup Actor)) ha
  have haE : E.map (MulAut.conj a).toMonoidHom=baseFour := by
    apply eq_of_le_of_card_ge
    · refine le_inf (haP ▸ map_mono hP) ?_
      rintro x ⟨y,hy,rfl⟩
      have hh : y.right=1 := hb hy
      change (a*y*a⁻¹).right=1
      simp [hh]
    · rw [baseFour_card,←Nat.card_congr (E.equivMapOfInjective
        (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).toEquiv,hc]
  obtain ⟨b,hbS⟩ := MulAction.exists_smul_eq Actor wreathTwoSylow S
  have hbP : model.range.map (MulAut.conj b).toMonoidHom=(S : Subgroup Actor) := by
    rw [←wreathTwoSylow_coe]
    exact congrArg (fun Q : Sylow 2 Actor => (Q : Subgroup Actor)) hbS
  refine ⟨b*mover*a,?_⟩
  have heq : E.map (MulAut.conj (b*mover*a)).toMonoidHom =
      (baseFour.map (MulAut.conj mover).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
    rw [←haE]
    change E.conjBy (b*mover*a) = ((E.conjBy a).conjBy mover).conjBy b
    rw [conjBy_conjBy,conjBy_conjBy,mul_assoc]
  rw [heq,←hbP,←Subgroup.map_inf _ _ _ (MulAut.conj b).injective]
  rw [←Nat.card_congr (((baseFour.map (MulAut.conj mover).toMonoidHom) ⊓ model.range).equivMapOfInjective
    _ (MulAut.conj b).injective).toEquiv]
  exact moved_baseFour_inf_card
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath

namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath
variable {D : Type*} [Group D] [Finite D]

/-- The conjugate is selected in the original group; the kernel condition
transports the relative Sylow index without any assertion about element orders. -/
theorem four_image_conjugate_half_sylow (q : D →* Actor) (hq : Function.Surjective q)
    (S : Sylow 2 D) (hk : q.ker ≤ (S : Subgroup D))
    (A : Subgroup D) (hp : IsPGroup 2 A)
    (hb : A.map q ≤ base) (hc : Nat.card (A.map q)=4) :
    ∃ g : D, (S : Subgroup D).relIndex (A.map (MulAut.conj g).toMonoidHom)=2 := by
  let P := S.mapSurjective hq
  obtain ⟨y,hy⟩ := four_base_conjugate_half_sylow (A.map q) (hp.map q) hb hc P
  obtain ⟨g,rfl⟩ := hq y
  let E := (A.map q).map (MulAut.conj (q g)).toMonoidHom
  have hEc : Nat.card E=4 := by
    rw [←Nat.card_congr ((A.map q).equivMapOfInjective _ (MulAut.conj (q g)).injective).toEquiv,hc]
  have hidx : (P : Subgroup Actor).relIndex E=2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup Actor)
      ((P : Subgroup Actor) ⊓ E) E bot_le inf_le_right
    simp only [relIndex_bot_left,inf_relIndex_right] at hh
    rw [inf_comm,hy,hEc] at hh
    omega
  have hm : (A.map (MulAut.conj g).toMonoidHom).map q=E := by
    dsimp only [E]
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change q (g*x*g⁻¹)=q g*q x*(q g)⁻¹
    rw [map_mul,map_mul,map_inv]
  have hP : (P : Subgroup Actor).comap q=(S : Subgroup D) := by
    change ((S : Subgroup D).map q).comap q=_
    rw [comap_map_eq,sup_eq_left.mpr hk]
  refine ⟨g,?_⟩
  rw [←hP,relIndex_comap,hm,hidx]
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath


namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Stellmacher Representation Representation.BinaryOffender
open NoncentralChiefRefinement Theory.GroupTheory SmallActionsSource
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Original quotient-image minimality excludes the four-image: the replacement
uses V itself, retains maximum elementary order, and has a proper nontrivial image. -/
theorem ChosenSmallSource.delta_image_card_two
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A∈delta H) : Nat.card (offenderImage H A)=2 := by
  rcases h.delta_image_card_two_or_four hunique hH he hA with htwo | hfour
  · exact htwo
  exfalso
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hi,hj,c,d,hc,hd,hb⟩ := h.two_chief_coordinates_with_common_base hunique hH he s
  let A₀ := A.subgroupOf H
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1.1
  have hAm : A₀ ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  have hAb : A₀.map c.actor ≤ ChiefWreath.base := by
    apply map_le_iff_le_comap.mpr
    rw [←c.factor_sup_eq_base,h.chief_marked_base hunique hH he s i hi c]
    exact le_sup_of_le_left (le_sSup hAm)
  have hAc : Nat.card (A₀.map c.actor)=4 := by
    rw [←Subgroup.relIndex_ker,hc]
    change Nat.card ((A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))=4 at hfour
    rwa [←Subgroup.relIndex_ker,QuotientGroup.ker_mk'] at hfour
  let S := T.subtype hH.1.1.2
  obtain ⟨g,hg⟩ := ChiefWreath.four_image_conjugate_half_sylow c.actor c.surjective S
    (hc.symm ▸ pCore_isPGroup.le_sylow_of_normal S) A₀
    (IsElementaryAbelian.isPGroup 2 A₀) hAb hAc
  let A' := A.map (MulAut.conj (g : G)).toMonoidHom
  have hA' : A'∈delta H := delta_conjugate hA g.property
  have hsub : A'.subgroupOf H = A₀.map (MulAut.conj g).toMonoidHom := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hA'.1.1,map_map,
      show H.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp H.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hA.1.1]
  have hidx : (T : Subgroup G).relIndex A'=2 := by
    rw [←relIndex_subgroupOf hA'.1.1,hsub]
    exact hg
  have hfour' : Nat.card (offenderImage H A')=4 := by
    rw [offenderImage,hsub,←Subgroup.relIndex_ker,QuotientGroup.ker_mk']
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (pCore 2 H) A₀ (MulAut.conj g).injective
    have hQ : (pCore 2 H).map (MulAut.conj g).toMonoidHom=pCore 2 H :=
      Subgroup.Normal.map_conj_eq (pCore 2 H) g
    rw [hQ] at hh
    rw [hh]
    rwa [←Subgroup.relIndex_ker,hc] at hAc
  obtain ⟨hD,hDc,hDA⟩ := h.delta_four_local_lift ha hH he hA' hfour' hidx
  let D := (A' ⊓ centralizer (V : Set G)) ⊔ V
  have hDn : ¬ D ≤ twoCoreIn H := by
    intro hh
    have hOne : Nat.card (offenderImage H D)=1 :=
      (image_card_index hD.1).trans (relIndex_eq_one.mpr hh)
    have hTwo : Nat.card (offenderImage H D)=2 := hDc
    exact (by decide : (2 : ℕ) ≠ 1) (hTwo.symm.trans hOne)
  have hEq := le_antisymm hDA (hA'.2.2 D hD hDn hDA)
  have hh := congrArg (fun E : Subgroup (H ⧸ pCore 2 H) => Nat.card E) hEq
  rw [hDc,hfour'] at hh
  contradiction

end CFSG.Quasithin.Chapter15.Section02
