module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer
public import Theory.SpecificGroups.PSL3Four.CentralCover.SylowCenter
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The second elementary plane in the original four-cover Sylow

A specified elementary subgroup of order64 containing the central four is
one of the two full root-plane preimages in a containing Sylow. The other
preimage is constructed on the same carrier. Together they generate that
Sylow, intersect in its full center of order16, and contain every elementary
subgroup of it. No automorphism or ambient conjugacy comparison is assumed.

Source: Aschbacher--Smith I.2.2(3b), used in the original12.7.7 Sylow comparison.
-/

namespace Matrix.PSL3Four
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open ElementaryParabolic
variable {E : Type*} [Group E] [Finite E]

private theorem preimage_card {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (f : A →* B) (hf : Function.Surjective f) (H : Subgroup B) :
    Nat.card (H.comap f)=Nat.card H * Nat.card f.ker := by
  rw [card_eq_card_quotient_mul_card_subgroup (f.ker.subgroupOf (H.comap f)),
    card_quotient_subgroupOf_comap_eq f hf H,
    Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap f H)).toEquiv]

private theorem planes_on_cover {R : Type*} [Group R] [Finite R]
    (q : R →* U F) (hq : Function.Surjective q) (hk : Nat.card q.ker=4)
    [IsElementaryAbelian 2 ((V₁ F).comap q)]
    [IsElementaryAbelian 2 ((V₂ F).comap q)]
    (A : Subgroup R) [IsElementaryAbelian 2 A] (hAc : Nat.card A=64) :
    ∃ W : Subgroup R, IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ W≠A ∧
      A⊔W=⊤ ∧ A⊓W=center R ∧ Nat.card (center R)=16 ∧
      (∀ X : Subgroup R, IsElementaryAbelian 2 X → X≤A ∨ X≤W) ∧ A.Normal ∧ W.Normal := by
  let P := (V₁ F).comap q
  let Q := (V₂ F).comap q
  have hPc : Nat.card P=64 := by rw [preimage_card q hq,card_V₁,card_F,hk]; decide
  have hQc : Nat.card Q=64 := by rw [preimage_card q hq,card_V₂,card_F,hk]; decide
  have hgen : P⊔Q=⊤ := by
    change (V₁ F).comap q⊔(V₂ F).comap q=⊤
    rw [Subgroup.comap_sup_eq q _ _ hq,planes_generate,comap_top]
  have hcenter : P⊓Q=center R := by
    rw [TwoPlaneCover.center_eq_comap q hq (V₁ F) (V₂ F) planes_generate center_le_planes]
    rw [←comap_inf,root_planes_inter,Z_eq_center]
  have hZc : Nat.card (center R)=16 := by
    rw [←hcenter,←comap_inf,root_planes_inter,preimage_card q hq,card_Z,card_F,hk]
  have hne : P≠Q := by
    intro he
    have h : V₁ F=V₂ F := by
      have hh := congrArg (Subgroup.map q) he
      simpa only [P,Q,map_comap_eq_self_of_surjective hq] using hh
    exact plane₁_not_le_plane₂ F h.le
  have hbound (X : Subgroup R) (hX : IsElementaryAbelian 2 X) : X≤P ∨ X≤Q := by
    let := hX
    let : IsElementaryAbelian 2 (X.map q) := IsElementaryAbelian.map _
    exact (elementary_le_plane F (X.map q)).imp
      (fun h => map_le_iff_le_comap.mp h) (fun h => map_le_iff_le_comap.mp h)
  have hclass := TwoPlaneCover.class_two q hq (V₁ F) (V₂ F)
    planes_generate center_le_planes class_two
  have hPn : P.Normal := Normal.of_commutator_le R
    (hclass.trans (hcenter.symm ▸ inf_le_left))
  have hQn : Q.Normal := Normal.of_commutator_le R
    (hclass.trans (hcenter.symm ▸ inf_le_right))
  rcases hbound A inferInstance with hA | hA
  · have he : A=P := eq_of_le_of_card_ge hA (by rw [hAc,hPc])
    subst A
    exact ⟨Q,inferInstance,hQc,Ne.symm hne,hgen,hcenter,hZc,hbound,hPn,hQn⟩
  · have he : A=Q := eq_of_le_of_card_ge hA (by rw [hAc,hQc])
    subst A
    refine ⟨P,inferInstance,hPc,hne,?_,?_,hZc,?_,hQn,hPn⟩
    · rwa [sup_comm]
    · rwa [inf_comm]
    · intro X hX
      exact (hbound X hX).symm

/-- The actual central four-cover has a containing Sylow and its second
full elementary64 plane, with the exact common center and elementary coverage. -/
public theorem four_cover_two_planes
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker=4)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hkQ : f.ker≤Q) (hQc : Nat.card Q=64) :
    ∃ S : Sylow 2 E, ∃ W : Subgroup E,
      Q≤(S : Subgroup E) ∧ W≤(S : Subgroup E) ∧
      Nat.card S=256 ∧ IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ W≠Q ∧
      Q⊔W=(S : Subgroup E) ∧ Q⊓W=(center S).map (S : Subgroup E).subtype ∧
      Nat.card (center S)=16 ∧
      (∀ A : Subgroup E, IsElementaryAbelian 2 A → A≤(S : Subgroup E) → A≤Q ∨ A≤W) ∧
      (S : Subgroup E) ≤ normalizer (Q : Set E) ⊓ normalizer (W : Set E) := by
  obtain ⟨S,hQS⟩ := (IsElementaryAbelian.isPGroup 2 Q).exists_le_sylow
  let SP := S.mapSurjective (f := f) hf
  let SP₀ := unipotentSylow F (n := 2) (by decide) (by simpa using card_F)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL SP SP₀
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have himage : (S : Subgroup E).map f'=unipotent F := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup E).map f).map (MulAut.conj g).toMonoidHom=unipotent F at hh
    simpa only [Subgroup.map_map] using hh
  have hkS : f'.ker≤(S : Subgroup E) := hker ▸ hkQ.trans hQS
  have hS : (S : Subgroup E)=(unipotent F).comap f' := by
    rw [←himage,comap_map_eq_self hkS]
  let q : S →* U F := (unipotentEquiv F).symm.toMonoidHom.comp
    ((f'.comp (S : Subgroup E).subtype).codRestrict (unipotent F) (fun x => by
      rw [←himage]; exact mem_map_of_mem f' x.property))
  have he (x : S) : projective F (q x)=f' x := by
    exact congrArg (unipotent F).subtype ((unipotentEquiv F).apply_symm_apply
      ⟨f' x,by rw [←himage]; exact mem_map_of_mem f' x.property⟩)
  have hq : Function.Surjective q := by
    intro u
    have hu : projective F u∈(S : Subgroup E).map f' := by
      rw [himage,←projective_range]; exact ⟨u,rfl⟩
    obtain ⟨x,hx,hxu⟩ := hu
    refine ⟨⟨x,hx⟩,?_⟩
    apply projective_injective F
    exact (he ⟨x,hx⟩).trans hxu
  have hqker : q.ker=f'.ker.subgroupOf (S : Subgroup E) := by
    ext x
    change q x=1 ↔ f' x=1
    rw [←he,←map_one (projective F),(projective_injective F).eq_iff]
  have hqk : Nat.card q.ker=4 := by
    rw [hqker,Nat.card_congr (subgroupOfEquivOfLe hkS).toEquiv,hker,hk]
  have hSc : Nat.card S=256 := by
    rw [hS,preimage_card f' hf',card_unipotent,card_F,hker,hk]
    decide
  have hplanes (A : Subgroup (U F)) [IsElementaryAbelian 2 A] :
      IsElementaryAbelian 2 (A.comap q) := by
    let V := A.map (projective F)
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
    let := elementary_comap f' hf' (hker ▸ hc)
      (fun z hz => elemPow_eq_one_of_isElementaryAbelian z (hkQ (hker ▸ hz))) V
    let j : A.comap q →* V.comap f' :=
      ((S : Subgroup E).subtype.comp (A.comap q).subtype).codRestrict _
        (fun x => ⟨q x,x.property,he x⟩)
    exact IsElementaryAbelian.of_injective j (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun t : V.comap f' => (t:E)) h)))
  let := hplanes (V₁ F)
  let := hplanes (V₂ F)
  let A := Q.subgroupOf (S : Subgroup E)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hQS
  obtain ⟨W,hWe,hWc,hne,hgen,hcenter,hZc,hbound,hAn,hWn⟩ :=
    planes_on_cover q hq hqk A (by rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv,hQc])
  let W' := W.map (S : Subgroup E).subtype
  let := hWe
  refine ⟨S,W',hQS,map_subtype_le _,hSc,IsElementaryAbelian.map _,?_,?_,?_,?_,hZc,?_,?_⟩
  · exact (card_map_of_injective (S : Subgroup E).subtype_injective).trans hWc
  · intro heq
    apply hne
    apply Subgroup.map_injective (S : Subgroup E).subtype_injective
    change W.map (S : Subgroup E).subtype = (Q.subgroupOf (S : Subgroup E)).map (S : Subgroup E).subtype
    rw [map_subgroupOf_eq_of_le hQS]
    exact heq
  · have hh := congrArg (Subgroup.map (S : Subgroup E).subtype) hgen
    simpa only [A,Subgroup.map_sup,map_subgroupOf_eq_of_le hQS,←MonoidHom.range_eq_map,range_subtype] using hh
  · have hh := congrArg (Subgroup.map (S : Subgroup E).subtype) hcenter
    simpa only [A,Subgroup.map_inf _ _ _ (S : Subgroup E).subtype_injective,map_subgroupOf_eq_of_le hQS] using hh
  · intro X hX hXS
    let := hX
    let : IsElementaryAbelian 2 (X.subgroupOf (S : Subgroup E)) := IsElementaryAbelian.subgroupOf hXS
    rcases hbound (X.subgroupOf (S : Subgroup E)) inferInstance with h | h
    · left
      intro x hx
      exact h (show (⟨x,hXS hx⟩ : S)∈X.subgroupOf (S : Subgroup E) from hx)
    · right
      intro x hx
      exact ⟨⟨x,hXS hx⟩,h hx,rfl⟩

  · have hAn' : (Q.subgroupOf (S : Subgroup E)).Normal := hAn
    have hWn' : (W'.subgroupOf (S : Subgroup E)).Normal := by
      have he : W'.subgroupOf (S : Subgroup E)=W := by
        change (W.map (S : Subgroup E).subtype).comap (S : Subgroup E).subtype=W
        exact comap_map_eq_self_of_injective (S : Subgroup E).subtype_injective W
      exact he.symm ▸ hWn
    exact le_inf ((normal_subgroupOf_iff_le_normalizer hQS).mp hAn')
      ((normal_subgroupOf_iff_le_normalizer (map_subtype_le W)).mp hWn')

end Matrix.PSL3Four
