module
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoFrameTwelve

/-!
# Marked restoration of the proper Hall–Janko extension

The compatible reduced comparison gives one original outer involution and one
concrete outer-Borel involution inducing the same actions on both endpoints.
The split multiplication maps extend the reduced equivalences across these
involutions. Their restrictions agree on the whole reduced Borel and the common
complement, hence on the entire original Borel. The resulting three equivalences
have both commuting squares and preserve every reduced inclusion.

The concrete permutation extension is then transported to the actual full
automorphism group of the ATLAS J₂ carrier. The unchanged weaker ParabolicModel
predicate is not used to infer compatibility. Both source orientations survive.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.228–231;
Aschbacher–Smith F.1.11–12, printed pp.262–264.
-/

open Subgroup Theory.GroupTheory
attribute [local instance] Classical.propDecidable
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.SplitComparison

private theorem involution_cases {A : Type*} [Group A]
    (x : A) (hx : x^2=1) (hx1 : x≠1) (k : zpowers x) :
    (k:A)=1 ∨ (k:A)=x := by
  classical
  have ho : orderOf x=2 := orderOf_eq_prime hx hx1
  have hf : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hx⟩
  have hm := k.property
  rw [hf.mem_zpowers_iff_mem_range_orderOf,ho] at hm
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn2 := Finset.mem_range.mp hn
  have hn' : n=0 ∨ n=1 := by omega
  rcases hn' with rfl | rfl
  · exact Or.inl (by simpa using he.symm)
  · exact Or.inr (by simpa using he.symm)

private noncomputable def involutionHom {A X : Type*} [Group A] [Group X]
    (x : A) (hx : x^2=1) (hx1 : x≠1) (y : X) (hy : y^2=1) : zpowers x →* X := by
  classical
  refine { toFun := fun k => if (k:A)=1 then 1 else y
           map_one' := by simp
           map_mul' := ?_ }
  intro k l
  have hxx : x*x=1 := by simpa only [pow_two] using hx
  have hyy : y*y=1 := by simpa only [pow_two] using hy
  rcases involution_cases x hx hx1 k with hk | hk <;>
    rcases involution_cases x hx hx1 l with hl | hl <;>
      simp only [coe_mul,hk,hl,one_mul,mul_one,hxx,if_pos,if_neg hx1,hyy]

private theorem involutionHom_apply {A X : Type*} [Group A] [Group X]
    (x : A) (hx : x^2=1) (hx1 : x≠1) (y : X) (hy : y^2=1) (k : zpowers x) :
    involutionHom x hx hx1 y hy k=if (k:A)=1 then 1 else y := by rfl

/-- Extend a marked embedding of the normal subgroup across a split involution.
The target actor and its conjugation action determine the whole embedding. -/
private theorem exists_split_involution_embedding
    {A X : Type*} [Group A] [Group X]
    (N : Subgroup A) [N.Normal] (x : A) (hx : x^2=1) (hxN : x∉N)
    (hc : IsComplement' N (zpowers x))
    (f : N →* X) (hf : Function.Injective f)
    (y : X) (hy : y^2=1) (hyN : y∉f.range)
    (ha : ∀ v : N, f (N.normalizerMonoidHom ⟨x,N.normalizer_eq_top ▸ mem_top x⟩ v)=
      y*f v*y⁻¹) :
    ∃ F : A →* X, Function.Injective F ∧
      (∀ v : N,F v=f v) ∧ F x=y ∧ F.range=f.range ⊔ zpowers y := by
  classical
  have hx1 : x≠1 := fun he => hxN (he ▸ N.one_mem)
  let c := involutionHom x hx hx1 y hy
  let α : zpowers x →* MulAut N := N.normalizerMonoidHom.comp (inclusion (N.normalizer_eq_top ▸ le_top))
  have hact (k : zpowers x) :
      f.comp (α k).toMonoidHom=(MulAut.conj (c k)).toMonoidHom.comp f := by
    apply MonoidHom.ext
    intro v
    rcases involution_cases x hx hx1 k with hk | hk
    · have hk1 : k=1 := Subtype.ext hk
      subst k
      simp only [map_one,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.one_apply]
    · have hcy : c k=y := by
        change involutionHom x hx hx1 y hy k=y
        rw [involutionHom_apply,hk,if_neg hx1]
      change f (α k v)=c k*f v*(c k)⁻¹
      rw [hcy]
      exact (congrArg f (show α k v=N.normalizerMonoidHom
        ⟨x,N.normalizer_eq_top ▸ mem_top x⟩ v from Subtype.ext (by change (k:A)*v*(k:A)⁻¹=x*v*x⁻¹; rw [hk]))).trans (ha v)
  let E := SemidirectProduct.mulEquivSubgroup hc
  let J := SemidirectProduct.lift f c hact
  let F := J.comp E.symm.toMonoidHom
  have hF (v : N) (k : zpowers x) : F ((v:A)*(k:A))=f v*c k := by
    have he : E ⟨v,k⟩=(v:A)*(k:A) := rfl
    change J (E.symm ((v:A)*(k:A)))=_
    rw [←he,E.symm_apply_apply]
    rfl
  have hFN (v : N) : F v=f v := by
    have hh := hF v 1
    simpa only [coe_one,mul_one,map_one] using hh
  have hFx : F x=y := by
    have hh := hF 1 ⟨x,mem_zpowers x⟩
    simpa only [coe_one,one_mul,map_one,c,involutionHom_apply,if_neg hx1] using hh
  have hFi : Function.Injective F := by
    apply (MonoidHom.ker_eq_bot_iff F).mp
    apply bot_unique
    intro a ha1
    obtain ⟨w,rfl⟩ := E.surjective a
    rcases w with ⟨v,k⟩
    have ha' : f v*c k=1 := (hF v k).symm.trans ha1
    rcases involution_cases x hx hx1 k with hk | hk
    · have hk1 : k=1 := Subtype.ext hk
      subst k
      rw [map_one,mul_one] at ha'
      have hv : v=1 := hf (ha'.trans (map_one f).symm)
      subst v
      exact mem_bot.mpr (map_one E)
    · have hcy : c k=y := by
        change involutionHom x hx hx1 y hy k=y
        rw [involutionHom_apply,hk,if_neg hx1]
      rw [hcy] at ha'
      exact (hyN ⟨v⁻¹,by
        calc
          f (v⁻¹)=(f v)⁻¹ := map_inv f v
          _=(f v)⁻¹*(f v*y) := by rw [ha',mul_one]
          _=y := inv_mul_cancel_left _ _⟩).elim
  refine ⟨F,hFi,hFN,hFx,le_antisymm ?_ ?_⟩
  · rintro _ ⟨a,rfl⟩
    obtain ⟨w,rfl⟩ := E.surjective a
    rcases w with ⟨v,k⟩
    change F ((v:A)*(k:A))∈_
    rw [hF]
    apply mul_mem_sup (show f v∈f.range from ⟨v,rfl⟩)
    rcases involution_cases x hx hx1 k with hk | hk
    · have hk1 : k=1 := Subtype.ext hk
      rw [hk1,map_one]
      exact one_mem _
    · change involutionHom x hx hx1 y hy k∈_
      rw [involutionHom_apply,hk,if_neg hx1]
      exact mem_zpowers y
  · apply sup_le
    · rintro _ ⟨v,rfl⟩
      exact ⟨v,hFN v⟩
    · exact zpowers_le.mpr ⟨x,hFx⟩


open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open Seed PairNormalizer
open CFSG.Quasithin.ChapterF.GreenBook

private theorem extensionAction_into (y : Extension) (v : Carrier) :
    intoExtension (extensionAction y v)=y*intoExtension v*y⁻¹ := by
  apply extension.subtype_injective
  rfl

private theorem subgroup_split_embedding
    {G : Type*} [Group G]
    (R P : Subgroup G) (hRP : R≤P) [(R.subgroupOf P).Normal]
    (D : Subgroup Carrier) (e : R ≃* D)
    (x : P) (hx : x^2=1) (hxR : (x:G)∉R)
    (hc : IsComplement' (R.subgroupOf P) (zpowers x))
    (y : Extension) (hy : y^2=1) (hyN : y∉intoExtension.range)
    (hxN : (x:G)∈normalizer (R:Set G))
    (ha : ∀ v : R, (e (R.normalizerMonoidHom ⟨(x:G),hxN⟩ v):Carrier)=
      extensionAction y (e v:Carrier)) :
    ∃ F : P →* Extension, Function.Injective F ∧
      (∀ v : R,F (inclusion hRP v)=intoExtension (e v:Carrier)) ∧
      F x=y ∧ F.range=D.map intoExtension ⊔ zpowers y := by
  let d := subgroupOfEquivOfLe hRP
  let f := intoExtension.comp (D.subtype.comp (e.toMonoidHom.comp d.toMonoidHom))
  have hf : Function.Injective f :=
    SecondParabolic.intoExtension_injective.comp (D.subtype_injective.comp (e.injective.comp d.injective))
  have hfR : f.range=D.map intoExtension := by
    apply le_antisymm
    · rintro _ ⟨v,rfl⟩
      exact mem_map_of_mem intoExtension (e (d v)).property
    · rintro _ ⟨v,hv,rfl⟩
      refine ⟨d.symm (e.symm ⟨v,hv⟩),?_⟩
      change intoExtension (e (d (d.symm (e.symm ⟨v,hv⟩))))=intoExtension v
      rw [d.apply_symm_apply,e.apply_symm_apply]
  have ha' (v : R.subgroupOf P) :
      f ((R.subgroupOf P).normalizerMonoidHom
        ⟨x,(R.subgroupOf P).normalizer_eq_top ▸ mem_top x⟩ v)=y*f v*y⁻¹ := by
    change intoExtension (e (d ((R.subgroupOf P).normalizerMonoidHom
      ⟨x,(R.subgroupOf P).normalizer_eq_top ▸ mem_top x⟩ v)))=_
    have he : d ((R.subgroupOf P).normalizerMonoidHom
        ⟨x,(R.subgroupOf P).normalizer_eq_top ▸ mem_top x⟩ v)=
          R.normalizerMonoidHom ⟨(x:G),hxN⟩ (d v) := Subtype.ext rfl
    rw [he,ha,extensionAction_into]
    rfl
  obtain ⟨F,hFi,hFN,hFx,hFr⟩ := exists_split_involution_embedding
    (R.subgroupOf P) x hx hxR hc f hf y hy
    (fun hm => by
      obtain ⟨v,hv⟩ := hm
      exact hyN ⟨(e (d v):Carrier),hv⟩) ha'
  refine ⟨F,hFi,?_,hFx,?_⟩
  · intro v
    exact hFN (d.symm v)
  · rw [hFr,hfR]

private theorem outer_span (D : Subgroup Carrier) (hBD : SecondParabolic.Overlap.B≤D)
    (houter : outerElement∈normalizer (D.map intoExtension:Set Extension))
    (y : SecondParabolic.Overlap.outerB) (hy : y^2=1)
    (hyN : (y:Extension)∉intoExtension.range) :
    D.map intoExtension ⊔ zpowers (y:Extension)=D.map intoExtension ⊔ zpowers outerElement := by
  have hn : SecondParabolic.Overlap.outerB≤normalizer (D.map intoExtension:Set Extension) := by
    apply sup_le
    · exact (map_mono hBD).trans (D.map intoExtension).le_normalizer
    · exact zpowers_le.mpr houter
  have hyD : (y:Extension)∉D.map intoExtension := fun hm => hyN ((map_le_range _ _) hm)
  have hoD : outerElement∉D.map intoExtension :=
    fun hm => SecondParabolic.outerElement_not_mem_range ((map_le_range _ _) hm)
  have hy2 : (y:Extension)^2=1 := congrArg Subtype.val hy
  apply eq_of_le_of_card_ge
  · apply sup_le le_sup_left (zpowers_le.mpr _)
    exact (sup_le_sup_right (map_mono hBD) _) y.property
  · rw [card_sup_zpowers_of_normalizing_involution _ _ hy2 hyD (hn y.property),
      card_sup_zpowers_of_normalizing_involution _ _ SecondParabolic.outerElement_sq hoD houter]


private theorem split_hom_ext {A X : Type*} [Group A] [Group X]
    (N : Subgroup A) (x : A) (hgen : N⊔zpowers x=⊤)
    (f g : A →* X) (hN : ∀ v : N,f v=g v) (hx : f x=g x) : f=g := by
  have he : ⊤≤f.eqLocus g := by
    rw [←hgen]
    exact sup_le (fun v hv => hN ⟨v,hv⟩) (zpowers_le.mpr hx)
  exact MonoidHom.ext (fun v => he (mem_top v))

open CFSG.Quasithin.ChapterF.Source
open SuzukiContainment ProductLift

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original marked amalgam in the proper Hall–Janko branch is the actual
permutation extension. Both inclusion squares and all three reduced restrictions
are constructed from one common outer involution. -/
public theorem original_extension_iso
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S) :
    let e₀ := e.trans catalogueIso.symm
    ∃ E : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S i) (commonBorel L S)
        (parabolic L S j) (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.extensionModel.toMarking.amalgam,
      (∀ b : commonBorel L (reducedSylow L S),
        (E.middle (inclusion (reduced_commonBorel_le h) b):Extension)=
          intoExtension (e₀.middle b:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) i,
        (E.left (inclusion (reduced_parabolic_le h i) v):Extension)=
          intoExtension (e₀.left v:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) j,
        (E.right (inclusion (reduced_parabolic_le h j) v):Extension)=
          intoExtension (e₀.right v:Carrier)) := by
  let e₀ := e.trans catalogueIso.symm
  obtain ⟨x,y,hx,hxN,hy,hyN,hB,hL,hR,hcB,hcP⟩ := original_aligned_action_lift h i j e hne
  let := reduced_borel_normal h
  let := reduced_parabolic_normal h i
  let := reduced_parabolic_normal h j
  have hxp (r : Fin 2) : (inclusion (commonBorel_le_parabolic r) x)^2=1 := by
    rw [←map_pow,hx,map_one]
  have hxn (r : Fin 2) : (x:G)∉parabolic L (reducedSylow L S) r := by
    intro hh
    apply hxN
    rw [←reduced_parabolic_inf_borel h r]
    exact ⟨hh,x.property⟩
  have hy2 : (y:Extension)^2=1 := congrArg Subtype.val hy
  obtain ⟨fB,hBi,hBN,hBx,hBr⟩ := subgroup_split_embedding
    (commonBorel L (reducedSylow L S)) (commonBorel L S) (reduced_commonBorel_le h)
    SecondParabolic.Overlap.B e₀.middle x hx hxN hcB y hy2 hyN
    (borel_normalizes_reduced h x.property) hB
  obtain ⟨fL,hLi,hLN,hLx,hLr⟩ := subgroup_split_embedding
    (parabolic L (reducedSylow L S) i) (parabolic L S i) (reduced_parabolic_le h i)
    l₁ e₀.left (inclusion (commonBorel_le_parabolic i) x) (hxp i) (hxn i) (hcP i)
    y hy2 hyN (parabolic_normalizes_reduced h i (commonBorel_le_parabolic i x.property)) hL
  obtain ⟨fR,hRi,hRN,hRx,hRr⟩ := subgroup_split_embedding
    (parabolic L (reducedSylow L S) j) (parabolic L S j) (reduced_parabolic_le h j)
    p₂ e₀.right (inclusion (commonBorel_le_parabolic j) x) (hxp j) (hxn j) (hcP j)
    y hy2 hyN (parabolic_normalizes_reduced h j (commonBorel_le_parabolic j x.property)) hR
  have hrB : fB.range=HallJanko.extensionModel.toMarking.B := by
    rw [hBr,outer_span _ le_rfl (SecondParabolic.Overlap.outerElement_normalizes_B card_p₂) y hy hyN,
      HallJanko.extensionModel_B]
    rfl
  have hrL : fL.range=HallJanko.extensionModel.toMarking.P 0 := by
    rw [hLr,outer_span _ SecondParabolic.Overlap.B_le_l₁
      SecondParabolic.Overlap.outerElement_normalizes_l₁ y hy hyN,
      HallJanko.extensionModel_P_zero,FirstParabolic.l₁s_eq_sup_outerElement]
    rfl
  have hrR : fR.range=HallJanko.extensionModel.toMarking.P 1 := by
    rw [hRr,outer_span _ SecondParabolic.Overlap.B_le_p₂
      SecondParabolic.Overlap.outerElement_normalizes_p₂ y hy hyN,
      HallJanko.extensionModel_P_one]
  have hleft : fL.comp (inclusion (commonBorel_le_parabolic i))=fB := by
    apply split_hom_ext _ x hcB.sup_eq_top
    · intro b
      let b₀ : commonBorel L (reducedSylow L S) := ⟨(b:G),b.property⟩
      change fL (inclusion (reduced_parabolic_le h i)
        (inclusion (commonBorel_le_parabolic i) b₀))=fB (inclusion (reduced_commonBorel_le h) b₀)
      rw [hLN,hBN]
      exact congrArg (fun a : l₁ => intoExtension (a:Carrier)) (e₀.left_commutes b₀)
    · exact hLx.trans hBx.symm
  have hright : fR.comp (inclusion (commonBorel_le_parabolic j))=fB := by
    apply split_hom_ext _ x hcB.sup_eq_top
    · intro b
      let b₀ : commonBorel L (reducedSylow L S) := ⟨(b:G),b.property⟩
      change fR (inclusion (reduced_parabolic_le h j)
        (inclusion (commonBorel_le_parabolic j) b₀))=fB (inclusion (reduced_commonBorel_le h) b₀)
      rw [hRN,hBN]
      exact congrArg (fun a : p₂ => intoExtension (a:Carrier)) (e₀.right_commutes b₀)
    · exact hRx.trans hBx.symm
  let E : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S i) (commonBorel L S)
        (parabolic L S j) (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.extensionModel.toMarking.amalgam := {
    left := (MonoidHom.ofInjective hLi).trans (MulEquiv.subgroupCongr hrL)
    middle := (MonoidHom.ofInjective hBi).trans (MulEquiv.subgroupCongr hrB)
    right := (MonoidHom.ofInjective hRi).trans (MulEquiv.subgroupCongr hrR)
    left_commutes := fun b => Subtype.ext (congrArg (fun f : commonBorel L S →* Extension => f b) hleft)
    right_commutes := fun b => Subtype.ext (congrArg (fun f : commonBorel L S →* Extension => f b) hright) }
  exact ⟨E,hBN,hLN,hRN⟩


/-- The full Aut(J₂) comparison, including the complete Borel and both endpoint
inclusion squares. On every reduced element it is the prescribed inner map. -/
public theorem original_autJ2_iso
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L (reducedSylow L S) i)
        (commonBorel L (reducedSylow L S)) (parabolic L (reducedSylow L S) j)
        (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : S≠reducedSylow L S) :
    let e₀ := e.trans catalogueIso.symm
    ∃ E : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S i) (commonBorel L S)
        (parabolic L S j) (commonBorel_le_parabolic i) (commonBorel_le_parabolic j))
      HallJanko.autJ2Model.toMarking.amalgam,
      (∀ b : commonBorel L (reducedSylow L S),
        (E.middle (inclusion (reduced_commonBorel_le h) b):MulAut Carrier)=
          MulAut.conj (e₀.middle b:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) i,
        (E.left (inclusion (reduced_parabolic_le h i) v):MulAut Carrier)=
          MulAut.conj (e₀.left v:Carrier)) ∧
      (∀ v : parabolic L (reducedSylow L S) j,
        (E.right (inclusion (reduced_parabolic_le h j) v):MulAut Carrier)=
          MulAut.conj (e₀.right v:Carrier)) := by
  obtain ⟨E,hB,hL,hR⟩ := original_extension_iso h i j e hne
  refine ⟨E.trans HallJanko.extensionAutAmalgamIso,?_,?_,?_⟩
  · intro b
    change extensionEquivAut (E.middle (inclusion (reduced_commonBorel_le h) b):Extension)=_
    rw [hB]
    exact congrArg (fun f : Carrier →* MulAut Carrier => f _) extensionEquivAut_comp_intoExtension
  · intro v
    change extensionEquivAut (E.left (inclusion (reduced_parabolic_le h i) v):Extension)=_
    rw [hL]
    exact congrArg (fun f : Carrier →* MulAut Carrier => f _) extensionEquivAut_comp_intoExtension
  · intro v
    change extensionEquivAut (E.right (inclusion (reduced_parabolic_le h j) v):Extension)=_
    rw [hR]
    exact congrArg (fun f : Carrier →* MulAut Carrier => f _) extensionEquivAut_comp_intoExtension

/-- The Hall–Janko alternative is restored in either orientation. This theorem
requires the genuine compatible reduced comparison and leaves the weaker
`ParabolicModel` interface unchanged. -/
public theorem original_j2_or_autJ2_models
    (h : HypothesisF11 L S)
    (he : Nonempty (RankTwoAmalgam.Iso (reducedAmalgam L S)
        HallJanko.j2Model.toMarking.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso (reducedAmalgam L S).reverse
        HallJanko.j2Model.toMarking.amalgam)) :
    (ExceptionalModels.IsModel .j2 (originalAmalgam L S) ∨
      ExceptionalModels.IsModel .j2 (originalAmalgam L S).reverse) ∨
    (ExceptionalModels.IsModel .autJ2 (originalAmalgam L S) ∨
      ExceptionalModels.IsModel .autJ2 (originalAmalgam L S).reverse) := by
  by_cases hs : S=reducedSylow L S
  · left
    let f := NativeRestoration.originalIsoReduced hs
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨(f.trans e).toParabolicEquiv⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨(f.reverse.trans e).toParabolicEquiv⟩
  · right
    rcases he with he | he
    · obtain ⟨e⟩ := he
      obtain ⟨E,_,_,_⟩ := original_autJ2_iso h 0 1 e hs
      exact Or.inl ⟨E.toParabolicEquiv⟩
    · obtain ⟨e⟩ := he
      obtain ⟨E,_,_,_⟩ := original_autJ2_iso h 1 0 e hs
      exact Or.inr ⟨E.toParabolicEquiv⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.SplitComparison
