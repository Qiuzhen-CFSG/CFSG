module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.Nonfusion
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HS
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
/-!
# The original HS overcomponent in its four-group extension

Let X be the actual ordinary component of G_i and R = ⟨t,i⟩ the source
four-group, Sylow in C_G(t) ∩ C_G(K) ∩ C_G(i). Work in L = X R. The marked
action of t and centralization by i make X normal in L, and L/X is a
two-group. The component centralizes O₂(L), so C_{O₂(L)}(t) lies in the
threefold centralizer. R normalizes this fixed subgroup; Sylow maximality
therefore puts it in R.

The actual HS central quotient has larger order than K ≅ A₆. The preceding
source nonfusion theorem consequently excludes t ∼ ti. Transporting the
literal marked quotient action to the component in L now discharges every
intrinsic premise of the HS covering-group argument, proving Z(X) = 1.
No normalizer assumption on the larger C_S(i) is required.

Source: Aschbacher--Smith, 2.5.19, printed pp.561--562. The original
four-group identity and its Sylow property belong to the preceding core
geometry and remain explicit source inputs.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
open ComponentRefinement ComponentSelection
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
variable {G : Type*} [Group G] [Finite G]
variable {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
/-- Sylow maximality absorbs the two-core fixed by t into the source four. -/
private theorem fixed_core_le_four_of_sylow
    {G : Type*} [Group G] [Finite G]
    (K X R L : Subgroup G) (hXL : X ≤ L)
    [(X.subgroupOf L).Normal] [IsQuasisimple (X.subgroupOf L)]
    (hKX : K ≤ X) (t i : G) (htL : t ∈ L)
    (hRL : R ≤ L) (hRt : R ≤ centralizer ({t} : Set G))
    (hLi : L ≤ centralizer ({i} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 R
      (centralizer ({t} : Set G) ⊓ centralizer (K : Set G) ⊓
        centralizer ({i} : Set G))) :
    ((pCore 2 L ⊓ centralizer ({(⟨t, htL⟩ : L)} : Set L)).map L.subtype) ≤ R := by
  let Q := pCore 2 L ⊓ centralizer ({(⟨t, htL⟩ : L)} : Set L)
  let A := Q.map L.subtype
  let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
  have hcomp : IsComponent L (X.subgroupOf L) :=
    ⟨(inferInstance : (X.subgroupOf L).Normal).isSubnormal, inferInstance⟩
  have hQX : pCore 2 L ≤ centralizer (X.subgroupOf L : Set L) :=
    le_centralizer_iff.mp (hcomp.le_centralizer_of_solvable_normal (pCore 2 L))
  have hAD : A ≤ centralizer ({t} : Set G) ⊓ centralizer (K : Set G) ⊓
      centralizer ({i} : Set G) := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨⟨?_, ?_⟩, hLi x.property⟩
    · apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx.2)
    · apply mem_centralizer_iff.mpr
      intro k hk
      exact congrArg Subtype.val
        (hQX hx.1 (⟨k, hXL (hKX hk)⟩ : L) (hKX hk))
  have hRt' : R.subgroupOf L ≤ centralizer ({(⟨t, htL⟩ : L)} : Set L) := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hRt hr)
  have hRN : R.subgroupOf L ≤ normalizer (Q : Set L) :=
    (le_inf le_normalizer_of_normal
      (hRt'.trans (centralizer ({(⟨t, htL⟩ : L)} : Set L)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hRAN : R ≤ normalizer (A : Set G) := by
    rw [← map_subgroupOf_eq_of_le hRL]
    exact (map_mono hRN).trans (Q.le_normalizer_map L.subtype)
  have hAp : IsPGroup 2 A := (pCore_isPGroup.to_le inf_le_left).map L.subtype
  obtain ⟨hRp, hRD, hmax⟩ := Chapter1.isSylowIn_iff.mp hSylow
  have hjoin : R ⊔ A = R := hmax (R ⊔ A)
    (hRp.to_sup_of_normal_right' hAp hRAN) le_sup_left (sup_le hRD hAD)
  exact hjoin ▸ le_sup_right

/-- Transfer the marked HS terminal to an equivalent component carrier. -/
private theorem center_eq_bot_of_equiv_fixed_core_bound
    {A L : Type*} [Group A] [Finite A] [Group L] [Finite L]
    [IsQuasisimple A] (X : Subgroup L) [X.Normal]
    (f : A ≃* X) (e : (A ⧸ center A) ≃* Sporadic.LeechRelated.HS.Carrier)
    (a : MulAut A) (t i : L) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hiZ : i ∈ center L)
    (hact : ∀ x : A, (f (a x) : L) = t * (f x : L) * t⁻¹)
    (hmark : MulAut.congr e (quotientAut (center A) a) =
      MulAut.conj ClassCoverage.t)
    (hq : IsPGroup 2 (L ⧸ X))
    (hbound : pCore 2 L ⊓ centralizer ({t} : Set L) ≤ zpowers t ⊔ zpowers i)
    (hnonfusion : ¬ IsConj t (t * i)) : center A = ⊥ := by
  let : IsQuasisimple X := IsQuasisimple.of_mulEquiv f
  have hcenter : (center A).map f.toMonoidHom = center X := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr f ⟨x, hx⟩).property
    · intro x hx
      exact ⟨f.symm x, (centerCongr f).symm ⟨x, hx⟩ |>.property,
        f.apply_symm_apply x⟩
  let q : (A ⧸ center A) ≃* (X ⧸ center X) :=
    QuotientGroup.congr (center A) (center X) f hcenter
  let e' : (X ⧸ center X) ≃* Sporadic.LeechRelated.HS.Carrier := q.symm.trans e
  let a' : MulAut X := MulAut.congr f a
  have hqmap (x : A) : q (QuotientGroup.mk' (center A) x) =
      QuotientGroup.mk' (center X) (f x) := rfl
  have hemap (x : A) : e' (QuotientGroup.mk' (center X) (f x)) =
      e (QuotientGroup.mk' (center A) x) := by
    change e (q.symm (QuotientGroup.mk' (center X) (f x))) = _
    rw [← hqmap, q.symm_apply_apply]
  have htransport : MulAut.centralQuotientAction e' a' =
      MulAut.centralQuotientAction e a := by
    apply MulEquiv.ext
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center A) z
    calc
      MulAut.centralQuotientAction e' a' (e (QuotientGroup.mk' (center A) x)) =
          MulAut.centralQuotientAction e' a'
            (e' (QuotientGroup.mk' (center X) (f x))) := by rw [hemap]
      _ = e' (QuotientGroup.mk' (center X) (a' (f x))) :=
        MulAut.centralQuotientAction_apply e' a' (f x)
      _ = e' (QuotientGroup.mk' (center X) (f (a x))) := by
        simp only [a', MulAut.congr_apply, MulEquiv.trans_apply, f.symm_apply_apply]
      _ = e (QuotientGroup.mk' (center A) (a x)) := hemap (a x)
      _ = MulAut.centralQuotientAction e a (e (QuotientGroup.mk' (center A) x)) :=
        (MulAut.centralQuotientAction_apply e a x).symm
  have hact' (x : X) : (a' x : L) = t * (x : L) * t⁻¹ := by
    obtain ⟨y, rfl⟩ := f.surjective x
    simpa only [a', MulAut.congr_apply, MulEquiv.trans_apply, f.symm_apply_apply] using hact y
  have hmark' : MulAut.congr e' (quotientAut (center X) a') =
      MulAut.conj ClassCoverage.t := htransport.trans hmark
  have hbot : center X = ⊥ := HS.center_eq_bot_of_fixed_core_bound
    X e' a' t i ht hi hiZ hact' hmark' hq hbound hnonfusion
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  have hfx : f x ∈ center X := (centerCongr f ⟨x, hx⟩).property
  rw [hbot, mem_bot] at hfx
  exact f.injective (by simpa only [map_one] using hfx)

/-- The actual nonfull A₆ source configuration discharges the fixed-core and
nonfusion inputs of the HS covering-group argument. -/
theorem source_hs_center_eq_bot
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : orderOf i = 2)
    (hiC : i ∈ (S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G))
    (hiZ : i ∉ centerIn ((S : Subgroup H).map H.subtype))
    (hR : ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G) = zpowers t ⊔ zpowers i)
    (hSylow : Chapter1.IsSylowIn 2 (zpowers t ⊔ zpowers i)
      (centralizer ({t} : Set G) ⊓ centralizer (K : Set G) ⊓ centralizer ({i} : Set G)))
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (hKX : K ≤ X.map (centralizer ({i} : Set G)).subtype)
    (e : (X ⧸ center X) ≃* Sporadic.LeechRelated.HS.Carrier)
    (a : MulAut X)
    (hact : ∀ x : X, ((a x : centralizer ({i} : Set G)) : G) =
      t * ((x : centralizer ({i} : Set G)) : G) * t⁻¹)
    (hmark : MulAut.congr e (quotientAut (center X) a) =
      MulAut.conj ClassCoverage.t) : center X = ⊥ := by
  let Gi := centralizer ({i} : Set G)
  let XA := X.map Gi.subtype
  let R := zpowers t ⊔ zpowers i
  let L := XA ⊔ R
  let XL := XA.subgroupOf L
  have hXL : XA ≤ L := le_sup_left
  have hRL : R ≤ L := le_sup_right
  have hXi : XA ≤ Gi := map_subtype_le X
  have htR : t ∈ R := mem_sup_left (mem_zpowers t)
  have hiR : i ∈ R := mem_sup_right (mem_zpowers i)
  have htL : t ∈ L := hRL htR
  have hiL : i ∈ L := hRL hiR
  let tL : L := ⟨t, htL⟩
  let iL : L := ⟨i, hiL⟩
  have htNX : t ∈ normalizer (XA : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨a ⟨y, hy⟩, (a ⟨y, hy⟩).property, hact ⟨y, hy⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      let u : X := a.symm ⟨x, hx⟩
      refine ⟨(u : Gi), mem_map_of_mem Gi.subtype u.property, ?_⟩
      exact (hact u).symm.trans
        (congrArg (fun v : X => ((v : Gi) : G)) (a.apply_symm_apply ⟨x, hx⟩))
  have hiXC : i ∈ centralizer (XA : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hXi hx)
  have hLN : L ≤ normalizer (XA : Set G) :=
    sup_le XA.le_normalizer (sup_le (zpowers_le.mpr htNX)
      (zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hiXC)))
  let : XL.Normal := normal_subgroupOf_of_le_normalizer hLN
  let : IsQuasisimple X := hX.2
  let f : X ≃* XL := (X.equivMapOfInjective Gi.subtype Gi.subtype_injective).trans
    (subgroupOfEquivOfLe hXL).symm
  let : IsQuasisimple XL := IsQuasisimple.of_mulEquiv f
  have hRt : R ≤ centralizer ({t} : Set G) := by
    apply sup_le
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (htZ.2 i hiC.1))
  have hLi : L ≤ centralizer ({i} : Set G) := by
    apply sup_le hXi
    exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (htZ.2 i hiC.1).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hiLZ : iL ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hLi x.property))
  have hRp : IsPGroup 2 R := (Chapter1.isSylowIn_iff.mp hSylow).1
  have hq : IsPGroup 2 (L ⧸ XL) := by
    apply isPGroup_quotient_of_sup_eq_top XL (R.subgroupOf L) hRp.comap_subtype
    rw [← subgroupOf_sup hXL hRL]
    exact subgroupOf_self L
  have hfixed : (pCore 2 L ⊓ centralizer ({tL} : Set L)).map L.subtype ≤ R :=
    fixed_core_le_four_of_sylow K XA R L hXL hKX t i htL hRL hRt hLi hSylow
  have hbound : pCore 2 L ⊓ centralizer ({tL} : Set L) ≤ zpowers tL ⊔ zpowers iL := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subtype_apply,
      R, tL, iL] using hfixed
  have hnot : ¬ Nonempty (X ≃* K) := by
    rintro ⟨u⟩
    have hsmall : Nat.card X = 360 := (Nat.card_congr (u.trans eK).toEquiv).trans
      AlternatingSix.ShadowLocal.card_A6
    have hlarge : Nat.card (X ⧸ center X) = 44352000 :=
      (Nat.card_congr e.toEquiv).trans Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier
    have hle := Nat.card_le_card_of_surjective (QuotientGroup.mk' (center X))
      (QuotientGroup.mk'_surjective (center X))
    omega
  have hnonfusion := (source_nonfusion_product_of_nonisomorphic_local_component
    c hG hempty hgen hb hstar t i ht htC htZ hi hiC hiZ hR X hX hnot).2
  have hnonfusionL : ¬ IsConj tL (tL * iL) := by
    intro hh
    obtain ⟨g, hg⟩ := isConj_iff.mp hh
    exact hnonfusion (isConj_iff.mpr ⟨(g : G), congrArg Subtype.val hg⟩)
  apply center_eq_bot_of_equiv_fixed_core_bound XL f e a tL iL
    ((orderOf_coe tL).symm.trans ht) ((orderOf_coe iL).symm.trans hi)
    hiLZ ?_ hmark hq hbound hnonfusionL
  intro x
  apply Subtype.ext
  exact hact x

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
