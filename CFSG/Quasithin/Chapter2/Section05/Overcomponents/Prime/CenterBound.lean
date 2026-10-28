module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HSLocalSetup
/-! The actual source four-group bound and nonfusion bound every central
two-cover by the bad involution. Source 2.5.19, printed pp.561–562. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
open ComponentRefinement ComponentSelection
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


/-- The actual covering center lies in the line of the bad involution. -/
theorem source_center_le_bad_involution
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
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
    (hZp : IsPGroup 2 (center X))
    (hnot : ¬ Nonempty (X ≃* K))
    (a : MulAut X) (ha : orderOf a = 2)
    (hact : ∀ x : X, ((a x : centralizer ({i} : Set G)) : G) =
      t * ((x : centralizer ({i} : Set G)) : G) * t⁻¹)
    : (center X).map ((centralizer ({i} : Set G)).subtype.comp X.subtype) ≤ zpowers i := by
  classical
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
  have hnonfusion := (source_nonfusion_product_of_nonisomorphic_local_component
    c hG hempty hgen hb hstar t i ht htC htZ hi hiC hiZ hR X hX hnot).2
  have hnonfusionL : ¬ IsConj tL (tL * iL) := by
    intro hh
    obtain ⟨g, hg⟩ := isConj_iff.mp hh
    exact hnonfusion (isConj_iff.mpr ⟨(g : G), congrArg Subtype.val hg⟩)
  let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
  have htQ : tL ∉ pCore 2 L := by
    intro htQ
    have hXQ := (show IsComponent L XL from
      ⟨(inferInstance : XL.Normal).isSubnormal,inferInstance⟩).le_centralizer_of_solvable_normal (pCore 2 L)
    have ha1 : a = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      have hx := hact x
      have hcomm := congrArg (fun y : L => (y : G)) (hXQ (f x).property tL htQ)
      change t * ((x : Gi) : G) = ((x : Gi) : G) * t at hcomm
      change ((a x : Gi) : G) = ((x : Gi) : G)
      rw [hx,hcomm,mul_inv_cancel_right]
    rw [ha1,orderOf_one] at ha
    omega
  have hline : pCore 2 L ⊓ centralizer ({tL} : Set L) = zpowers iL := by
    have hil : zpowers iL ≤ center L := zpowers_le.mpr hiLZ
    let : (zpowers iL).Normal := {
      conj_mem := by
        intro y hy g
        rw [mem_center_iff.mp (hil hy) g,mul_inv_cancel_right]
        exact hy }
    have hip : IsPGroup 2 (zpowers iL) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,←orderOf_coe iL,hi,pow_one])
    have hiQ : zpowers iL ≤ pCore 2 L := le_sSup ⟨inferInstance,hip⟩
    apply le_antisymm
    · intro x hx
      obtain ⟨u,hu,v,hv,rfl⟩ := mem_sup_of_normal_right.mp (hbound hx)
      have huQ : u ∈ pCore 2 L := ((pCore 2 L).mul_mem_cancel_right (hiQ hv)).mp hx.1
      have htL2 : orderOf tL = 2 := (orderOf_coe tL).symm.trans ht
      rw [mem_zpowers_iff_mem_range_orderOf,htL2] at hu
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hu
      have hn2 : n < 2 := Finset.mem_range.mp hn
      have hu1 : u = 1 := by
        interval_cases n
        · simpa only [pow_zero] using he.symm
        · exact (htQ (by simpa only [←he,pow_one] using huQ)).elim
      simpa only [hu1,one_mul] using hv
    · exact le_inf hiQ (fun x hx =>
        mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hil hx) tL).symm)
  have hcore := eq_zpowers_of_fixed_central_involution_of_nonfusion (pCore 2 L)
    pCore_isPGroup tL iL (Subtype.ext (ht ▸ pow_orderOf_eq_one t))
    ((orderOf_coe iL).symm.trans hi) hiLZ hline hnonfusionL
  have hZp' : IsPGroup 2 (center XL) := hZp.of_equiv (centerCongr f)
  have hZZ : (center XL).map XL.subtype ≤ zpowers iL := by
    rw [←hcore]
    exact le_sSup ⟨inferInstance,hZp'.map XL.subtype⟩
  rintro x ⟨q,hq,rfl⟩
  have hfZ : f q ∈ center XL := (centerCongr f ⟨q,hq⟩).property
  have hh := mem_map_of_mem L.subtype (hZZ (mem_map_of_mem XL.subtype hfZ))
  change ((f q : XL) : G) ∈ (zpowers iL).map L.subtype at hh
  rw [MonoidHom.map_zpowers] at hh
  exact hh

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
