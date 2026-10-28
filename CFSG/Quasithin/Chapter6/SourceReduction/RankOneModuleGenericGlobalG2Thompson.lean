module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Generation
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.RootCentralizer

/-!
# Thompson counts for the actual G₂ completion

The source centralizer bounds put the marked long and short centralizers
in the normalizers of the two original factors. Since S=T lies in each
factor, Sylow conjugacy inside its normalizer puts every involution there
in the factor itself. Thus every pair counted by either Thompson fiber
lies in the corresponding original parabolic.

Both actual parabolic maps preserve and reflect the two ambient involution
classes. Injectivity preserves the order of the product and its half-order
power, so the fiber maps are bijections with the native G₂ fibers. This
identifies both counts without recognizing the ambient group. Thompson's
formula then expresses its order through the native counts and the two
full ambient centralizer orders. Comparing each centralizer with its
parabolic intersection gives |G| ≤ m |G₂(F)|, where m is the larger of
the two original parabolic indices in their respective normalizers.

The index bound needed to force a twelve-cycle remains an ambient source
obligation. Exhaustive amalgam comparison and original uniqueness also
remain with the generic-global assembly. The Chapter 12 companion applies
the result to the literal chosen-module hypotheses at every n>1, including
field four. Native root geometry retains LICENSES/ATLAS.txt attribution.
Source: Aschbacher–Smith F.4.43–44, printed p.296, and 5.3.3–4,
printed p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open TwoInvolutionClassOrder
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Order

private theorem conj_order {X : Type*} [Group X] {x y : X}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

private theorem halfOrder_injective {X Q : Type*} [Group X] [Group Q]
    (f : Q →* X) (hf : Function.Injective f) (a b : Q) :
    halfOrder (f a) (f b) = f (halfOrder a b) := by
  simp only [halfOrder_def,←map_mul,orderOf_injective f hf,map_pow]

private abbrev LocalFiber {X Q : Type*} [Group X] [Group Q]
    (f : Q →* X) (z v u : Q) :=
  {p : Q × Q // orderOf p.1=2 ∧ orderOf p.2=2 ∧
    IsConj (f z) (f p.1) ∧ IsConj (f v) (f p.2) ∧ halfOrder p.1 p.2=u}

private def localFiberMap {X Q : Type*} [Group X] [Group Q]
    (f : Q →* X) (hf : Function.Injective f) (z v u : Q) :
    LocalFiber f z v u → Fiber (f z) (f v) (f u) := fun p =>
  ⟨(f p.val.1,f p.val.2),p.property.2.2.1,p.property.2.2.2.1,
    (halfOrder_injective f hf _ _).trans (congrArg f p.property.2.2.2.2)⟩

private theorem localFiberMap_bijective {X Q : Type*} [Group X] [Finite X] [Group Q]
    (f : Q →* X) (hf : Function.Injective f) (z v u : Q)
    (hz : orderOf z=2) (hv : orderOf v=2) (hn : ¬ IsConj (f z) (f v))
    (hC : ∀ a : X, orderOf a=2 → a∈centralizer ({f u} : Set X) → a∈f.range) :
    Function.Bijective (localFiberMap f hf z v u) := by
  constructor
  · intro p q he
    apply Subtype.ext
    exact Prod.ext (hf (congrArg (fun t => t.val.1) he))
      (hf (congrArg (fun t => t.val.2) he))
  · intro p
    have hz' : orderOf (f z)=2 := (orderOf_injective f hf z).trans hz
    have hv' : orderOf (f v)=2 := (orderOf_injective f hf v).trans hv
    have ha : orderOf p.val.1=2 := (conj_order p.property.1).symm.trans hz'
    have hb : orderOf p.val.2=2 := (conj_order p.property.2.1).symm.trans hv'
    have hm := fiber_mem_centralizer hz' hv' hn p
    obtain ⟨a,hea⟩ := hC p.val.1 ha hm.1
    obtain ⟨b,heb⟩ := hC p.val.2 hb hm.2
    refine ⟨⟨(a,b),?_,?_,?_,?_,?_⟩,?_⟩
    · exact (orderOf_injective f hf a).symm.trans (hea ▸ ha)
    · exact (orderOf_injective f hf b).symm.trans (heb ▸ hb)
    · exact hea ▸ p.property.1
    · exact heb ▸ p.property.2.1
    · apply hf
      rw [←halfOrder_injective f hf,hea,heb]
      exact p.property.2.2
    · exact Subtype.ext (Prod.ext hea heb)

private theorem kappa_transport {X Y Q : Type*}
    [Group X] [Finite X] [Group Y] [Finite Y] [Group Q]
    (f : Q →* X) (hf : Function.Injective f)
    (g : Q →* Y) (hg : Function.Injective g) (z v u : Q)
    (hz : orderOf z=2) (hv : orderOf v=2)
    (hnf : ¬ IsConj (f z) (f v)) (hng : ¬ IsConj (g z) (g v))
    (hX : ∀ a : X, orderOf a=2 → a∈centralizer ({f u} : Set X) → a∈f.range)
    (hY : ∀ a : Y, orderOf a=2 → a∈centralizer ({g u} : Set Y) → a∈g.range)
    (hfusion : ∀ a : Q, orderOf a=2 →
      (IsConj (f z) (f a) ↔ IsConj (g z) (g a)) ∧
      (IsConj (f v) (f a) ↔ IsConj (g v) (g a))) :
    kappa (f z) (f v) (f u) = kappa (g z) (g v) (g u) := by
  have he : LocalFiber f z v u ≃ LocalFiber g z v u :=
    Equiv.subtypeEquivRight (by
      intro p
      constructor
      · rintro ⟨ha,hb,hza,hvb,hu⟩
        exact ⟨ha,hb,(hfusion p.1 ha).1.mp hza,(hfusion p.2 hb).2.mp hvb,hu⟩
      · rintro ⟨ha,hb,hza,hvb,hu⟩
        exact ⟨ha,hb,(hfusion p.1 ha).1.mpr hza,(hfusion p.2 hb).2.mpr hvb,hu⟩)
  have hc := Nat.card_congr
    ((Equiv.ofBijective _ (localFiberMap_bijective f hf z v u hz hv hnf hX)).symm.trans
      (he.trans (Equiv.ofBijective _ (localFiberMap_bijective g hg z v u hz hv hng hY))))
  simpa only [kappa_def,Fiber,halfOrder_def] using hc

private theorem involution_mem_factor {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (K : Subgroup G) (hTK : (T : Subgroup G) ≤ K)
    (x : G) (hxN : x∈normalizer (K : Set G)) (hx2 : orderOf x=2) : x∈K := by
  let N := normalizer (K : Set G)
  let a : N := ⟨x,hxN⟩
  let U := T.subtype (hTK.trans K.le_normalizer)
  have ha2 : orderOf a=2 := (Subgroup.orderOf_coe a).symm.trans hx2
  obtain ⟨b,hb⟩ := U.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ha2)
  obtain ⟨g,hg⟩ := isConj_iff.mp hb
  have hbK : (b.val : G)∈K := hTK b.property
  have he : g.val*x*g.val⁻¹=(b.val : G) := congrArg Subtype.val hg
  exact (mem_normalizer_iff.mp g.property x).mpr (he ▸ hbK)

private theorem centralizer_card_bound {X Q : Type*}
    [Group X] [Finite X] [Group Q] (f : Q →* X) (hf : Function.Injective f)
    (u : Q) (N : Subgroup X) (hC : centralizer ({f u} : Set X) ≤ N) :
    Nat.card (centralizer ({f u} : Set X)) ≤
      Nat.card (centralizer ({u} : Set Q)) * f.range.relIndex N := by
  have he : (centralizer ({u} : Set Q)).map f =
      f.range ⊓ centralizer ({f u} : Set X) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨⟨a,rfl⟩,mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ha)
    · rintro ⟨⟨a,rfl⟩,ha⟩
      refine ⟨a,mem_centralizer_singleton_iff.mpr (hf ?_),rfl⟩
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp ha
  have hc := relIndex_mul_relIndex (⊥ : Subgroup X)
    (f.range ⊓ centralizer ({f u} : Set X)) (centralizer ({f u} : Set X)) bot_le inf_le_right
  simp only [relIndex_bot_left,inf_relIndex_right] at hc
  rw [←he,card_map_of_injective hf] at hc
  rw [←hc]
  exact Nat.mul_le_mul_left _ (relIndex_le_of_le_right hC index_ne_zero_of_finite)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Order

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open G2Order
variable {G : Type*} [Group G] [Finite G]

/-- The two mixed-pair counts in Thompson's formula are exactly those of
the native G₂ model. The resulting order is at most the native order times
the larger original parabolic index in its normalizer. The original
centralizer bounds and S=T place both involutions of each fiber in the
corresponding original factor, without a geometric smallness assumption. -/
theorem Preparation.g2_thompson_counts
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let z : G := (e.right.symm (G2CompletionFusion.long (1:F))).val
      let v : G := (e.right.symm (G2CompletionFusion.short (1:F))).val
      kappa z v z = kappa (rootA (1:F)) (rootC (1:F)) (rootA (1:F)) ∧
      kappa z v v = kappa (rootA (1:F)) (rootC (1:F)) (rootC (1:F)) ∧
      Nat.card G =
        kappa (rootA (1:F)) (rootC (1:F)) (rootA (1:F)) *
          Nat.card (centralizer ({v} : Set G)) +
        kappa (rootA (1:F)) (rootC (1:F)) (rootC (1:F)) *
          Nat.card (centralizer ({z} : Set G)) ∧
      Nat.card G ≤
        max ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).relIndex
          (normalizer (L : Set G)))
          ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).relIndex
            (normalizer (residual H : Set G))) * Nat.card (Model F) := by
  have hST := d.g2_sourceS_eq_sylow h hH hp F he
  obtain ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,hclasses,_,hfixed⟩ :=
    d.g2_short_fixed_coset_classes h hH hp F he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic₂ (F := F) →* G := Q.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have hl : Function.Injective l := Q.subtype_injective.comp e.left.symm.injective
  have ha (x : Model F) (hx : x∈parabolic₁) (hy : x∈parabolic₂) :
      f ⟨x,hx⟩=l ⟨x,hy⟩ := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨x,hx,hy⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  have hz' : f (G2CompletionFusion.long 1)=z.val := hz.symm
  have hv' : f (G2CompletionFusion.short 1)=v.val := hv.symm
  have hzl : l G2ShortAction.long=z.val := (ha _ _ _).symm.trans hz'
  have hvl : l G2ShortAction.short=v.val := (ha _ _ _).symm.trans hv'
  have hzG : orderOf z.val=2 := (Subgroup.orderOf_coe z).trans hz2
  have hvG : orderOf v.val=2 := (Subgroup.orderOf_coe v).trans hv2
  have hnf : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)) := by
    rwa [hz',hv']
  have hnl : ¬ IsConj (l G2ShortAction.long) (l G2ShortAction.short) := by
    rwa [hzl,hvl]
  have hnm : ¬ IsConj (rootA (1:F)) (rootC (1:F)) := by
    rintro hh
    obtain ⟨g,hg⟩ := isConj_iff.mp hh
    exact EvenInvolutionGeometry.PureLong.rootC_not_long one_ne_zero ⟨1,one_ne_zero,g,hg.symm⟩
  have hzf : orderOf (G2CompletionFusion.long (1:F))=2 := by
    rw [←orderOf_injective f hf,hz']; exact hzG
  have hvf : orderOf (G2CompletionFusion.short (1:F))=2 := by
    rw [←orderOf_injective f hf,hv']; exact hvG
  have hzl2 : orderOf (G2ShortAction.long (F := F))=2 := by
    rw [←orderOf_injective l hl,hzl]; exact hzG
  have hvl2 : orderOf (G2ShortAction.short (F := F))=2 := by
    rw [←orderOf_injective l hl,hvl]; exact hvG
  have hflu := G2LocalFusion.compatible_parabolic_fusion f l ha hnf
  have hTK : (T : Subgroup G)≤residual H := by
    rw [←hST]
    exact (d.g2_local_structure h hH.1.1.2 hp F he).2.2.2.2 1
  have hTL : (T : Subgroup G)≤L := by
    rw [←hST]
    exact (d.g2_local_structure h hH.1.1.2 hp F he).2.2.2.2 0
  have hCz : centralizer ({z.val} : Set G) ≤ normalizer (residual H : Set G) :=
    d.g2_central_involution_centralizers h hH hp F he 1 z.val hzK hzG
  have hCv : centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) := by
    rw [←hvl]
    exact (hfixed hST).2
  have hfr : f.range=P := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.right.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hlr : l.range=Q := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.left.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hkz := kappa_transport f hf (parabolic₁ (F := F)).subtype Subtype.val_injective
    (G2CompletionFusion.long 1) (G2CompletionFusion.short 1) (G2CompletionFusion.long 1)
    hzf hvf hnf hnm (by
      intro a ha2 hac
      rw [hfr]
      exact (show residual H≤P from le_sup_left.trans le_sup_left)
        (involution_mem_factor T (residual H) hTK a (hCz (hz' ▸ hac)) ha2))
    (by
      intro a _ hac
      rw [range_subtype]
      exact (le_sup_left.trans_eq local₁_sup_borel)
        ((centralizer_rootA_eq_local₁ one_ne_zero).le hac))
    (fun a ha2 => ⟨hflu.1 _ _ hzf ha2,hflu.1 _ _ hvf ha2⟩)
  have hkv := kappa_transport l hl (parabolic₂ (F := F)).subtype Subtype.val_injective
    G2ShortAction.long G2ShortAction.short G2ShortAction.short hzl2 hvl2 hnl hnm
    (by
      intro a ha2 hac
      rw [hlr]
      exact (show L≤Q from le_sup_left.trans le_sup_left)
        (involution_mem_factor T L hTL a (hCv (hvl ▸ hac)) ha2))
    (by
      intro a _ hac
      rw [range_subtype]
      exact Atlas.G2.ShortRootProducts.CentralizerCore.centralizer_rootC_le_parabolic
        1 one_ne_zero hac)
    (fun a ha2 => ⟨hflu.2.1 _ _ hzl2 ha2,hflu.2.1 _ _ hvl2 ha2⟩)
  change kappa (f _) (f _) (f _) = kappa (rootA (1:F)) (rootC (1:F)) (rootA (1:F)) at hkz
  rw [hz',hv'] at hkz
  change kappa (l _) (l _) (l _) = kappa (rootA (1:F)) (rootC (1:F)) (rootC (1:F)) at hkv
  rw [hzl,hvl] at hkv
  have hc (x : G) (hx : orderOf x=2) : IsConj z.val x ∨ IsConj v.val x := by
    obtain ⟨a,ha⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
    let a' : (L⊔residual H : Subgroup G) := ⟨a.val,hTK.trans le_sup_right a.property⟩
    have ha2 : orderOf a'=2 := (Subgroup.orderOf_coe a').symm.trans
      ((conj_order ha).symm.trans hx)
    have haS : a'.val∈sourceS L H := hST ▸ a.property
    rcases hclasses a' haS ha2 with hh | hh
    · exact Or.inl (((L⊔residual H : Subgroup G).subtype.map_isConj hh).trans ha.symm)
    · exact Or.inr (((L⊔residual H : Subgroup G).subtype.map_isConj hh).trans ha.symm)
  have hcard := TwoInvolutionClassOrder.card_eq z.val v.val hzG hvG hn hc
  rw [hkz,hkv] at hcard
  have hmz : orderOf (rootA (1:F))=2 :=
    (Subgroup.orderOf_coe (G2CompletionFusion.long (1:F))).trans hzf
  have hmv : orderOf (rootC (1:F))=2 :=
    (Subgroup.orderOf_coe (G2CompletionFusion.short (1:F))).trans hvf
  have hmc (x : Model F) (hx : orderOf x=2) :
      IsConj (rootA (1:F)) x ∨ IsConj (rootC (1:F)) x := by
    obtain ⟨a,ha⟩ := (Atlas.G2.LieParabolicSetup.sylow (F := F)).exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa using hx)
    let b : parabolic₁ (F := F) :=
      ⟨a.val,(le_sup_left.trans borel_le_parabolic₁) a.property⟩
    have hb2 : orderOf b=2 := (Subgroup.orderOf_coe b).symm.trans
      ((conj_order ha).symm.trans hx)
    have hbpow : b^2=1 := hb2 ▸ pow_orderOf_eq_one b
    have hbne : b≠1 := by intro heq; simp [heq] at hb2
    rcases G2CompletionFusion.compatible_involution_classes
        (parabolic₁ (F := F)).subtype (parabolic₂ (F := F)).subtype (fun _ _ _ => rfl)
        b a.property hbpow hbne with hh | hh
    · exact Or.inl (hh.trans ha.symm)
    · exact Or.inr (hh.trans ha.symm)
  have hmcard := TwoInvolutionClassOrder.card_eq (rootA (1:F)) (rootC (1:F))
    hmz hmv hnm hmc
  have hCmz : centralizer ({rootA (1:F)} : Set (Model F)) ≤ parabolic₁ :=
    (centralizer_rootA_eq_local₁ one_ne_zero).le.trans (le_sup_left.trans_eq local₁_sup_borel)
  have hCmv := Atlas.G2.ShortRootProducts.CentralizerCore.centralizer_rootC_le_parabolic
    (1:F) one_ne_zero
  have hcz := centralizer_card_bound f hf (G2CompletionFusion.long 1)
    (normalizer (residual H : Set G)) (hz'.symm ▸ hCz)
  have hcv := centralizer_card_bound l hl G2ShortAction.short
    (normalizer (L : Set G)) (hvl.symm ▸ hCv)
  rw [hz',hfr,Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv
    (parabolic₁ (F := F)) (G2CompletionFusion.long 1) hCmz)] at hcz
  rw [hvl,hlr,Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv
    (parabolic₂ (F := F)) G2ShortAction.short hCmv)] at hcv
  let m := max (Q.relIndex (normalizer (L : Set G)))
    (P.relIndex (normalizer (residual H : Set G)))
  have hzbound : Nat.card (centralizer ({z.val} : Set G)) ≤
      Nat.card (centralizer ({rootA (1:F)} : Set (Model F))) * m :=
    hcz.trans (Nat.mul_le_mul_left _ (le_max_right _ _))
  have hvbound : Nat.card (centralizer ({v.val} : Set G)) ≤
      Nat.card (centralizer ({rootC (1:F)} : Set (Model F))) * m :=
    hcv.trans (Nat.mul_le_mul_left _ (le_max_left _ _))
  have hbound : Nat.card G ≤ m * Nat.card (Model F) := by
    rw [hcard,hmcard]
    calc
      _ ≤ kappa (rootA (1:F)) (rootC (1:F)) (rootA (1:F)) *
            (Nat.card (centralizer ({rootC (1:F)} : Set (Model F))) * m) +
          kappa (rootA (1:F)) (rootC (1:F)) (rootC (1:F)) *
            (Nat.card (centralizer ({rootA (1:F)} : Set (Model F))) * m) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hvbound) (Nat.mul_le_mul_left _ hzbound)
      _ = _ := by ring
  refine ⟨e,?_⟩
  dsimp only
  rw [←hz,←hv]
  exact ⟨hkz,hkv,hcard,hbound⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
