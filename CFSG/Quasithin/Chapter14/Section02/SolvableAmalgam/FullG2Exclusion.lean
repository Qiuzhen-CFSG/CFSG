module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.CubicRecognition
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullSignSwap
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullElementaryEight
public import Theory.SpecificGroups.C4SquareSignSwapCentralizerFusion

/-!
# Excluding the full binary G₂ row in source 14.2.22

The compatible amalgam marking transports the actual common Sylow group,
its derived index-two subgroup and the full first parabolic. First-parabolic
fusion preserves that derived subgroup. Its elementary eights are
self-centralizing and are never normalized by the whole first parabolic.

The distinguished involution has centralizer of order 192. These particular
local facts force the elementary-eight normalizer two-cores to have order at
least 32. Centric fusion in the marked Sylow group then preserves its
index-two subgroup, and Thompson transfer contradicts ambient simplicity.
The final application retains the original local module and quotient action.

Source: Aschbacher--Smith, 14.2.21–22, printed pp.988–989. The concrete G₂
root calculations and their attribution are recorded in the imported model
modules. No hypothesis on all two-local normalizers is used.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullG2Exclusion
open Atlas.G2.BinaryParabolicPair
local notation "F" => Atlas.G2.Model (ZMod 2)
variable {G : Type*} [Group G]

/-- Transport the full first parabolic's two elementary-eight facts. -/
theorem elementary_eight_local
    (T : Sylow 2 G) (H : Subgroup G)
    (eH : firstParabolic ≃* H) (eT : commonSylow ≃* T)
    (hc : ∀ t : commonSylow,
      (eH ⟨t,commonSylow_le_first t.property⟩ : G) = (eT t : G))
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hET : E ≤ (T : Subgroup G)) (hcard : Nat.card E = 8)
    (hself : (T : Subgroup G) ⊓ centralizer (E : Set G) ≤ E) :
    H ⊓ centralizer (E : Set G) = E ∧ ¬ H ≤ normalizer (E : Set G) := by
  let j : firstParabolic →* G := H.subtype.comp eH.toMonoidHom
  have hj : Function.Injective j := H.subtype_injective.comp eH.injective
  have hTH : (T : Subgroup G) ≤ H := by
    intro x hx
    have ht := hc (eT.symm ⟨x,hx⟩)
    rw [eT.apply_symm_apply] at ht
    have ht' : (eH ⟨eT.symm ⟨x,hx⟩,
      commonSylow_le_first (eT.symm ⟨x,hx⟩).property⟩ : G) = x := ht
    rw [← ht']
    exact (eH _).property
  let D := E.comap j
  let V := D.map firstParabolic.subtype
  have hV (x : firstParabolic) : (x : F) ∈ V ↔ j x ∈ E := by
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact (Subtype.ext hxy : y = x) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  let k : D →* E := (j.comp D.subtype).codRestrict E (fun x => x.property)
  have hk : Function.Bijective k := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hj (congrArg (fun a : E => (a : G)) h)
    · intro x
      let a := eH.symm ⟨x,hTH (hET x.property)⟩
      have ha : j a = x := congrArg Subtype.val (eH.apply_symm_apply ⟨x,hTH (hET x.property)⟩)
      exact ⟨⟨a,show j a ∈ E from ha.symm ▸ x.property⟩,Subtype.ext ha⟩
  let eD := MulEquiv.ofBijective k hk
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective eD.toMonoidHom eD.injective
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (A := D) firstParabolic.subtype
  have hVcard : Nat.card V = 8 := by
    rw [card_map_of_injective firstParabolic.subtype_injective]
    exact (Nat.card_congr eD.toEquiv).trans hcard
  have hVS : V ≤ (commonSylow : Subgroup F) := by
    rintro x ⟨a,ha,rfl⟩
    let t : T := ⟨j a,hET ha⟩
    let u := eT.symm t
    have he : j ⟨u,commonSylow_le_first u.property⟩ = j a := by
      exact (hc u).trans (congrArg Subtype.val (eT.apply_symm_apply t))
    have hv := congrArg Subtype.val (hj he)
    change (u : F) = (a : F) at hv
    change (a : F) ∈ (commonSylow : Subgroup F)
    rw [← hv]
    exact u.property
  have hVSself : (commonSylow : Subgroup F) ⊓ centralizer (V : Set F) ≤ V := by
    rintro x ⟨hx,hcx⟩
    let a : firstParabolic := ⟨x,commonSylow_le_first hx⟩
    apply (hV a).mpr
    apply hself
    constructor
    · have he : j a = (eT ⟨x,hx⟩ : G) := hc ⟨x,hx⟩
      rw [he]
      exact (eT ⟨x,hx⟩).property
    · intro y hy
      obtain ⟨b,hb⟩ := hk.surjective ⟨y,hy⟩
      have he : j b.val = y := congrArg Subtype.val hb
      rw [← he]
      exact (map_mul j b.val a).symm.trans ((congrArg j (Subtype.ext
        (hcx b.val ⟨b.val,b.property,rfl⟩))).trans (map_mul j a b.val))
  have hmodel := elementary_eight_centralizer_first V hVS hVcard hVSself
  constructor
  · apply le_antisymm
    · rintro x ⟨hx,hcx⟩
      let a := eH.symm ⟨x,hx⟩
      have ha : j a = x := congrArg Subtype.val (eH.apply_symm_apply ⟨x,hx⟩)
      have ham : (a : F) ∈ V := by
        rw [← hmodel]
        refine ⟨a.property,?_⟩
        rintro y ⟨b,hb,rfl⟩
        have hh : b * a = a * b := hj (by
          simp only [map_mul,ha]
          exact hcx (j b) hb)
        exact congrArg (fun t : firstParabolic => (t : F)) hh
      exact ha ▸ (hV a).mp ham
    · intro x hx
      exact ⟨hTH (hET hx),E.le_centralizer hx⟩
  · intro hn
    apply elementary_eight_not_normalized_first V hVS hVcard
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨b,hb,rfl⟩
      let c : firstParabolic := ⟨a,ha⟩
      apply (hV (c*b*c⁻¹)).mpr
      have hh : j c * j b * (j c)⁻¹ ∈ E :=
        (mem_normalizer_iff.mp (hn (eH c).property) (j b)).mp hb
      simpa only [map_mul,map_inv] using hh
    · intro hx
      have hxP : x ∈ firstParabolic := by
        have hh := map_subtype_le D (show a*x*a⁻¹ ∈ V from hx)
        have hc := firstParabolic.mul_mem (firstParabolic.mul_mem (firstParabolic.inv_mem ha) hh) ha
        simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hc
      let b : firstParabolic := ⟨x,hxP⟩
      let c : firstParabolic := ⟨a,ha⟩
      apply (hV b).mpr
      apply (mem_normalizer_iff.mp (show j c ∈ normalizer (E : Set G) from hn (eH c).property) (j b)).mpr
      have hh := (hV (c*b*c⁻¹)).mp hx
      simpa only [map_mul,map_inv] using hh


/-- The marked derived subgroup makes first-parabolic fusion preserve transfer. -/
theorem first_fusion_preserves_transfer
    (T : Sylow 2 G) (H : Subgroup G)
    (eH : firstParabolic ≃* H) (eT : commonSylow ≃* T)
    (hc : ∀ t : commonSylow,
      (eH ⟨t,commonSylow_le_first t.property⟩ : G) = (eT t : G))
    (g : G) (hg : g ∈ H) (x y : T)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) :
    FullSignSwap.equiv (eT.symm x) ∈ C4SquareSignSwap.transfer ↔
      FullSignSwap.equiv (eT.symm y) ∈ C4SquareSignSwap.transfer := by
  have hm (t : commonSylow) : FullSignSwap.equiv t ∈ C4SquareSignSwap.transfer ↔
      (t : F) ∈ commutator F := by
    rw [← FullSignSwap.derived_mark,mem_map_equiv,FullSignSwap.equiv.symm_apply_apply]
    rfl
  rw [hm,hm]
  let j : firstParabolic →* G := H.subtype.comp eH.toMonoidHom
  have hj : Function.Injective j := H.subtype_injective.comp eH.injective
  let a := eH.symm ⟨g,hg⟩
  let u : firstParabolic := ⟨eT.symm x,commonSylow_le_first (eT.symm x).property⟩
  let v : firstParabolic := ⟨eT.symm y,commonSylow_le_first (eT.symm y).property⟩
  have ha : j a = g := congrArg Subtype.val (eH.apply_symm_apply ⟨g,hg⟩)
  have hu : j u = x := (hc (eT.symm x)).trans (congrArg Subtype.val (eT.apply_symm_apply x))
  have hv : j v = y := (hc (eT.symm y)).trans (congrArg Subtype.val (eT.apply_symm_apply y))
  have he : a⁻¹ * u * a = v := hj (by simpa only [map_mul,map_inv,ha,hu,hv] using hxy)
  have heF : (a : F)⁻¹ * (eT.symm x : F) * (a : F) = (eT.symm y : F) :=
    congrArg Subtype.val he
  have hn := mem_normalizer_iff.mp (show (a : F)⁻¹ ∈ normalizer (commutator F : Set F) from by
    rw [Subgroup.normalizer_eq_top]
    trivial) (eT.symm x : F)
  simpa only [inv_inv,heF] using hn

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullG2Exclusion


namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.GreenBook ChapterF.SourceAssembly ChapterF.SourceAssembly.Goldschmidt RankTwoAmalgam
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G]

/-- The full binary G₂ amalgam cannot occur in a finite simple ambient group
with its first parabolic equal to the central-involution centralizer. -/
theorem full_g2_exclusion [IsSimpleGroup G]
    (T : Sylow 2 G) (H X : Subgroup G)
    (hHX : H ⊓ X = (T : Subgroup G))
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hH : H = centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hm : ExceptionalModels.G2.IsFullAmalgam (inclusionAmalgam H X)) : False := by
  obtain ⟨m⟩ := hm
  let f := m.symm
  let eT : commonSylow ≃* T := f.middle.trans (MulEquiv.subgroupCongr hHX)
  have hc : ∀ t : commonSylow,
      (f.left ⟨t,commonSylow_le_first t.property⟩ : G) = (eT t : G) := by
    intro t
    exact congrArg Subtype.val (f.left_commutes t)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (hZ ▸ (by decide : 2 ∣ 2))
  have hzG : orderOf (z : G) = 2 := (orderOf_injective Z.subtype Z.subtype_injective z).trans hz
  obtain ⟨hzT,hzpow,hzC⟩ := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp z.property
  let v : T := ⟨z,hzT⟩
  have hv : v ∈ center T := mem_center_iff.mpr (fun t => Subtype.ext (hzC t t.property))
  have hv2 : orderOf v = 2 := (Subgroup.orderOf_coe v).symm.trans hzG
  have hzgen : zpowers (z : G) = Z := eq_of_le_of_card_ge (zpowers_le.mpr z.property) (by
    rw [Nat.card_zpowers,hzG]
    exact hZ.le)
  have hC : centralizer ({(v : G)} : Set G) = H := by
    calc
      _ = centralizer (zpowers (z : G) : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      _ = H := (congrArg (fun K : Subgroup G => centralizer (K : Set G)) hzgen).trans hH.symm
  apply C4SquareSignSwap.simple_exclusion_of_centralizer192 T
    (eT.symm.trans FullSignSwap.equiv) v hv hv2
  · rw [hC]
    exact (Nat.card_congr f.left.toEquiv).symm.trans card_firstParabolic
  · intro g hg x y hxy
    exact FullG2Exclusion.first_fusion_preserves_transfer T H f.left eT hc g (hC ▸ hg) x y hxy
  · intro E hET hself hEA hcard
    let : IsElementaryAbelian 2 E := hEA
    have he := FullG2Exclusion.elementary_eight_local T H f.left eT hc E hET hcard hself
    have hzE : (v : G) ∈ E := hself ⟨v.property,centralizer_le hET hzC⟩
    have hcent : centralizer (E : Set G) ≤ H := by
      rw [← hC]
      intro a ha b hb
      have hb' : b = (v : G) := Set.mem_singleton_iff.mp hb
      exact hb' ▸ ha v hzE
    exact ⟨le_antisymm (fun x hx => he.1 ▸ (show x ∈ H ⊓ centralizer (E : Set G) from
      ⟨hcent hx,hx⟩)) E.le_centralizer, hC ▸ he.2⟩

/-- The full-G₂ row is excluded in the literal original 14.2.22 context. -/
theorem source_full_g2_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hcard : Nat.card (localModule T M) = 4) (hTM : (T : Subgroup G) ≤ M)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hHX : H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)) = (T : Subgroup G))
    (hH : H = centralizer (centralInvolutions T : Set G))
    (hm : ExceptionalModels.G2.IsFullAmalgam
      (inclusionAmalgam H (sourceResidual M Mc ⊔ (T : Subgroup G)))) : False := by
  let : IsSimpleGroup G := hG.simple
  exact full_g2_exclusion T H _ hHX (plane_centralInvolutions_card T M hTM hcard e) hH hm

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
