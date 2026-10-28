module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialPlacement
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Containment
public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# Movement after the G₂ centralizer conjugations

The full centralizer of the marked short root C(1) lies in the opposite
parabolic. Consequently every two-subgroup of its centralizer inside the
right factor lies in the common Borel's unique Sylow subgroup. Commutation
with C(1) kills the D and F coordinates, giving the bound q⁴.

This bound survives every ambient normalizer of K = O²(H). If the changed
involution were fixed modulo Z(K) under the original S, orbit–stabilizer
would give q⁶ = |S| ≤ |Z(K)| |C_S(v)| ≤ q⁵, a contradiction. Thus movement
in the original S survives the second source conjugation without requiring
S to equal its conjugate, or the original mover to belong to both.

Combining this with the constructed root pair, the two Sylow placements
and the special-core saturation proves nonfusion with the single remaining
placement premise C_T(Z(K)) ≤ S. That premise, the triality movement argument,
original uniqueness, exhaustive compatible comparison and ambient recognition
still require discharge. The Chapter12 companion supplies the actual application.

Source: Aschbacher–Smith F.4.35, printed p.292, and 5.3.3, p.659
(`refs/quasithin.pdf`). The coordinate and centralizer proofs reuse the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace G2Nonfusion
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem centralizer_coordinates (t : Fin 6 → F)
    (hc : Commute (unipotentProduct t) (rootC (1:F))) : t 3=0 ∧ t 5=0 := by
  have he := hc.eq
  have hC : rootC (1:F) = unipotentProduct ![0,0,1,0,0,0] := by simp [unipotentProduct]
  rw [hC,unipotentProduct_mul,unipotentProduct_mul] at he
  have he' := unipotentProduct_injective he
  have h0 := congrFun he' 0
  have h1 := congrFun he' 1
  have h3 : (3:F)=1 := by
    have hh := CharTwo.add_self_eq_zero (1:F)
    linear_combination hh
  have h5 : t 5=0 := by
    simpa [unipotentProductParameters,h3,CharTwo.sub_eq_add] using h1
  refine ⟨?_,h5⟩
  simpa [unipotentProductParameters,h3,h5,CharTwo.sub_eq_add] using h0

private theorem unipotent_centralizer_bound (D : Subgroup (Model F))
    (hDU : D ≤ unipotent)
    (hDC : D ≤ centralizer ({rootC (1:F)} : Set (Model F))) :
    Nat.card D ≤ Nat.card F ^ 4 := by
  let t (x : D) := unipotentParameters x.val
  have ht (x : D) : unipotentProduct (t x)=x.val := by
    have hx := hDU x.property
    rw [unipotent_eq_range] at hx
    obtain ⟨u,hu⟩ := hx
    dsimp [t]
    rw [←hu,unipotentParameters_product]
  have hz (x : D) : t x 3=0 ∧ t x 5=0 :=
    centralizer_coordinates _ ((ht x).symm ▸
      (mem_centralizer_singleton_iff.mp (hDC x.property)))
  let f : D → (Fin 4 → F) := fun x => ![t x 0,t x 1,t x 2,t x 4]
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    rw [←ht x,←ht y]
    congr 1
    ext i
    fin_cases i
    · exact congrFun he 0
    · exact congrFun he 1
    · exact congrFun he 2
    · exact (hz x).1.trans (hz y).1.symm
    · exact congrFun he 3
    · exact (hz x).2.trans (hz y).2.symm
  simpa only [Nat.card_fun,Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- A two-subgroup in the short parabolic fixing C(1) has order at most q⁴. -/
private theorem two_subgroup_centralizer_bound (D : Subgroup (Model F))
    (hD : IsPGroup 2 D) (hDP : D ≤ parabolic₁)
    (hDC : D ≤ centralizer ({rootC (1:F)} : Set (Model F))) :
    Nat.card D ≤ Nat.card F ^ 4 := by
  have hDB : D ≤ Atlas.G2.borel := by
    rw [←ChapterF.GreenBook.LieModels.G2.overlap_eq_borel]
    exact le_inf hDP (hDC.trans
      (ShortRootProducts.CentralizerCore.centralizer_rootC_le_parabolic 1 one_ne_zero))
  let U := (Atlas.G2.LieParabolicSetup.sylow (F := F)).subtype
    (show unipotent ≤ Atlas.G2.borel from le_sup_left)
  let : (U : Subgroup (Atlas.G2.borel (K := F))).Normal := EvenBorelTorus.radical_normal
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  obtain ⟨P,hP⟩ := (hD.comap_subtype : IsPGroup 2 (D.subgroupOf Atlas.G2.borel)).exists_le_sylow
  have hPU : P=U := Subsingleton.elim _ _
  apply unipotent_centralizer_bound D _ hDC
  intro x hx
  have hh := hP (show (⟨x,hDB hx⟩ : Atlas.G2.borel (K := F)) ∈ D.subgroupOf Atlas.G2.borel from hx)
  rw [hPU] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G]

private theorem point_orbit_bound (S Z : Subgroup G) (v : G)
    (hc : ∀ x ∈ S, ⁅x,v⁆ ∈ Z) :
    Nat.card S ≤ Nat.card Z * Nat.card (S ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  let _ : MulAction S G := {
    smul := fun r t => (r : G)*t*(r : G)⁻¹
    one_smul := by intro t; change (1:G)*t*(1:G)⁻¹=t; simp
    mul_smul := by
      intro a b t
      change ((a:G)*(b:G))*t*((a:G)*(b:G))⁻¹ = (a:G)*((b:G)*t*(b:G)⁻¹)*(a:G)⁻¹
      simp [mul_assoc] }
  let C := S ⊓ centralizer ({v} : Set G)
  have hstab : MulAction.stabilizer S v = C.subgroupOf S := by
    ext r
    rw [MulAction.mem_stabilizer_iff]
    change (r:G)*v*(r:G)⁻¹=v ↔ r.val ∈ S ∧ r.val ∈ centralizer ({v} : Set G)
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun hh => ⟨r.property,mem_centralizer_singleton_iff.mpr hh⟩,
      fun hh => mem_centralizer_singleton_iff.mp hh.2⟩
  let f : MulAction.orbit S v → Z := fun t => ⟨t.val*v⁻¹,by
    obtain ⟨r,hr⟩ := t.property
    change (r:G)*v*(r:G)⁻¹=t.val at hr
    rw [←hr]
    exact hc r r.property⟩
  have hf : Function.Injective f := by
    intro a b hh
    exact Subtype.ext (mul_right_cancel (congrArg Subtype.val hh))
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S v)
  rw [Nat.card_prod,hstab,Nat.card_congr (subgroupOfEquivOfLe (show C ≤ S from inf_le_left)).toEquiv] at hh
  rw [←hh]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf)

private theorem factor_center_bound {K : Subgroup G}
    (hc : HasCharacteristicTwo K) (e : K ≃* local₁ (F := F)) :
    Nat.card ((center K).map K.subtype) ≤ Nat.card F := by
  let Q := pCore 2 K
  have hZQ : center K ≤ Q := (center_le_centralizer _).trans hc
  let a : center K → center Q := fun z => ⟨⟨z.val,hZQ z.property⟩,
    mem_center_iff.mpr (fun q => Subtype.ext (mem_center_iff.mp z.property q.val))⟩
  have ha : Function.Injective a := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : center Q => z.val.val) he)
  let b := (pCore 2 K).equivMapOfInjective e.toMonoidHom e.injective
  let b' : pCore 2 K ≃* pCore 2 (local₁ (F := F)) :=
    b.trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  calc
    Nat.card ((center K).map K.subtype) = Nat.card (center K) :=
      (Nat.card_congr ((center K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm
    _ ≤ Nat.card (center Q) := Nat.card_le_card_of_injective a ha
    _ = Nat.card F := by
      rw [Nat.card_congr (centerCongr b').toEquiv,
        local₁_pCore_special.2.2.2.2.2.2]

omit [Finite G] in
/-- The short-root centralizer bound survives every ambient normalizer of K.
The source marking is retained through the actual parabolic equivalence. -/
private theorem conjugate_centralizer_bound {K P S : Subgroup G}
    (hKP : K ≤ P) (hSK : S ≤ K) (hS : IsPGroup 2 S)
    (e : P ≃* parabolic₁ (F := F)) (w : P)
    (hw : (e w).val = rootC (1:F))
    (c : G) (hc : c ∈ normalizer (K : Set G)) :
    Nat.card (S ⊓ centralizer ({c*w.val*c⁻¹} : Set G) : Subgroup G) ≤ Nat.card F^4 := by
  let R := S ⊓ centralizer ({c*w.val*c⁻¹} : Set G)
  let f : R →* P := {
    toFun x := ⟨c⁻¹*x.val*c, hKP (by simpa only [inv_inv] using
      ((mem_normalizer_iff.mp ((normalizer (K : Set G)).inv_mem hc) x.val).mp (hSK x.property.1)))⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intro x y; apply Subtype.ext; change c⁻¹*(x.val*y.val)*c = (c⁻¹*x.val*c)*(c⁻¹*y.val*c); group }
  let a : R →* Model F := (parabolic₁ (F := F)).subtype.comp (e.toMonoidHom.comp f)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change c⁻¹*x.val*c=c⁻¹*y.val*c at hh
    exact mul_left_cancel (mul_right_cancel hh)
  have ha : Function.Injective a := Subtype.val_injective.comp (e.injective.comp hf)
  have hAP : a.range ≤ parabolic₁ := by rintro _ ⟨x,rfl⟩; exact (e (f x)).property
  have hAC : a.range ≤ centralizer ({rootC (1:F)} : Set (Model F)) := by
    rintro _ ⟨x,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←hw]
    change (e (f x)).val*(e w).val=(e w).val*(e (f x)).val
    change ((e (f x)*e w) : parabolic₁ (F := F)).val = (e w*e (f x)).val
    apply congrArg Subtype.val
    rw [←map_mul,←map_mul]
    apply congrArg e
    apply Subtype.ext
    have hh := mem_centralizer_singleton_iff.mp x.property.2
    change x.val*(c*w.val*c⁻¹)=(c*w.val*c⁻¹)*x.val at hh
    change (c⁻¹*x.val*c)*w.val=w.val*(c⁻¹*x.val*c)
    calc
      _ = c⁻¹*(x.val*(c*w.val*c⁻¹))*c := by group
      _ = c⁻¹*((c*w.val*c⁻¹)*x.val)*c := by rw [hh]
      _ = _ := by group
  have hbound := two_subgroup_centralizer_bound a.range ((hS.to_le (show R ≤ S from inf_le_left)).of_surjective a.rangeRestrict a.rangeRestrict_surjective) hAP hAC
  exact (Nat.card_congr (MonoidHom.ofInjective ha).toEquiv).le.trans hbound

/-- Conjugating the marked short involution by a normalizer of K cannot
make its image fixed modulo Z(K) under the original source S. -/
private theorem conjugate_moved {K P S : Subgroup G}
    (hKP : K ≤ P) (hSK : S ≤ K) (hS : IsPGroup 2 S)
    (hcK : HasCharacteristicTwo K) (a : K ≃* local₁ (F := F))
    (hcard : Nat.card S = Nat.card F^6)
    (e : P ≃* parabolic₁ (F := F)) (w : P)
    (hw : (e w).val = rootC (1:F))
    (c : G) (hc : c ∈ normalizer (K : Set G)) :
    ∃ x ∈ S, ⁅x,c*w.val*c⁻¹⁆ ∉ (center K).map K.subtype := by
  by_contra hh
  push Not at hh
  have hb := point_orbit_bound S ((center K).map K.subtype) (c*w.val*c⁻¹) hh
  have hz := factor_center_bound hcK a
  have hcentral := conjugate_centralizer_bound hKP hSK hS e w hw c hc
  have hle := hb.trans (Nat.mul_le_mul hz hcentral)
  rw [hcard,←pow_succ'] at hle
  exact (Nat.pow_lt_pow_right (Finite.one_lt_card (α := F)) (by decide : 5<6)).not_ge hle


omit [Finite G] in
private theorem core_commutator {K : Subgroup G} (e : K ≃* local₁ (F := F)) :
    ⁅K.pCoreIn 2,K.pCoreIn 2⁆ ≤ (center K).map K.subtype := by
  have hi : ⁅pCore 2 K,pCore 2 K⁆ ≤ center K := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_commutator,pCore_map_iso,center_map_equiv]
    rw [←map_subtype_commutator,local₁_pCore_special.2.2.1]
    exact local₁_core_center_le_center
  change ⁅(pCore 2 K).map K.subtype,(pCore 2 K).map K.subtype⁆ ≤ _
  rw [←map_commutator]
  exact map_mono hi

private theorem saturation_fixes_point_mod_center
    {G : Type*} [Group G] {K S : Subgroup G} {v : G}
    (hv : v ∈ K.pCoreIn 2) (hc : ⁅K.pCoreIn 2,K.pCoreIn 2⁆ ≤ (center K).map K.subtype)
    (hn : S ≤ normalizer (K.pCoreIn 2 : Set G))
    (g : G) (hvg : v ∈ ((center K).map K.subtype).map (MulAut.conj g).toMonoidHom)
    (hS : S = K.pCoreIn 2 ⊔ ((K.pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center K).map K.subtype : Subgroup G) : Set G))) :
    ∀ x ∈ S, ⁅x,v⁆ ∈ (center K).map K.subtype := by
  let Q := K.pCoreIn 2
  let R := Q.map (MulAut.conj g).toMonoidHom ⊓
    centralizer (((center K).map K.subtype : Subgroup G) : Set G)
  have hRN : R ≤ normalizer (Q : Set G) := (le_sup_right.trans hS.ge).trans hn
  have hRV : R ≤ centralizer ({v} : Set G) := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    obtain ⟨z,⟨k,hk,rfl⟩,he⟩ := hvg
    apply mem_centralizer_singleton_iff.mpr
    rw [←he,←map_mul,←map_mul]
    exact congrArg (MulAut.conj g).toMonoidHom (congrArg (fun t : K => t.val)
      (mem_center_iff.mp hk ⟨y,map_subtype_le _ hy⟩))
  intro x hx
  have hx' : x ∈ (Q : Set G) * (R : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q R hRN]
    exact hS ▸ hx
  obtain ⟨q,hq,r,hr,rfl⟩ := hx'
  have he : ⁅r,v⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp (hRV hr))
  rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
  exact hc (commutator_mem_commutator hq hv)


private theorem source_sylow_card
    {T : Sylow 2 G} {L H A B K : Subgroup G}
    (d : Preparation T L H A B K) (hS : sourceS L H ≤ K)
    (e : K ≃* local₁ (F := F)) : Nat.card (sourceS L H)=Nat.card F^6 := by
  obtain ⟨U,hU⟩ := (show ∃ U : Sylow 2 K,
    (U : Subgroup K).map K.subtype=sourceS L H ⊓ K from d.sylow 1)
  rw [inf_eq_left.mpr hS] at hU
  let U' := U.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := (Atlas.G2.LieParabolicSetup.sylow (F := F)).subtype sylow_le_local₁
  calc
    Nat.card (sourceS L H) = Nat.card U := by
      rw [←hU,card_map_of_injective K.subtype_injective]
    _ = Nat.card U' := (card_map_of_injective e.injective).symm
    _ = Nat.card P := Nat.card_congr (U'.equiv P).toEquiv
    _ = Nat.card F^6 := by
      change Nat.card ((unipotent (K := F)).subgroupOf local₁) = Nat.card F^6
      rw [Nat.card_congr (subgroupOfEquivOfLe (show unipotent (K := F) ≤ local₁ from sylow_le_local₁)).toEquiv]
      exact card_unipotent

end G2Nonfusion
variable {G : Type*} [Group G] [Finite G]

/-- Movement in the original S is invariant under every ambient normalizer
of the right factor; the marked short root is read through the actual right map. -/
theorem Preparation.g2_short_root_conjugates_moved
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (hw : (e.right w).val=rootC (1:F))
    (c : G) (hc : c ∈ normalizer (residual H : Set G)) :
    ∃ x ∈ sourceS L H,
      ⁅x,c*w.val*c⁻¹⁆ ∉ (center (residual H)).map (residual H).subtype := by
  have hs := d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)
  obtain ⟨a⟩ := hs.2.2.1
  have hSK := hs.2.2.2.2 1
  have hK := d.g2_right_maximal_all h hH hp F (Or.inr ⟨e⟩)
  have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hK.1
  exact G2Nonfusion.conjugate_moved (le_sup_left.trans le_sup_left) hSK
    (pCore_isPGroup.map _) hchar a (G2Nonfusion.source_sylow_card d hSK a)
    e.right w hw c hc

/-- The marked G₂ short root is not fused into Z(K), provided the original
Sylow centralizer C_T(Z(K)) lies in S. Both Sylow placements and movement after
the second conjugation are proved here; neither is an additional premise. -/
theorem Preparation.g2_short_root_not_fused_of_centralizer_le
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
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (hCS : (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val=v ∧ (e.right w).val=rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v=2 ∧ ∀ g : G, v ∉ Z.conjBy g := by
  have hf := d.g2_right_center_fusion h hH hp F he
  have hPhiS := d.g2_source_frattini_le_core h hH.1.1.2 hp F he
  have hs := d.g2_local_structure h hH.1.1.2 hp F he
  obtain ⟨a⟩ := hs.2.2.1
  obtain ⟨e,v,hv,hmark,hvZ,hv2,_,r,s,hUQ,_,hPhiU,hUC,_⟩ :=
    d.g2_special_core_root_pair h hH hp F he
  refine ⟨e,v,hv,hmark,hvZ,hv2,?_⟩
  intro g hvg
  obtain ⟨c,g',hc,hcQ,hcZ,_,hcg,hZQ,hRS,_⟩ :=
    source_special_core_placements hH.1.1.2 hPhiS hf.2.2 hCS _ hUQ hPhiU
      v hv hvZ g hvg (hUC g hvg)
  have hcK : c ∈ normalizer (residual H : Set G) :=
    hf.2.2 ▸ (Subgroup.centralizer_le_normalizer _ hc)
  have hg : g' ∉ normalizer (residual H : Set G) := by
    intro hh
    have hZg := mem_normalizer_iff_map_conj_eq.mp (hf.2.2.symm ▸ hh)
    exact hcZ (hZg ▸ hcg)
  have hsat := (d.g2_special_core_saturation h hH hp F he g' hg hZQ hRS).2
  have hnQ := d.S_normalizes_right.trans (normalizer_le_normalizer_characteristic_image
    (residual H) (pCore 2 (residual H)))
  have hfixed := G2Nonfusion.saturation_fixes_point_mod_center hcQ
    (G2Nonfusion.core_commutator a) hnQ g' hcg hsat
  obtain ⟨w,hwv,hw⟩ := hmark
  obtain ⟨x,hx,hxv⟩ := d.g2_short_root_conjugates_moved h hH hp F e w hw c hcK
  rw [hwv] at hxv
  exact hxv (hfixed x hx)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
