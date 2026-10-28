module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialPlus
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
public import Theory.GroupTheory.PCoreCentralQuotientImage
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.OriginalContext
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.ElementaryEightPlaneOrder24

/-!
# Quaternion-core rigidity in the original cubic amalgam

The characteristic-two centralizer chain identifies the actual two-core of
Mc with the quaternion product in H. A proper Sylow-preserving enlargement
then has order 576. Its conjugation action on the elementary eight is a
point stabilizer of order 24. The source normalizer bound makes this same
action preserve the source plane, contradicting the elementary-eight
plane stabilizer's absence of a nonidentity fixed point.

The final theorem uses the original source context and actual local geometry.
The source plane lies in the eight because the latter is self-centralizing
in T and normalized by X; no separate marking assumption is needed.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialRigidity
variable {D : Type*} [Group D] [Finite D]

/-- The centralizer chain forces equality with the quaternion core. -/
theorem core_eq (Z R : Subgroup D) (d : QuaternionCentralProductData R)
    (hZ : Z ≤ center D) (hZcard : Nat.card Z = 2)
    (hQR : pCore 2 D ≤ R)
    (hc : centralizer (pCore 2 D : Set D) ≤ pCore 2 D) : pCore 2 D = R := by
  have hZQ : Z ≤ pCore 2 D := (hZ.trans (center_le_centralizer _)).trans hc
  have hZR : Z ≤ R := hZQ.trans hQR
  have hZcenter : Z ≤ (center R).map R.subtype := by
    intro z hz
    refine ⟨⟨z,hZR hz⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_center_iff.mp (hZ hz) x)
  have hcenter : (center R).map R.subtype = Z :=
    (eq_of_le_of_card_ge hZcenter (by
      rw [card_map_of_injective R.subtype_injective,d.center_card,hZcard])).symm
  let : Z.Normal := ⟨fun a ha b => by
    simpa only [mem_center_iff.mp (hZ ha) b,mul_inv_cancel_right] using ha⟩
  let q := QuotientGroup.mk' Z
  have hs (x : R.map q) : x ^ 2 = 1 := by
    obtain ⟨r,hr,he⟩ := x.property
    apply Subtype.ext
    change (x : D ⧸ Z) ^ 2 = 1
    rw [← he,← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← hcenter]
    exact ⟨(⟨r,hr⟩ : R)^2,d.square_mem_center _,rfl⟩
  have hi (x : R.map q) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using hs x
  let : IsMulCommutative (R.map q) := ⟨⟨fun x y => by
    calc
      x*y = (x*y)⁻¹ := (hi _).symm
      _ = y*x := by rw [mul_inv_rev,hi,hi]⟩⟩
  exact core_eq_of_abelian_quotient Z (pCore 2 D) R hZQ hQR
    (centralizer_image_pCore_le_of_central_quotient Z hZ hc)

/-- The actual point stabilizer, with intrinsic quaternion factor data. -/
theorem normalizer_stabilizer (Q : Subgroup D) [Q.Normal]
    (d : QuaternionCentralProductData Q)
    (hc : centralizer (Q : Set D) ≤ Q) (hD : Nat.card D = 576)
    (E S : Subgroup D) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hEQ : E ≤ Q)
    (hS : Nat.card S = 64) (hSN : S ≤ normalizer (E : Set D))
    (hcentral : S ⊓ centralizer (E : Set D) = E)
    (z : E) (hz : z ≠ 1) (hzQ : (z : D) ∈ (center Q).map Q.subtype) :
    E.normalizerMonoidHom.range = MulAction.stabilizer (MulAut E) z ∧
      Nat.card E.normalizerMonoidHom.range = 24 := by
  let B := d.left.map Q.subtype
  let C := d.right.map Q.subtype
  have hj : B ⊔ C = Q := by
    rw [← Subgroup.map_sup,d.span]
    ext x
    exact ⟨fun ⟨q,_,he⟩ => he ▸ q.property,fun hx => ⟨⟨x,hx⟩,mem_top _,rfl⟩⟩
  have hB : Nonempty (B ≃* QuaternionGroup 2) :=
    ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans
      d.left_model.some⟩
  have hC : Nonempty (C ≃* QuaternionGroup 2) :=
    ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans
      d.right_model.some⟩
  have hinter : Nat.card (B ⊓ C : Subgroup D) = 2 := by
    rw [← map_inf _ _ Q.subtype Q.subtype_injective,
      card_map_of_injective Q.subtype_injective,d.intersection_card]
  have hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    exact congrArg Subtype.val (d.commute b hb c hc)
  let : (B ⊔ C : Subgroup D).Normal := hj.symm ▸ inferInstance
  have hzBC : (z : D) ∈ (center (B ⊔ C : Subgroup D)).map (B ⊔ C).subtype := by
    obtain ⟨q,hq,hqz⟩ := hzQ
    refine ⟨⟨z,hj.symm ▸ hEQ z.property⟩,mem_center_iff.mpr (fun x => ?_),rfl⟩
    apply Subtype.ext
    have hh := congrArg Subtype.val (mem_center_iff.mp hq (⟨x,hj ▸ x.property⟩ : Q))
    change (x : D) * (q : D) = (q : D) * (x : D) at hh
    change (q : D) = (z : D) at hqz
    rw [hqz] at hh
    exact hh
  obtain ⟨himage,⟨e⟩,_⟩ := ExtraspecialPlus.normalizer_stabilizer_of_order576
    B C E S hB hC hinter hcomm (hj.symm ▸ hc) hD hE (hj.symm ▸ hEQ)
    hS hSN hcentral z hz hzBC
  refine ⟨himage, ?_⟩
  rw [himage,Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
  decide

/-- A quaternion enlargement cannot preserve an elementary-eight plane.
The source normalizer bound supplies precisely this preservation. -/
theorem not_plane_stable (Q : Subgroup D) [Q.Normal]
    (d : QuaternionCentralProductData Q)
    (hc : centralizer (Q : Set D) ≤ Q) (hD : Nat.card D = 576)
    (E S : Subgroup D) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (hEQ : E ≤ Q)
    (hS : Nat.card S = 64) (hSN : S ≤ normalizer (E : Set D))
    (hcentral : S ⊓ centralizer (E : Set D) = E)
    (z : E) (hz : z ≠ 1) (hzQ : (z : D) ∈ (center Q).map Q.subtype)
    (W : Subgroup E) (hW : Nat.card W = 4)
    (hstable : ∀ g : normalizer (E : Set D), ∀ x : E,
      E.normalizerMonoidHom g x ∈ W ↔ x ∈ W) : False := by
  obtain ⟨himage,hcard⟩ := normalizer_stabilizer Q d hc hD E S
    hE hEQ hS hSN hcentral z hz hzQ
  apply hz
  apply elementaryEight_plane_order24_fixed_eq_one hE W hW
    E.normalizerMonoidHom.range hcard
  · rintro ⟨_,g,rfl⟩ x
    exact hstable g x
  · intro a
    have ha : (a : MulAut E) ∈ MulAction.stabilizer (MulAut E) z := by
      rw [← himage]
      exact a.property
    exact ha


open CFSG.Quasithin.Chapter15.Section03
open SourcePreliminaries

/-- The quaternion rows of the original cubic rigidity argument. -/
theorem rigidity_of_geometry {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M Mc H : Subgroup G) (c : CubicSourceContext T M Mc H)
    (d : QuaternionCentralProductData (H.pCoreIn 2))
    (hH : Nat.card H = 192) (hT : Nat.card (T : Subgroup G) = 64)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hEQ : E ≤ H.pCoreIn 2)
    (hXE : sourceResidual M Mc ⊔ (T : Subgroup G) ≤ normalizer (E : Set G))
    (hcentral : (T : Subgroup G) ⊓ centralizer (E : Set G) = E) : H = Mc := by
  classical
  have hET : E ≤ (T : Subgroup G) := hcentral ▸ inf_le_left
  have hZE : centralInvolutions T ≤ E := by
    intro z hz
    rw [← hcentral]
    exact ⟨centralInvolutions_le_sylow T hz,
      (centralizer_le hET) (centralInvolutions_le_centralizer_sylow T hz)⟩
  have hVE : localModule T M ≤ E := by
    rw [c.module_span]
    exact conjugateSpanBy_le hZE hXE
  by_contra hproper
  have hTMc := c.sylow_le_H.trans c.H_le_Mc
  have hRMc := (pCoreIn_le 2 H).trans c.H_le_Mc
  have hEMc := hEQ.trans hRMc
  let R := (H.pCoreIn 2).subgroupOf Mc
  let E' := E.subgroupOf Mc
  let S := T.subtype hTMc
  let eR : R ≃* H.pCoreIn 2 := subgroupOfEquivOfLe hRMc
  let eE : E' ≃* E := subgroupOfEquivOfLe hEMc
  let dR := d.map eR.symm
  have hQR : pCore 2 Mc ≤ R := by
    let i : H →* Mc := inclusion c.H_le_Mc
    have hpre : (pCore 2 Mc).comap i ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective i (inclusion_injective _)⟩
    intro q hq
    have hqT : (q : G) ∈ (T : Subgroup G) :=
      show q ∈ (S : Subgroup Mc) from pCore_isPGroup.le_sylow_of_normal S hq
    exact ⟨⟨q,c.sylow_le_H hqT⟩,hpre hq,rfl⟩
  have hZMc : centralInvolutions T ≤ Mc :=
    (centralInvolutions_le_sylow T).trans hTMc
  let Z := (centralInvolutions T).subgroupOf Mc
  have hZ : Z ≤ center Mc := by
    intro z hz
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hx : (x : G) ∈ centralizer (centralInvolutions T : Set G) :=
      c.Mc_centralizer ▸ x.property
    exact (hx z hz).symm
  have hZcard : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZMc).toEquiv).trans c.mark_card
  have hQR' : pCore 2 Mc = R := core_eq Z R dR hZ hZcard hQR c.Mc_characteristic_two
  let dQ : QuaternionCentralProductData (pCore 2 Mc) :=
    dR.map (MulEquiv.subgroupCongr hQR'.symm)
  have hHc : Nat.card (H.subgroupOf Mc) = 192 :=
    (Nat.card_congr (subgroupOfEquivOfLe c.H_le_Mc).toEquiv).trans hH
  have hproper' : H.subgroupOf Mc ≠ ⊤ := by
    intro he
    apply hproper
    apply le_antisymm c.H_le_Mc
    intro x hx
    exact show (⟨x,hx⟩ : Mc) ∈ H.subgroupOf Mc from he.ge (mem_top _)
  have hS' : (S : Subgroup Mc) ≤ H.subgroupOf Mc := fun x hx => c.sylow_le_H hx
  have hMc : Nat.card Mc = 576 := card_eq_576_of_quaternion_product_enlargement
    (pCore 2 Mc) dQ c.Mc_characteristic_two (H.subgroupOf Mc) hHc hproper' S hS'
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.subgroupOf hEMc
  have hE' : Nat.card E' = 8 := (Nat.card_congr eE.toEquiv).trans hE
  have hEQ' : E' ≤ pCore 2 Mc := by
    rw [hQR']
    exact fun x hx => hEQ hx
  have hS64 : Nat.card (S : Subgroup Mc) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTMc).toEquiv).trans hT
  have hSN : (S : Subgroup Mc) ≤ normalizer (E' : Set Mc) := by
    rw [← subgroupOf_normalizer_eq hEMc]
    exact fun x hx => hXE (Subgroup.mem_sup_right hx)
  have hcentral' : (S : Subgroup Mc) ⊓ centralizer (E' : Set Mc) = E' := by
    ext x
    change (x : G) ∈ (T : Subgroup G) ∧ x ∈ centralizer (E' : Set Mc) ↔ (x : G) ∈ E
    have hh : x ∈ centralizer (E' : Set Mc) ↔ (x : G) ∈ centralizer (E : Set G) := by
      constructor
      · intro hc y hy
        exact congrArg Subtype.val (hc ⟨y,hEMc hy⟩ hy)
      · intro hc y hy
        exact Subtype.ext (hc y hy)
    rw [hh]
    exact SetLike.ext_iff.mp hcentral (x : G)
  have hZV : centralInvolutions T ≤ localModule T M := by
    rw [c.module_span]
    exact le_conjugateSpanBy _ _
  obtain ⟨z,hz, _⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp c.mark_card
  let z' : E' := ⟨⟨z,hZMc z.property⟩,hVE (hZV z.property)⟩
  have hz' : z' ≠ 1 := fun he => hz (Subtype.ext (congrArg (fun x : E' => (x : Mc).val) he))
  have hzQ : (z' : Mc) ∈ (center (pCore 2 Mc)).map (pCore 2 Mc).subtype := by
    refine ⟨⟨z',hEQ' z'.property⟩,mem_center_iff.mpr (fun q => ?_),rfl⟩
    apply Subtype.ext
    exact mem_center_iff.mp (hZ z.property) q
  let W : Subgroup E' := (localModule T M).comap (Mc.subtype.comp E'.subtype)
  let eW : W ≃* localModule T M := {
    toFun w := ⟨w.val.val.val,w.property⟩
    invFun v := ⟨⟨⟨v,hEMc (hVE v.property)⟩,hVE v.property⟩,v.property⟩
    left_inv := by intro w; rfl
    right_inv := by intro v; rfl
    map_mul' := by intro x y; rfl }
  have hW : Nat.card W = 4 := (Nat.card_congr eW.toEquiv).trans c.module_card
  have hn : normalizer (E : Set G) ≤ M := c.normalizer_control E
    (IsElementaryAbelian.isPGroup 2 E)
    (by intro he; have hh := Nat.card_congr (MulEquiv.subgroupCongr he).toEquiv
        have hb : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
        rw [hE,hb] at hh
        omega)
    hXE
  apply not_plane_stable (pCore 2 Mc) dQ c.Mc_characteristic_two hMc E' (S : Subgroup Mc)
    hE' hEQ' hS64 hSN hcentral' z' hz' hzQ W hW
  intro g x
  have hg : ((g : Mc) : G) ∈ normalizer (E : Set G) := by
    exact show (g : Mc) ∈ (normalizer (E : Set G)).subgroupOf Mc from
      (subgroupOf_normalizer_eq hEMc).symm ▸ g.property
  have hgV : ((g : Mc) : G) ∈ normalizer (localModule T M : Set G) :=
    c.module_normalizer ▸ hn hg
  exact ((mem_normalizer_iff.mp hgV) (x : Mc).val).symm


end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.ExtraspecialRigidity
