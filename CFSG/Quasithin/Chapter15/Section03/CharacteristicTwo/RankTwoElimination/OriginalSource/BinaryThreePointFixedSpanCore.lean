module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCoordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanDisplacementBound
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourEndpointEquality
public import Theory.Representation.BinaryEndpointInduction.EndpointParabolicIdentification
public import Theory.Representation.BinaryFifteenPoint.ParabolicCoinvariants

/-!
# The original fixed-four span lies in the original commutator core

The actual image of [U,L] in U/<z> has dimension at most eleven. Every
marked parabolic displacement lands in this image. The complete finite
kernel certificate then makes the original seed and this displacement
span all of U/<z>. Both lift into Q, and the full quotient kernel <z> is
already in Q. This proves U≤Q without identifying the point kernel with Q.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryEndpointInduction

section Helpers
variable {G E : Type*} [Group G] [Finite G] [Group E] [IsElementaryAbelian 2 E]
private def imageModule (U A : Subgroup G) (p : U →* E) :
    Submodule (ZMod 2) (Additive E) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup ((A.subgroupOf U).map p))

private theorem imageModule_card_le (U A : Subgroup G) (p : U →* E)
    (hAU : A ≤ U) : Nat.card (imageModule U A p) ≤ Nat.card A := by
  have he : Nat.card (imageModule U A p)=Nat.card ((A.subgroupOf U).map p) :=
    Nat.card_congr {
      toFun := fun x => ⟨x.val.toMul,x.property⟩
      invFun := fun x => ⟨Additive.ofMul x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [he]
  have hm := Nat.le_of_dvd (Nat.card_pos (α := A.subgroupOf U))
    ((A.subgroupOf U).card_map_dvd p)
  exact hm.trans_eq (Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv)

omit [Finite G] in
private theorem displacement_mem (U L : Subgroup G) (hLU : L ≤ normalizer U)
    (p : U →* E) (hp : Function.Surjective p)
    (τ : Representation (ZMod 2) L (Additive E))
    (hτ : ∀ (l : L) (u v : U), (v:G)=l*(u:G)*(l:G)⁻¹ →
      τ l (Additive.ofMul (p u))=Additive.ofMul (p v))
    (l : L) (y : Additive E) : τ l y-y ∈ imageModule U ⁅U,L⁆ p := by
  obtain ⟨u,hu⟩ := hp y.toMul
  have hy : Additive.ofMul (p u)=y := congrArg Additive.ofMul hu
  rw [←hy]
  let v : U := U.normalizerMonoidHom ⟨l,hLU l.property⟩ u
  rw [hτ l u v rfl]
  change p v / p u ∈ (⁅U,L⁆.subgroupOf U).map p
  refine ⟨v/u,?_,map_div p v u⟩
  change ((v:G)/(u:G)) ∈ ⁅U,L⁆
  have hh := commutator_mem_commutator l.property u.property
  rw [commutator_comm L U] at hh
  change (l:G)*(u:G)*(l:G)⁻¹/(u:G) ∈ ⁅U,L⁆
  simpa only [commutatorElement_def,div_eq_mul_inv] using hh

omit [Finite G] in
private theorem subgroup_le_of_image_eq_top (U Q Z : Subgroup G)
    (p : U →* E) (hker : p.ker=Z.subgroupOf U) (hZQ : Z ≤ Q)
    (htop : imageModule U Q p=⊤) : U ≤ Q := by
  intro u hu
  have hp : Additive.ofMul (p ⟨u,hu⟩) ∈ imageModule U Q p := htop ▸ Submodule.mem_top
  obtain ⟨v,hv,he⟩ := hp
  change p v=p ⟨u,hu⟩ at he
  have hz : (⟨u,hu⟩ : U)/v ∈ p.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_div,he,div_self']
  rw [hker] at hz
  have hh := Q.mul_mem (hZQ hz) hv
  change u/(v:G)*(v:G) ∈ Q at hh
  simpa only [div_mul_cancel] using hh

open scoped MatrixGroups
open Matrix BinaryEndpointInduction
variable {X : Type*} [Group X]
omit [Finite G] in
private theorem coordinate_displacements
    (C L U : Subgroup G) (hLC : L ≤ C) (hCU : C ≤ normalizer U)
    (q : C →* X) (K : Subgroup X) (eK : K ≃* SL(4,ZMod 2))
    (heK : (((L.subgroupOf C).map q).subgroupOf K).map eK.toMonoidHom=endpointParabolic)
    (p : U →* E) (hp : Function.Surjective p) (ρ : X →* MulAut E)
    (hρ : ∀ (c : C) (u v : U), (v:G)=c*(u:G)*(c:G)⁻¹ → ρ (q c) (p u)=p v)
    (F : (Fin 15 → ZMod 2) →ₗ[ZMod 2] Additive E)
    (hFa : ∀ (a : Fin 6) x, F (x ᵥ* BinaryFifteenPoint.permutationActor a)=
      elementaryRepresentation (p := 2) (ρ.comp K.subtype) (eK.symm (cosetActor a)⁻¹) (F x))
    (j : Fin 4) (x : Fin 15 → ZMod 2) :
    F (x ᵥ* BinaryFifteenPoint.permutationActor ⟨j.val+2,by omega⟩)-F x ∈
      imageModule U ⁅U,L⁆ p := by
  let B := (L.subgroupOf C).map q
  let κ := eK.symm (parabolicGenerator j)⁻¹
  have hκ : κ ∈ B.subgroupOf K := by
    apply mem_map_equiv.mp
    rw [heK]
    exact endpointParabolic.inv_mem (parabolicGenerator_mem_endpoint j)
  obtain ⟨c,hc,hcκ⟩ := (show κ.val ∈ (L.subgroupOf C).map q from hκ)
  let l : L := ⟨c.val,hc⟩
  let σ := elementaryRepresentation (p := 2) (ρ.comp (q.comp (inclusion hLC)))
  have hσ (l : L) (u v : U) (hv : (v:G)=l*(u:G)*(l:G)⁻¹) :
      σ l (Additive.ofMul (p u))=Additive.ofMul (p v) := by
    exact congrArg Additive.ofMul (hρ (inclusion hLC l) u v hv)
  have hact (y : Additive E) : σ l y=elementaryRepresentation (p := 2) (ρ.comp K.subtype) κ y := by
    change Additive.ofMul (ρ (q (inclusion hLC l)) y.toMul)=Additive.ofMul (ρ κ.val y.toMul)
    have he : inclusion hLC l=c := Subtype.ext rfl
    rw [he,hcκ]
  have hd := displacement_mem U L (hLC.trans hCU) p hp σ hσ l (F x)
  rw [hact] at hd
  rw [hFa,cosetActor_parabolic]
  exact hd

end Helpers

variable {G : Type*} [Group G] [Finite G]

/-- The actual point-centralizer span of H is contained in the original Q. -/
theorem binary_three_source_fixed_span_le_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G)) ≤
      LinearThree.commutatorCore c.L := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  let Q := LinearThree.commutatorCore c.L
  let T := ⁅U,c.L⁆
  have hz1 : z ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hz2
    norm_num at hz2
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨_,_,_,_,hCU,_⟩ := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK (Or.inl rfl) hm
  have hLU : c.L ≤ normalizer U := hLC.trans hCU
  have hTU : T ≤ U := le_normalizer_iff_commutator_le_left.mp hLU
  have hTQ : T ≤ Q := (binary_three_source_fixed_span_middle_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hzH hz1).2.1.trans inf_le_left
  have hTcard : Nat.card T ≤ 2048 := (binary_three_source_fixed_span_displacement_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hzH hz1).2.2.2
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHQ : H ≤ Q :=
    (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans inf_le_left
  have hZQ : Z ≤ Q := (zpowers_le.mpr hzH).trans hHQ
  obtain ⟨hZ,hel,ρ,hρ,h,_,_,_,hcoords⟩ := binary_three_source_fixed_span_coordinates
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm
  let := hZ
  let := hel
  let p := QuotientGroup.mk' (Z.subgroupOf U)
  obtain ⟨_,_,_,a,v,_,hflag⟩ :=
    binary_three_point_four_endpoint_equality d c.L b z hLS P hP K hBK hm
  obtain ⟨eK,heK⟩ := exists_endpointParabolic_marking (B.subgroupOf K) a v hflag
  obtain ⟨F,hF,hFi,hFa,r,hr,_⟩ := hcoords eK heK
  let S := imageModule U T p
  have hScard : Nat.card S ≤ 2048 := (imageModule_card_le U T p hTU).trans hTcard
  have hSdim : Module.finrank (ZMod 2) S ≤ 11 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hScard
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hScard
  have hdisp := coordinate_displacements C c.L U hLC hCU q K eK heK p
    (QuotientGroup.mk'_surjective _) ρ hρ F hFa
  have hspan := BinaryFifteenPoint.parabolic_seed_span_of_finrank_le r F hF hr S hSdim hdisp
  have hSQ : S ≤ imageModule U Q p := by
    rintro y ⟨u,hu,he⟩
    exact ⟨u,hTQ hu,he⟩
  have hseed : F (Pi.single 0 1) ∈ imageModule U Q p := by
    have he := hFi 0
    simp only [cosetRepresentative_zero,inv_one,map_one,Module.End.one_apply] at he
    rw [he]
    exact ⟨inclusion (le_conjugateSpanBy H C) h,hHQ h.property,rfl⟩
  have htop : imageModule U Q p=⊤ := by
    apply top_unique
    rw [←hspan]
    apply sup_le ?_ hSQ
    apply Submodule.span_le.mpr
    intro y hy
    have he := Set.mem_singleton_iff.mp hy
    subst y
    exact hseed
  exact subgroup_le_of_image_eq_top U Q Z p (QuotientGroup.ker_mk' _) hZQ htop

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
