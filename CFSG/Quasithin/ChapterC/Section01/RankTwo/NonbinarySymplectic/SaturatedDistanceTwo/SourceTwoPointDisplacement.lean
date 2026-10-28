module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoPointCover
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary.RootFixed
public import Theory.SpecificGroups.SymplecticFour.RootHyperplane
public import Theory.Representation.SymplecticFourOrthogonalCover.HyperplaneMovement
public import Theory.Representation.SymplecticFourOrthogonalCover.RootValues

public noncomputable section
open scoped commutatorElement IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
open Representation.SymplecticFourOrthogonalCover

private theorem cover_moving_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    (centralizer (A : Set G)).relIndex U =
      Nat.card F ^ Module.finrank F
        (displacementSpace ((commutator (Sp F)).subtype.comp β).range) := by
  let α := (commutator (Sp F)).subtype.comp β
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  rw [hi]
  change 2 ^ Module.finrank (ZMod 2)
    (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
  rw [hfixed]
  have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (TwoLocalCover.fixedSpace α.range)).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  rw [hc,fixed_quotient_card]

private theorem cover_large_movement_displacement_bound
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A B : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F)) (γ : B →* L (K := F))
    (hactA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hactB : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (γ b) w))=
      b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
    (hlarge : Nat.card F^2 < (centralizer (A : Set G)).relIndex U)
    (htriple : ⁅⁅U,A⁆,B⁆=⊥) :
    Module.finrank F (displacementSpace (((commutator (Sp F)).subtype.comp γ).range)) ≤ 1 := by
  let α := (commutator (Sp F)).subtype.comp β
  let δ := (commutator (Sp F)).subtype.comp γ
  have hAB : displacementSpace α.range ≤ TwoLocalCover.fixedSpace δ.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩ b hb
    change b • (a.val • v-v)=a.val • v-v
    obtain ⟨a,ha⟩ := a.property
    rw [←ha]
    obtain ⟨b,rfl⟩ := hb
    obtain ⟨w,rfl⟩ := hp.1 v
    have hval : j (Multiplicative.ofAdd (σ (β a) w-w)) =
        ⁅a.val,j (Multiplicative.ofAdd w)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hactA]
      rfl
    have hc : b.val*⁅a.val,j (Multiplicative.ofAdd w)⁆ =
        ⁅a.val,j (Multiplicative.ofAdd w)⁆*b.val := by
      apply commutator_eq_bot_iff_le_centralizer.mp htriple
      · rw [commutator_comm]
        exact commutator_mem_commutator a.property (hjr ▸ ⟨_,rfl⟩)
      · exact b.property
    have he : σ (γ b) (σ (β a) w-w)=σ (β a) w-w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hactB,hval,hc,mul_inv_cancel_right]
    have hh := congrArg p he
    rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
    exact hh
  rw [cover_moving_index σ p hp U A j hj hjr β hactA] at hlarge
  have hdim : 2 < Module.finrank F (displacementSpace α.range) :=
    (pow_lt_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card F)).mp hlarge
  have hle := Submodule.finrank_mono hAB
  rw [←orthogonal_displacementSpace,
    LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate] at hle
  have hv : Module.finrank F (Theory.SpecificGroups.SymplecticFour.Vector F)=4 := by
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hv] at hle
  have hd := (displacementSpace δ.range).finrank_le
  rw [hv] at hd
  have hδ : Module.finrank F (displacementSpace δ.range) ≤ 1 := by omega
  exact hδ


private theorem point_small_displacement_le_root
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (P B C : Subgroup (Sp F)) [IsElementaryAbelian 2 P]
    (hBP : B ≤ P) (hCP : C ≤ P)
    (hBdim : Module.finrank F (displacementSpace B) ≤ 1)
    (hBcard : Nat.card B = Nat.card F)
    (hCdim : Module.finrank F (displacementSpace C) ≤ 1)
    (v : Sp F) (hP : P.map (MulAut.conj v).toMonoidHom = pointRadicalAmbient) :
    C ≤ B := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (inclusion hBP) (inclusion_injective _)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hCP) (inclusion_injective _)
  have hdim : Module.finrank F (displacementSpace B) = 1 := by
    have hc := card_actor_le_displacement_dimension B
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hn : Module.finrank F (displacementSpace B) ≠ 0 := by
      intro hz
      rw [hz,zero_pow (by decide : 2 ≠ 0),pow_zero,hBcard] at hc
      omega
    omega
  have hBne : B ≠ ⊥ := by
    intro hz
    rw [hz,Subgroup.card_bot] at hBcard
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hm (X : Subgroup (Sp F)) (hx : Module.finrank F (displacementSpace X) ≤ 1)
      (x : Sp F) (hxx : x ∈ X) : Module.finrank F (movedSpace x) ≤ 1 := by
    apply (Submodule.finrank_mono (show movedSpace x ≤ displacementSpace X from ?_)).trans hx
    rintro _ ⟨w,rfl⟩
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp X.subtype) ⟨x,hxx⟩ w
  have hfixB := MaximalElementary.point_displacement_eq_root_fixed P B hBP hBne
    (hm B hBdim) v hP
  by_cases hC : C = ⊥
  · rw [hC]; exact bot_le
  have hfixC := MaximalElementary.point_displacement_eq_root_fixed P C hCP hC
    (hm C hCdim) v hP
  rw [←root_fixedSpace_fixer_eq B hdim hBcard]
  intro x hx
  apply (mem_fixingSubgroup_iff _).mpr
  intro w hw
  have he : TwoLocalCover.fixedSpace B = TwoLocalCover.fixedSpace C :=
    hfixB.symm.trans hfixC
  exact (he ▸ hw) x hx

private theorem index_le_relative_product
    {G : Type*} [Group G] [Finite G] (N X : Subgroup G) :
    N.index ≤ N.relIndex X * X.index := by
  have ht : N.index ≤ (N ⊓ X).index := by
    have hh := relIndex_le_of_le_left (L := ⊤) (show N ⊓ X ≤ N from inf_le_left)
      (show (N ⊓ X).relIndex ⊤ ≠ 0 from index_ne_zero_of_finite)
    simpa only [relIndex_top_right] using hh
  have hm := relIndex_mul_index (H := N ⊓ X) (K := X) inf_le_right
  rw [inf_relIndex_right] at hm
  exact ht.trans_eq hm.symm

private theorem embedded_kernel_card_le_field
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) :
    Nat.card (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) ≤ Nat.card F := by
  have hd := finrank_ker_le_H1_of_cover p hp
  rw [binary_dual_H1_finrank] at hd
  rw [embedded_cover_kernel_card p j hj,
    Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  calc
    2 ^ Module.finrank (ZMod 2) p.toLinearMap.ker ≤
        2 ^ Module.finrank (ZMod 2) F := Nat.pow_le_pow_right (by decide) hd
    _ = Nat.card F := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]

private theorem embedded_displacement_disjoint_kernel_of_card
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) [Finite U] (j : Multiplicative W →* G)
    (hj : Function.Injective j) (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hAU : A ≤ normalizer (U : Set G))
    (hsize : (centralizer (A : Set G)).relIndex U = Nat.card (⁅A,U⁆ : Subgroup G)) :
    Disjoint (⁅A,U⁆) (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) := by
  classical
  let α := (commutator (Sp F)).subtype.comp β
  let D := displacementSpace α.range
  let C := ⁅A,U⁆
  let : Finite C := Finite.of_injective
    (inclusion (le_normalizer_iff_commutator_le_right.mp hAU)) (inclusion_injective _)
  have hlift : ∀ v : D, ∃ w : W, p w=v.val ∧ j (Multiplicative.ofAdd w) ∈ C :=
    fun v => natural_displacement_lifts U A j hjr β σ hact p hp.1 v.val v.property
  choose w hw hm using hlift
  let f : D → C := fun v => ⟨j (Multiplicative.ofAdd (w v)),hm v⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : w x=w y := Multiplicative.ofAdd.injective (hj (congrArg Subtype.val he))
    exact Subtype.ext ((hw x).symm.trans ((congrArg p hh).trans (hw y)))
  have hcard : Nat.card D = Nat.card C := by
    calc
      Nat.card D = Nat.card F ^ Module.finrank F D := Module.natCard_eq_pow_finrank
      _ = (centralizer (A : Set G)).relIndex U :=
        (cover_moving_index σ p hp U A j hj hjr β hact).symm
      _ = Nat.card C := hsize
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩).2
  have hfzero : f 0=1 := by
    obtain ⟨v,hv⟩ := hs 1
    have hw0 : w v=0 := by
      apply Multiplicative.ofAdd.injective
      apply hj
      exact (congrArg Subtype.val hv).trans (map_one j).symm
    have hv0 : v=0 := Subtype.ext ((hw v).symm.trans (by simp only [hw0,map_zero,Submodule.coe_zero]))
    simpa only [hv0] using hv
  apply Subgroup.disjoint_def.mpr
  intro x hx hk
  obtain ⟨k,hk,hkx⟩ := hk
  obtain ⟨v,hv⟩ := hs ⟨x,hx⟩
  have hwk : w v=k.toAdd := Multiplicative.ofAdd.injective
    (hj ((congrArg Subtype.val hv).trans hkx.symm))
  have hv0 : v=0 := Subtype.ext ((hw v).symm.trans ((congrArg p hwk).trans hk))
  rw [hv0,hfzero] at hv
  exact congrArg Subtype.val hv.symm

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem source_two_large_fixedCore_not_le_component_sup
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    ¬ fixedCore d.radical a ≤ componentRadical d a t ⊔ Q d.radical z := by
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : ((Q d.radical z).subgroupOf (Q d.radical t)).Normal := c'.core_normal
  have hBT : componentRadical d a t ≤ Q d.radical t := inf_le_left
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  intro hDle
  let X := componentRadical d a t ⊔ fixedCore d.radical a
  have hXT : X ≤ Q d.radical t := sup_le hBT hDT
  have hXle : X ≤ componentRadical d a t ⊔ Q d.radical z := sup_le le_sup_left hDle
  have hrel : (Q d.radical z).relIndex X ≤ 2^n := by
    have hh := relIndex_le_of_le_right hXle (show
      (Q d.radical z).relIndex (componentRadical d a t ⊔ Q d.radical z) ≠ 0 from by
        let : Finite (componentRadical d a t ⊔ Q d.radical z : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
          (inclusion (sup_le hBT c'.core_le_edge)) (inclusion_injective _)
        exact index_ne_zero_of_finite)
    rw [←relIndex_subgroupOf (sup_le hBT c'.core_le_edge),
      subgroupOf_sup hBT c'.core_le_edge,relIndex_sup_right,relIndex_subgroupOf hBT,
      (source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).1] at hh
    exact hh
  have hi := index_le_relative_product ((Q d.radical z).subgroupOf (Q d.radical t))
    (X.subgroupOf (Q d.radical t))
  rw [relIndex_subgroupOf hXT] at hi
  change (Q d.radical z).relIndex (Q d.radical t) ≤
    (Q d.radical z).relIndex X * X.relIndex (Q d.radical t) at hi
  have hXindex := (componentRadical_fixedCore_relIndex h d g hb path.start_color c).2
  have hc := source_two_large_full_radical_card h d g hb hsat path hat hzt c c' hlarge
  rw [hc] at hi
  have hle : (2^n)^3 ≤ (2^n)^2 := hi.trans (by
    simpa only [pow_two] using Nat.mul_le_mul hrel hXindex)
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 2 < 3))) hle

theorem source_two_large_fixedCore_movement_eq_square
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) = (2^n)^2 := by
  let := replacementComponent_normal h d
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : ((Q d.radical z).subgroupOf (Q d.radical t)).Normal := c'.core_normal
  let s := replacementMovedSection h d
  obtain ⟨pc⟩ := source_two_large_radical_point_cover h d g hb hsat path hat hzt c c' hlarge
  let E := pc.field
  let α := (commutator (Sp E.Carrier)).subtype.comp pc.actor
  have hAT : Q d.radical a ≤ Q d.radical t := c.core_le_edge
  have hBT : componentRadical d a t ≤ Q d.radical t := inf_le_left
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans hAT
  let βA := pc.actor.comp (inclusion hAT)
  let βB := pc.actor.comp (inclusion hBT)
  let βD := pc.actor.comp (inclusion hDT)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  let αD := (commutator (Sp E.Carrier)).subtype.comp βD
  have hBker : αB.ker = (Q d.radical z).subgroupOf (componentRadical d a t) := by
    change (α.comp (inclusion hBT)).ker = _
    rw [←MonoidHom.comap_ker,pc.actor_kernel,comap_inclusion_subgroupOf]
  have hBcard : Nat.card αB.range = Nat.card E.Carrier := by
    rw [←index_ker,hBker]
    change (Q d.radical z).relIndex (componentRadical d a t)=_
    rw [(source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).1,
      E.card_eq,pc.degree]
  have hBdim : Module.finrank E.Carrier (displacementSpace αB.range) ≤ 1 := by
    apply cover_large_movement_displacement_bound (MovedSection.coverAction s pc.equiv)
      (MovedSection.coverProjection s pc.equiv) pc.cover (U d.radical z)
      (Q d.radical a) (componentRadical d a t) pc.embedding pc.injective pc.range_eq βA βB
      (fun x => pc.actor_conjugation (inclusion hAT x))
      (fun x => pc.actor_conjugation (inclusion hBT x))
      (by simpa only [pc.field.card_eq,pc.degree] using hlarge)
    exact le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (paired_source_triples h d g hb hsat path hat hzt c c').2.1.le) bot_le
  have hiD := cover_moving_index (MovedSection.coverAction s pc.equiv)
    (MovedSection.coverProjection s pc.equiv) pc.cover (U d.radical z)
    (fixedCore d.radical a) pc.embedding pc.injective pc.range_eq βD
    (fun x => pc.actor_conjugation (inclusion hDT x))
  have hsmall := source_two_fixedCore_movement_le_square h d g hb hsat path hat hzt c c'
  have hfield : Nat.card E.Carrier = 2^n := E.card_eq.trans (congrArg (2^·) pc.degree)
  have hdimupper : Module.finrank E.Carrier (displacementSpace αD.range) ≤ 2 := by
    have hp : Nat.card E.Carrier ^ Module.finrank E.Carrier (displacementSpace αD.range) ≤
        Nat.card E.Carrier ^ 2 := (hiD.symm.trans_le hsmall).trans_eq (congrArg (·^2) hfield.symm)
    exact (pow_le_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card E.Carrier)).mp hp
  have hdimlower : ¬ Module.finrank E.Carrier (displacementSpace αD.range) ≤ 1 := by
    intro hDdim
    let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (pc.actor_kernel.trans c'.action_kernel.symm)).trans
        (QuotientGroup.quotientKerEquivRange c'.action))
    let : IsElementaryAbelian 2 c'.action.range := c'.action_range.symm ▸
      source_two_large_marked_radical_elementary h d g hb hsat path hat hzt c c' hlarge
    let : IsElementaryAbelian 2 α.range :=
      IsElementaryAbelian.of_surjective er.symm.toMonoidHom er.symm.surjective
    obtain ⟨v,hv⟩ := pc.point_image
    have hDB : αD.range ≤ αB.range := point_small_displacement_le_root α.range αB.range αD.range
      (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hBT x,rfl⟩)
      (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hDT x,rfl⟩) hBdim hBcard hDdim v hv
    have hDle : fixedCore d.radical a ≤ componentRadical d a t ⊔ Q d.radical z := by
      intro x hx
      obtain ⟨b,hb⟩ := hDB (show αD ⟨x,hx⟩ ∈ αD.range from ⟨_,rfl⟩)
      have hker : (inclusion hBT b)⁻¹ * inclusion hDT ⟨x,hx⟩ ∈ α.ker := by
        change α ((inclusion hBT b)⁻¹ * inclusion hDT ⟨x,hx⟩)=1
        rw [map_mul,map_inv]
        change (αB b)⁻¹ * αD ⟨x,hx⟩ = 1
        rw [hb,inv_mul_cancel]
      rw [pc.actor_kernel] at hker
      have hm := (componentRadical d a t ⊔ Q d.radical z).mul_mem
        (mem_sup_left b.property) (mem_sup_right hker)
      change b.val * (b.val⁻¹*x) ∈ _ at hm
      simpa only [mul_inv_cancel_left] using hm
    exact source_two_large_fixedCore_not_le_component_sup h d g hb hsat path hat hzt c c' hlarge hDle
  have hdim : Module.finrank E.Carrier (displacementSpace αD.range)=2 := by omega
  rw [hiD]
  change Nat.card E.Carrier ^ Module.finrank E.Carrier (displacementSpace αD.range)=_
  rw [hdim,hfield]

/-- The full fixed attachment in the original natural cover has order at most q. -/
theorem moving_fixed_attachment_card_le_field
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    Nat.card (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) ≤ 2^n := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨pc⟩ := replacement_ambient_initial_cover_at_vertex h d ha
  have hk : (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding = U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨pc.range_eq ▸ ⟨w,rfl⟩,(pc.kernel w.toAdd).mp hw⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := (pc.range_eq.symm ▸ hx.1 : x ∈ pc.embedding.range)
      exact ⟨w,(pc.kernel w.toAdd).mpr hx.2,rfl⟩
  have hbound := embedded_kernel_card_le_field (MovedSection.coverAction s pc.equiv)
    (MovedSection.coverProjection s pc.equiv) pc.cover pc.embedding pc.injective
  rw [hk,pc.field.card_eq,pc.degree] at hbound
  exact hbound

/-- The source point-radical squeeze determines the full displacement and
both original fixed attachments without discarding a central kernel. -/
theorem source_two_large_fixed_attachment_displacement_card
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    let C := ⁅Z d.radical z,fixedCore d.radical a⁆
    Nat.card A = 2^n ∧ Nat.card A' = 2^n ∧ Nat.card C = (2^n)^2 ∧ A ≤ C := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
  let C := ⁅Z d.radical z,fixedCore d.radical a⁆
  let W := ⁅Z d.radical a,Z d.radical z⁆
  change Nat.card A = 2^n ∧ _ ∧ Nat.card C = (2^n)^2 ∧ A ≤ C
  obtain ⟨pc⟩ := source_two_large_radical_point_cover h d g hb hsat path hat hzt c c' hlarge
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  let β := pc.actor.comp (inclusion hDT)
  have hlow := HyperplaneMovement.embedded_fixed_index_le_commutator_card
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U d.radical z) (fixedCore d.radical a) pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x))
  have hmove : ⁅fixedCore d.radical a,U d.radical z⁆ = C := by
    rw [commutator_comm]
    exact (fixedCore_displacement_eq_moving h d g hb path hat hzt c c').symm
  rw [source_two_large_fixedCore_movement_eq_square h d g hb hsat path hat hzt c c' hlarge,
    hmove] at hlow
  have hupper := source_two_large_displacement_card h d g hb hsat path hat hzt c c' hlarge
  have hA := moving_fixed_attachment_card_le_field h d path.start_color
  have hq : 0 < 2^n := by positivity
  have hAc : Nat.card A = 2^n := by change Nat.card C ≤ 2^n * Nat.card A at hupper; nlinarith
  have hCc : Nat.card C = (2^n)^2 := by
    change Nat.card C ≤ 2^n * Nat.card A at hupper
    rw [hAc] at hupper
    nlinarith
  have hlayers := source_two_large_paired_fixed_layers h d g hb hsat path hat hzt c c' hlarge
  refine ⟨hAc,hlayers.2.2.2.1.symm.trans hAc,hCc,?_⟩
  let := finite_Z d.radical a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  let : Finite (W ⊓ C : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hlayers.2.2.2.2) (inclusion_injective _)
  have hindex := source_two_large_displacement_index h d g hb hsat path hat hzt c c' hlarge
  have hmul : Nat.card (W ⊓ C : Subgroup (FreeAmalgam d.radical)) * W.relIndex C = Nat.card C := by
    have hh := ((W ⊓ C).subgroupOf C).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show W ⊓ C ≤ C from inf_le_right)).toEquiv] at hh
    change Nat.card (W ⊓ C : Subgroup (FreeAmalgam d.radical)) * (W ⊓ C).relIndex C = Nat.card C at hh
    rwa [inf_relIndex_right] at hh
  have hge : Nat.card A ≤ Nat.card (W ⊓ C : Subgroup (FreeAmalgam d.radical)) := by
    rw [hAc]
    change W.relIndex C ≤ 2^n at hindex
    rw [hCc] at hmul
    nlinarith
  have he := Subgroup.eq_of_le_of_card_ge hlayers.2.2.2.2 hge
  exact he.symm.le.trans inf_le_right

set_option maxHeartbeats 1000000 in
private theorem pointCover_displacement_disjoint_fixedCore
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (pc : RadicalPointCover d.radical (replacementMovedSection h d) n z t)
    (hsize : (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) = Nat.card (⁅Z d.radical z,fixedCore d.radical a⁆ : Subgroup (FreeAmalgam d.radical))) :
    Disjoint ⁅Z d.radical z,fixedCore d.radical a⁆ (fixedCore d.radical z) := by
  let := replacementComponent_normal h d
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (U_le_Z z)) (inclusion_injective _)
  let s := replacementMovedSection h d
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have hnorm : fixedCore d.radical a ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    hDT.trans (c'.edge_le.trans (U_normalized z))
  let β := pc.actor.comp (inclusion hDT)
  have hk : (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding = U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨pc.range_eq ▸ ⟨w,rfl⟩,(pc.kernel w.toAdd).mp hw⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := (pc.range_eq.symm ▸ hx.1 : x ∈ pc.embedding.range)
      exact ⟨w,(pc.kernel w.toAdd).mpr hx.2,rfl⟩
  have hmove : ⁅fixedCore d.radical a,U d.radical z⁆ = ⁅Z d.radical z,fixedCore d.radical a⁆ := by
    rw [commutator_comm]
    exact (fixedCore_displacement_eq_moving h d g hb path hat hzt c c').symm
  have hsize' : (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) = Nat.card (⁅fixedCore d.radical a,U d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) := by
    rw [hmove]
    exact hsize
  have hdis := embedded_displacement_disjoint_kernel_of_card
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U d.radical z) (fixedCore d.radical a) pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x)) hnorm hsize'
  rw [hmove,hk] at hdis
  have hCU : ⁅Z d.radical z,fixedCore d.radical a⁆ ≤ U d.radical z := by
    rw [←hmove]
    exact le_normalizer_iff_commutator_le_right.mp hnorm
  have hfull : Disjoint ⁅Z d.radical z,fixedCore d.radical a⁆ (fixedCore d.radical z) := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hz
    exact Subgroup.disjoint_def.mp hdis hx ⟨hCU hx,hz.2⟩
  exact hfull

/-- The full fixed-core displacement is disjoint from the opposite
entire fixed core; in particular the first attachment meets that core trivially. -/
theorem source_two_large_displacement_disjoint_opposite_fixedCore
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    Disjoint ⁅Z d.radical z,fixedCore d.radical a⁆ (fixedCore d.radical z) ∧
      Disjoint (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
        (fixedCore d.radical z) := by
  obtain ⟨pc⟩ := source_two_large_radical_point_cover h d g hb hsat path hat hzt c c' hlarge
  have hcards := source_two_large_fixed_attachment_displacement_card h d g hb hsat path hat hzt c c' hlarge
  have hsize := (source_two_large_fixedCore_movement_eq_square h d g hb hsat path hat hzt c c' hlarge).trans
    hcards.2.2.1.symm
  have hfull := pointCover_displacement_disjoint_fixedCore h d g hb path hat hzt c c' pc hsize
  exact ⟨hfull,hfull.mono_left hcards.2.2.2⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

