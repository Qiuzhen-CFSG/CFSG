module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourKernel
public import Theory.Representation.HermitianTensorThree.PlaneSection
/-!
# The actual selected Hermitian section

For the original parameter-one pair, E.2.10 places [A,B] in U. Under the
same plane-radical marking this puts B in the canonical hyperplane X₂₂=0.
Both have order 2⁸, so the marking identifies B exactly, while U is the
Hermitian corner. Matrix congruences then identify the full kernels on B/U
and U for every element of N_L(U). The original central/module kernels
are retained; no faithful replacement of the ambient component is made.

The companion Chapter 12 module uses its established C_R(U)=O₂(R) to
discharge the B/U kernel premise of 8.2.8(4) for the literal chosen module.
Source: Aschbacher–Smith E.2.10, H.4.6(2), and 8.2.8(4), printed
pp.222,382,718, refs/quasithin.pdf (1 March 2004 manuscript).
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]

/-- The selected B and U are the literal hyperplane and corner in one marking. -/
theorem selected_one_section_coordinates
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    {H M I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 1 i S) (hT : HypothesisE322 V T)
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction 1 (binaryNormalizer 1) (j a) (e v)) :
    ∃ c : Cover 1, let e' := e.trans (binaryActionHom 1 c)
      (∀ v : Additive V, (v.toMul : G) ∈ V ⊓ centralizer
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) ↔
        e' v ∈ PlaneSection.Corner) ∧
      (∀ v : Additive V, (v.toMul : G) ∈ V ⊓ I.pCoreIn 2 ↔ (e' v).val 2 2 = 0) := by
  obtain ⟨_,hAT,_,_,hUeq,_,_,_,_,c,hc⟩ := selected_one_fixed_subgroup s hT 1 e j hj he
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let B := V ⊓ I.pCoreIn 2
  let U := V ⊓ centralizer (A : Set G)
  let z := binaryActionHom 1 c
  let e' := e.trans z
  let l := (MulAut.conj z).toMonoidHom.comp ((binaryNormalizer 1).subtype.comp j)
  have hl (a : Automizer V) (v : Additive V) :
      e' (automizerRepresentation V a v) = l a (e' v) := by
    change z (e (automizerRepresentation V a v)) = z ((j a).val (z.symm (z (e v))))
    rw [z.symm_apply_apply]
    exact congrArg z (he a v)
  have him : (inducedAutomizer V A).map l = UnipotentRadicals.plane 1 := by
    rw [←map_map]
    exact hc
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans hT.normalizes
  have hmark (v : Additive V) : (v.toMul : G) ∈ U ↔ e' v ∈ PlaneSection.Corner := by
    constructor
    · intro hv a
      have hfix := (mem_fixedSpace_inducedAutomizer V A hAN v).mpr hv.2
      obtain ⟨x,hx,hxa⟩ := (show a.val ∈ (inducedAutomizer V A).map l by rw [him]; exact a.property)
      change a.val (e' v) = e' v
      rw [←hxa,←hl]
      exact congrArg e' (hfix ⟨x,hx⟩)
    · intro hv
      refine ⟨v.toMul.property,?_⟩
      apply (mem_fixedSpace_inducedAutomizer V A hAN v).mp
      intro a
      apply e'.injective
      change e' (automizerRepresentation V a.val v) = e' v
      rw [hl]
      exact hv ⟨l a.val,him ▸ mem_map_of_mem l a.property⟩
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hbmap : (TwoConjugate.B (V.subgroupOf I) (M.subgroupOf I)).map I.subtype = B := by
    rw [s.twoConjugate.B_eq_twoCore_inf,map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hVI,inf_comm]
    rfl
  have hcomm : ⁅A,B⁆ ≤ U := by
    have hh := map_mono (f := I.subtype) s.twoConjugate.commutator_A_B_le_Z
    rw [map_commutator,selected_actor_image I M V hVI S i s.twoConjugate,
      hbmap,selected_intersection_image I V hVI i,←hUeq] at hh
    exact hh
  have hB (v : Additive V) (hv : (v.toMul : G) ∈ B) : (e' v).val 2 2 = 0 := by
    apply (PlaneSection.displacement_mem_corner_iff _).mp
    intro t ht
    obtain ⟨a,ha,hat⟩ := (show t ∈ (inducedAutomizer V A).map l by rw [him]; exact ht)
    obtain ⟨a,ha,rfl⟩ := ha
    have hdisp : (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict a) v - v).toMul.val ∈ U := by
      change (a.val * (v.toMul : G) * a.val⁻¹) / (v.toMul : G) ∈ U
      simpa only [Subgroup.subtype_apply,commutatorElement_def,div_eq_mul_inv] using hcomm (commutator_mem_commutator ha hv)
    have hh := (hmark _).mp hdisp
    rw [map_sub,hl,hat] at hh
    exact hh
  have hdim : rank V = 9 := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hcor : subgroupCorank V B = 1 := by
    change subgroupCorank V (V ⊓ (pCore 2 I).map I.subtype) = 1
    rw [←quotient_rank_eq_core_corank I V hVI]
    exact s.rank_eq
  have hrB : rank B = 8 := by
    have hh := offender_corank_add (W := V) (A := B) bot_le inf_le_left
    have hh' : rank V = subgroupCorank V B + rank B := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hh
    omega
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ V from inf_le_left)
  have hcard : Nat.card B = 2^8 := by
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
    have hh : rank B = a := by rw [rank,ha,Nat.log_pow Nat.one_lt_two]
    rw [ha]
    congr 1
    omega
  let f : B → {X : Space 1 // X.val 2 2 = 0} :=
    fun b => ⟨e' (Additive.ofMul ⟨b,b.property.1⟩),hB _ b.property⟩
  have hfi : Function.Injective f := by
    intro b d hbd
    have hh := e'.injective (congrArg Subtype.val hbd)
    exact Subtype.ext (congrArg (fun v : Additive V => (v.toMul : G)) hh)
  have hfs : Function.Surjective f := (hfi.bijective_of_nat_card_le (by
    rw [PlaneSection.card_hyperplane,hcard])).2
  refine ⟨c,hmark,fun v => ⟨hB v,?_⟩⟩
  intro hv
  obtain ⟨b,hb⟩ := hfs ⟨e' v,hv⟩
  have hh := e'.injective (congrArg Subtype.val hb)
  have hbv : (b : G) = (v.toMul : G) := congrArg (fun v : Additive V => (v.toMul : G)) hh
  exact hbv ▸ b.property

omit [Finite G] in
/-- Equality of the kernels on the literal section and its corner. -/
theorem field_four_section_centralizer
    (V L B U : Subgroup G) [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hBV : B ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ PlaneSection.Corner)
    (hB : ∀ v : Additive V, (v.toMul : G) ∈ B ↔ (e v).val 2 2 = 0)
    (a : L) (ha : (a : G) ∈ normalizer (U : Set G)) :
    (∀ b : B, ⁅(a : G),(b : G)⁆ ∈ U) ↔ (a : G) ∈ centralizer (U : Set G) := by
  let t := V.normalizerMonoidHom.rangeRestrict (inclusion hLN a)
  have hd (v : Additive V) : ⁅(a : G),(v.toMul : G)⁆ ∈ U ↔
      (q a).val (e v) - e v ∈ PlaneSection.Corner := by
    have hh := hU (automizerRepresentation V t v - v)
    have hes : e (automizerRepresentation V t v - v) =
        e (automizerRepresentation V t v) - e v := map_sub e _ _
    rw [hes] at hh
    dsimp only [t] at hh
    rw [he] at hh
    change ((a : G) * (v.toMul : G) * (a : G)⁻¹) / (v.toMul : G) ∈ U ↔
      (q a).val (e v) - e v ∈ PlaneSection.Corner at hh
    simpa only [commutatorElement_def,div_eq_mul_inv] using hh
  have hf : (a : G) ∈ centralizer (U : Set G) ↔
      ∀ X ∈ PlaneSection.Corner, (q a).val X = X := by
    constructor
    · intro hac X hX
      obtain ⟨v,rfl⟩ := e.surjective X
      have hv := (hU v).mpr hX
      rw [←he]
      apply congrArg e
      apply Additive.toMul.injective
      apply Subtype.ext
      change (a : G) * (v.toMul : G) * (a : G)⁻¹ = (v.toMul : G)
      rw [←hac _ hv,mul_assoc,mul_inv_cancel,mul_one]
    · intro hx u hu
      let v : Additive V := Additive.ofMul ⟨u,hUV hu⟩
      have hh := e.injective ((he a v).trans (hx _ ((hU v).mp hu)))
      have hh := congrArg (fun z : Additive V => (z.toMul : G)) hh
      change (a : G) * u * (a : G)⁻¹ = u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [hf]
  constructor
  · intro hab
    obtain ⟨c,hc⟩ := (q a).property
    rw [←hc]
    apply PlaneSection.section_trivial_implies_corner_trivial c
    · intro X hX
      obtain ⟨v,rfl⟩ := e.surjective X
      have hu := (mem_normalizer_iff.mp ha _).mp ((hU v).mpr hX)
      have hh := (hU (automizerRepresentation V t v)).mp hu
      rw [he,←hc] at hh
      exact hh
    · intro X hX
      obtain ⟨v,rfl⟩ := e.surjective X
      have hh := (hd v).mp (hab ⟨v.toMul,(hB v).mpr hX⟩)
      rwa [←hc] at hh
  · intro hac b
    let v : Additive V := Additive.ofMul ⟨b,hBV b.property⟩
    apply (hd v).mpr
    have hp := (field_four_plane_pointwise_stabilizer (q a).val (q a).property).mp hac
    exact (PlaneSection.displacement_mem_corner_iff (e v)).mpr ((hB v).mp b.property) _ hp
end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
