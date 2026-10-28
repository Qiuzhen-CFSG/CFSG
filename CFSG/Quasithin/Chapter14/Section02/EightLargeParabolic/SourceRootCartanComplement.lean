module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanComplement
public import Theory.Representation.SL2.EightInvariantRootPlacement
public import Theory.Representation.BinaryConjugationSection.QuotientKernel
public import Theory.GroupTheory.CoprimeCentralQuotientRootPlacement
public import Theory.SpecificGroups.SL2.RootLiftDerived

/-!
# Retaining a prescribed original root and the whole Cartan

The actual degree-eight binary core module makes every root section conjugate
modulo the central involution. Coprime transporter selection retains the
original whole Cartan. Fixed-point lifting and the rank-one root commutator
then place the original root, including its central lift, in a full endpoint
complement with the prescribed quotient marking.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootCartanComplement
variable {G : Type*} [Group G] [Finite G]

private theorem card_map_of_disjoint {E D : Type*} [Group E] [Group D]
    (q : E →* D) (R : Subgroup E) (hk : Disjoint R q.ker) :
    Nat.card (R.map q)=Nat.card R := by
  have hi : Function.Injective (q.subgroupMap R) := by
    apply (q.subgroupMap R).ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hk.le_bot ⟨x.property,congrArg Subtype.val hx⟩)
  exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap R)
    ⟨hi,q.subgroupMap_surjective R⟩).toEquiv).symm

private theorem root_moved {E : Type*} [Group E] [Finite E]
    (q : E →* SL(2,GaloisField 2 3)) (R A : Subgroup E)
    (hR : IsPGroup 2 R) (hR8 : Nat.card R=8) (hkR : Disjoint R q.ker)
    (hA7 : Nat.card (A.map q)=7) (hAR : A≤normalizer (R:Set E)) :
    ⁅R,A⁆=R := by
  obtain ⟨S,hS⟩ := (hR.map q).exists_le_sylow
  have hS8 : Nat.card S=8 := by
    rw [Nat.card_congr (S.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow
      (GaloisField 2 3) 2)).toEquiv,Matrix.SpecialLinearGroup.coe_upperUnipotentSylow,
      Matrix.SpecialLinearGroup.card_upperUnipotent,
      GaloisField.card 2 3 (by decide)]
    rfl
  have he : R.map q=(S:Subgroup SL(2,GaloisField 2 3)) :=
    eq_of_le_of_card_ge hS (by rw [hS8,card_map_of_disjoint q R hkR,hR8])
  have hn : A.map q≤normalizer (S:Set SL(2,GaloisField 2 3)) := by
    change A.map q≤normalizer ((S:Subgroup SL(2,GaloisField 2 3)):Set SL(2,GaloisField 2 3))
    rw [←he]
    exact (map_mono hAR).trans (R.le_normalizer_map q)
  have hm : (⁅R,A⁆).map q=R.map q := by
    rw [map_commutator,he,Matrix.SpecialLinearGroup.sylow_commutator_odd_normalizer S
      (A.map q) hn (by rw [hA7]; decide) (by
        intro hz
        have hh := congrArg (fun U : Subgroup SL(2,GaloisField 2 3) => Nat.card U) hz
        rw [hA7,card_bot] at hh
        omega)]
  have hle : ⁅R,A⁆≤R := le_normalizer_iff_commutator_le_left.mp hAR
  apply le_antisymm hle
  intro x hx
  obtain ⟨y,hy,heq⟩ := hm.symm ▸ mem_map_of_mem q hx
  have hxy : x*y⁻¹∈R⊓q.ker := ⟨R.mul_mem hx (R.inv_mem (hle hy)),by
    change q (x*y⁻¹)=1
    rw [map_mul,map_inv,heq,mul_inv_cancel]⟩
  have hxy' : x=y := mul_inv_eq_one.mp (hkR.le_bot hxy)
  rwa [hxy']

private theorem root_conjugator_of_triple_core (P : Subgroup G)
    (ε : (P ⧸ pCore 2 P) ≃* Theory.PSL2.BinaryGroup 3)
    (hs : SourceTripleModule.HasTripleExtraspecialCore P ε)
    (K : Subgroup P) (hK : (pCore 2 P).IsComplement' K)
    (f : K ≃* Theory.PSL2.BinaryGroup 3)
    (hf : ∀ k:K,f k=ε (QuotientGroup.mk' (pCore 2 P) (k:P)))
    (A R : Subgroup P) (hAK : A≤K) (hA7 : Nat.card A=7)
    (hR : IsPGroup 2 R) (hR8 : Nat.card R=8)
    (hkR : Disjoint R (pCore 2 P)) (hAR : A≤normalizer (R:Set P)) :
    ∃ v∈pCore 2 P⊓centralizer (A:Set P),
      R≤K.map (MulAut.conj v).toMonoidHom := by
  classical
  obtain ⟨hex,Z,hZ,hN,hel,ρ,d,hcoord,hirr,hcard,_⟩ := hs
  let _ := hN
  let _ := hel
  let _ := hex
  let _ := hirr
  let Q := P.pCoreIn 2
  have hQP : Q≤P := pCoreIn_le 2 P
  have hZQ : Z≤Q := by rw [hZ]; exact inf_le_left
  have hZP : Z≤P := hZQ.trans hQP
  have hPN : P≤normalizer Z := by rw [hZ]; exact normalizes_centerIn d.normalized
  let : (Z.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hZP).mpr hPN
  have hZcentral : Z.subgroupOf P≤center P := by
    have hh : Z≤centralizer (P:Set G) := by
      rw [hZ]
      apply centerIn_centralizes_of_card_two _ d.normalized
      rw [centerIn_eq_map_center,card_map_of_injective Q.subtype_injective]
      exact IsExtraspecial.center_order_p 2 Q
    intro z hz
    apply Subgroup.mem_center_iff.mpr
    intro p
    exact Subtype.ext (hh hz p p.property)
  let E := P ⧸ Z.subgroupOf P
  let π : P →* E := QuotientGroup.mk' (Z.subgroupOf P)
  let eSL := ε.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let q₀ : P →* SL(2,GaloisField 2 3) := eSL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hk₀ : q₀.ker=pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ eSL.injective,QuotientGroup.ker_mk']
  have hkQ : q₀.ker=Q.subgroupOf P := by
    rw [hk₀]
    exact (comap_map_eq_self_of_injective P.subtype_injective (pCore 2 P)).symm
  have hZker : π.ker≤pCore 2 P := by
    rw [QuotientGroup.ker_mk',←hk₀,hkQ]
    exact fun z hz => hZQ hz
  let V := Additive (Q ⧸ Z.subgroupOf Q)
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let σ : Representation (ZMod 2) SL(2,GaloisField 2 3) V := ρ.comp eSL.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eSL.symm.toMonoidHom eSL.symm.surjective ρ).mpr hirr
  have hd : Module.finrank (ZMod 2) V=8 := by
    have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=V)
    rw [Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1<2) (hc.symm.trans hcard : 2^Module.finrank (ZMod 2) V=2^8)
  let dSL : BinaryConjugationSection P Q Z (σ.comp q₀) := {d with
    equivariant := by
      intro h u
      simpa only [σ,q₀,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,eSL.symm_apply_apply]
        using d.equivariant h u }
  obtain ⟨q,hq,hqπ,ek,_,hact⟩ := BinaryConjugationSection.exists_quotient_kernel_equiv
    P Q Z q₀ (eSL.surjective.comp (QuotientGroup.mk'_surjective _)) hkQ σ dSL hcoord
  have hqπ' (g:P) : q (π g)=q₀ g := DFunLike.congr_fun hqπ g
  have hker : (pCore 2 P).map π=q.ker := by
    ext v
    constructor
    · rintro ⟨g,hg,rfl⟩
      change q (π g)=1
      rw [hqπ']
      change g∈q₀.ker
      rwa [hk₀]
    · intro hv
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf P) v
      refine ⟨g,?_,rfl⟩
      rw [←hk₀]
      exact (hqπ' g).symm.trans hv
  let s₀ : SL(2,GaloisField 2 3) →* P := K.subtype.comp
    (f.symm.toMonoidHom.comp (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toMonoidHom)
  have hs₀ (g : SL(2,GaloisField 2 3)) : q₀ (s₀ g)=g := by
    apply (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).injective
    change (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3))
      (eSL (QuotientGroup.mk' (pCore 2 P) (s₀ g)))=_
    simp only [eSL,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    exact (hf (f.symm ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)) g))).symm.trans
      (f.apply_symm_apply _)
  have hsr : s₀.range=K := by
    apply le_antisymm
    · rintro x ⟨g,rfl⟩
      exact (f.symm _).property
    · intro k hk
      refine ⟨(Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm (f ⟨k,hk⟩),?_⟩
      change ((f.symm ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3))
        ((Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm (f ⟨k,hk⟩))):K):P)=k
      rw [MulEquiv.apply_symm_apply,MulEquiv.symm_apply_apply]
  let s := π.comp s₀
  have hs (g : SL(2,GaloisField 2 3)) : q (s g)=g := (hqπ' (s₀ g)).trans (hs₀ g)
  have hsk : s.range=K.map π := by rw [MonoidHom.range_comp,hsr]
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hA : IsPGroup 7 A := IsPGroup.of_card (n:=1) (by simpa only [pow_one] using hA7)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pCore 2 P)) :=
    IsPGroup.coprime_card_of_ne 7 2 (by decide) A (pCore 2 P) hA pCore_isPGroup
  have hkRπ : Disjoint R π.ker := hkR.mono_right hZker
  have hRm : Disjoint (R.map π) q.ker := by
    apply disjoint_def.mpr
    rintro v ⟨g,hg,rfl⟩ hv
    have hgQ : g∈pCore 2 P := hk₀ ▸ ((hqπ' g).symm.trans hv : q₀ g=1)
    rw [hkR.le_bot ⟨hg,hgQ⟩,map_one]
  let em : q.ker ≃* Multiplicative V := ek.symm.trans (MulEquiv.multiplicativeAdditive _).symm
  obtain ⟨vbar,hvbar,hRv⟩ := SL2.BinarySmall.root_le_centralizing_conjugate_section_of_eight_irreducible_kernel
    q σ hd em (by
      intro g v
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf P) g
      exact (hact a v).trans (congrArg (fun z => σ z (Additive.ofMul (ek.symm v))) (hqπ' a).symm))
    s hs (R.map π) (hR.map π) ((card_map_of_disjoint π R hkRπ).trans hR8) hRm
    (A.map π) (by rw [hsk]; exact map_mono hAK)
    ((map_mono hAR).trans (R.le_normalizer_map π)) (hA.map π) (by
      have hc : Nat.card q.ker=256 := (Nat.card_congr ek.toEquiv).symm.trans hcard
      rw [hc]
      decide)
  have hAq7 : Nat.card (A.map q₀)=7 :=
    (card_map_of_disjoint q₀ A (by rw [hk₀]; exact (hK.disjoint.symm.mono_left hAK))).trans hA7
  have hmoved := root_moved q₀ R A hR hR8 (by rwa [hk₀]) hAq7 hAR
  obtain ⟨v,hv,hRv'⟩ := root_le_centralizing_conjugate_of_central_quotient
    (pCore 2 P) (Z.subgroupOf P) A R K hZcentral
    (by let := (pCore_isPGroup (p:=2) (G:=P)).isNilpotent; infer_instance)
    hcop hAK hmoved vbar (by rwa [hker]) (by rwa [←hsk])
  exact ⟨v,hv,hRv'⟩

open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- Relative to any prescribed full-core complement containing an actual
seven-subgroup, root placement retains the conjugator in the full original
core centralizing that same seven-subgroup. -/
theorem source_seven_root_conjugator
    (K : Subgroup H) (hK : (pCore 2 H).IsComplement' K)
    (A R : Subgroup H) (hAK : A≤K) (hA7 : Nat.card A=7)
    (hR : IsPGroup 2 R) (hR8 : Nat.card R=8)
    (hkR : Disjoint R (pCore 2 H)) (hAR : A≤normalizer (R:Set H)) :
    ∃ v∈pCore 2 H⊓centralizer (A:Set H),
      R≤K.map (MulAut.conj v).toMonoidHom := by
  let ε := sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
  let f := hK.symm.QuotientMulEquiv.symm.trans ε
  have hf (k:K) : f k=ε (QuotientGroup.mk' (pCore 2 H) (k:H)) := by
    apply congrArg ε
    change hK.symm.QuotientMulEquiv.symm k=QuotientGroup.mk' (pCore 2 H) (k:H)
    apply hK.symm.QuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']
  exact root_conjugator_of_triple_core H ε
    (SourceTripleModule.source_core_triple hG T hempty hM hu hmany hcard e H hH eR)
    K hK f hf A R hAK hA7 hR hR8 hkR hAR

/-- Every prescribed original eight-root normalized by the original whole
Cartan lies with it in a complement to the full H-core. The restriction
of the prescribed source quotient is retained as the rank-one marking. -/
theorem source_root_cartan_complement
    (c : CompatibleCartans ![locals T M Mc H 1,locals T M Mc H 0]
      (reducedSylow ![locals T M Mc H 1,locals T M Mc H 0] (T : Subgroup G)))
    (R : Subgroup G) (hRH : R≤H) (hR : IsPGroup 2 R) (hR8 : Nat.card R=8)
    (hkR : Disjoint R (H.pCoreIn 2))
    (hCR : c.D 0 ⊔ c.D 1≤normalizer (R:Set G)) :
    ∃ K : Subgroup H, (pCore 2 H).IsComplement' K ∧
      c.D 0 ⊔ c.D 1≤K.map H.subtype ∧ R≤K.map H.subtype ∧
      ∃ f : K ≃* Theory.PSL2.BinaryGroup 3,
        ∀ k:K,f k=(sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
          (QuotientGroup.mk' (pCore 2 H) (k:H)) := by
  obtain ⟨K,hK,hCK,_,_⟩ := SourceCartanComplement.source_cartan_complement
    hG T hempty hM hu hmany hcard e H hH eR c
  have hCH : c.D 0 ⊔ c.D 1≤H := hCK.trans (map_subtype_le K)
  let A := (c.D 0 ⊔ c.D 1).subgroupOf H
  have hAK : A≤K := by
    intro a ha
    obtain ⟨k,hk,he⟩ := hCK ha
    exact (Subtype.ext he : k=a) ▸ hk
  have hA7 : Nat.card A=7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCH).toEquiv]
    have hc := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
    rw [cartan,card_map_of_injective middleMap_injective,
      Nat.card_congr (subgroupOfEquivOfLe c.joint_le).toEquiv] at hc
    exact hc
  let R₀ := R.subgroupOf H
  have hR₀ : IsPGroup 2 R₀ := hR.of_equiv (subgroupOfEquivOfLe hRH).symm
  have hR₀8 : Nat.card R₀=8 := (Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv).trans hR8
  have hkR₀ : Disjoint R₀ (pCore 2 H) := by
    apply disjoint_def.mpr
    intro r hr hq
    exact Subtype.ext (hkR.le_bot ⟨hr,mem_map_of_mem H.subtype hq⟩)
  have hAR₀ : A≤normalizer (R₀:Set H) := by
    intro a ha
    exact R.le_normalizer_comap H.subtype (hCR ha)
  let ε := sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
  obtain ⟨v,hv,hRK'⟩ := source_seven_root_conjugator
    hG T hempty hM hu hmany hcard e H hH eR K hK A R₀ hAK hA7 hR₀ hR₀8 hkR₀ hAR₀
  let K' := K.map (MulAut.conj v).toMonoidHom
  have hK' : (pCore 2 H).IsComplement' K' := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [card_map_of_injective (MulAut.conj v).injective]
      exact hK.card_mul_card
    · have hh := disjoint_map (f:=(MulAut.conj v).toMonoidHom) (MulAut.conj v).injective hK.disjoint
      have hn : (pCore 2 H).map (MulAut.conj v).toMonoidHom=pCore 2 H :=
        Subgroup.Normal.map_conj_eq (pCore 2 H) v
      rwa [hn] at hh
  have hAK' : A≤K' := by
    intro a ha
    refine ⟨a,hAK ha,?_⟩
    change v*a*v⁻¹=a
    rw [←hv.2 a ha,mul_inv_cancel_right]
  let f' := hK'.symm.QuotientMulEquiv.symm.trans ε
  refine ⟨K',hK',?_,?_,f',?_⟩
  · rw [←map_subgroupOf_eq_of_le hCH]
    exact map_mono hAK'
  · rw [←map_subgroupOf_eq_of_le hRH]
    exact map_mono hRK'
  · intro k
    apply congrArg ε
    change hK'.symm.QuotientMulEquiv.symm k=QuotientGroup.mk' (pCore 2 H) (k:H)
    apply hK'.symm.QuotientMulEquiv.injective
    rw [MulEquiv.apply_symm_apply,quotientMulEquiv_mk_apply_of_isComplement']

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootCartanComplement
