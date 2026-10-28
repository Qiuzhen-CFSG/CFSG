module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosureLayers
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperNatural

/-!
# The literal upper natural section in the nonnormal ordinary A₆ branch

Keep S₂=V(U_H∩U_Hᵍ) as the quotient denominator. The pair kernel is
WWᵍ; the two images are complementary, and the marked four-group has
its moved space inside its fixed W-image. The original Borel preserves
that image. The proved projective criterion supplies natural SL₂(4)
coordinates with their actual conjugation action.
Source: Aschbacher–Smith13.5.14(4),13.5.22; G.2.4(6), pp.334,919,924.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosureUpper
open Section08.SourceCompletion NormalBranch
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks SourceFiveModule SourceUpperStructure
open ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive.Recognition
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
open ClosureLayers
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem upper_elementary (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hg : g.val ∈ NormalBranch.K D g.val) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    [((second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)).Normal] :
    IsElementaryAbelian 2 ((NormalBranch.K D g.val).pCoreIn 2 ⧸
      (second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)) := by
  let S := (NormalBranch.K D g.val).pCoreIn 2
  let W := D.UH ⊓ S
  let X := conjugate W g.val
  let q := QuotientGroup.mk' ((second D g.val).subgroupOf S)
  have hsplit : S=W⊔X := ClosureLayers.core_generated d h e htilde hU g hg hK hp a hi
  have hXS : X ≤ S := (conjugate_marked g hg).le.trans inf_le_right
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf (SourceCoreProduct.core_normalizes_closure d h e g hK a hi) S.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hSX : S ≤ normalizer (X : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) hSW).trans
      (W.le_normalizer_map (MulAut.conj g.val⁻¹).toMonoidHom)
    change conjugate S g.val ≤ normalizer (X : Set G) at hh
    rwa [conjugate_core g hg] at hh
  have hWX : ⁅W,X⁆ ≤ second D g.val := by
    have hc := le_inf (le_normalizer_iff_commutator_le_left.mp (hXS.trans hSW))
      (le_normalizer_iff_commutator_le_right.mp ((show W≤S from inf_le_right).trans hSX))
    exact hc.trans ((inf_le_inf inf_le_left (map_mono inf_le_left)).trans
      (show D.UH⊓conjugate D.UH g.val≤second D g.val from le_sup_right))
  have hpoint : D.V₁ ≤ D.V := h.point_lt.le.trans h.plus_le
  have hsqU (u : G) (hu : u∈D.UH) : u^2∈D.V₁ := by
    let : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
    exact h.frattini_UH_le_point
      ⟨(⟨u,hu⟩:D.UH)^2,pth_power_mem_frattini_of_isPGroup _,rfl⟩
  have hsqW : ∀w∈W,w^2∈D.V := fun w hw => hpoint (hsqU w hw.1)
  have hsqX : ∀x∈X,x^2∈D.V := by
    rintro x ⟨w,hw,rfl⟩
    have hh := mem_map_of_mem (MulAut.conj g.val⁻¹).toMonoidHom (hsqW w hw)
    have he : D.V.map (MulAut.conj g.val⁻¹).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.V : Set G)).inv_mem (d.normalizes_V (mem_sup_left g.property)))
    rw [he] at hh
    simpa only [map_pow] using hh
  have hsq : ∀x:S ⧸ (second D g.val).subgroupOf S,x^2=1 := by
    intro x
    obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hprod : s.val ∈ (W:Set G)*(X:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ (hXS.trans hSW),←hsplit]
      exact s.property
    obtain ⟨w,hw,x,hx,hwx⟩ := hprod
    let wS : S := ⟨w,hw.2⟩
    let xS : S := ⟨x,hXS hx⟩
    have hs : wS*xS=s := Subtype.ext hwx
    have hqw : (q wS)^2=1 := by
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (mem_sup_left (hsqW w hw))
    have hqx : (q xS)^2=1 := by
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (mem_sup_left (hsqX x hx))
    have hcomm : Commute (q wS) (q xS) := by
      change q wS*q xS=q xS*q wS
      rw [←commutatorElement_eq_one_iff_mul_comm,←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hWX (commutator_mem_commutator hw hx))
    change (q s)^2=1
    rw [←hs,map_mul,hcomm.mul_pow,hqw,hqx,mul_one]
  exact {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
/-- The action descends to the exact A₅ quotient, with the original quotient map. -/
theorem upper_action (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val ∈ NormalBranch.K D g.val) (hK : NormalBranch.K D g.val ≤ D.L)
    (hL : D.L₁ ≤ NormalBranch.K D g.val) (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    let := second_normal_in_core d h g hK
    let := upper_elementary d h e htilde hU g hg hK hp a hi
    ∃ (σ : Representation (ZMod 2) (alternatingGroup (Fin 5))
        (Additive ((NormalBranch.K D g.val).pCoreIn 2 ⧸
          (second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2))))
      (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
        ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val) (σ.comp (restrictedActor d hK a hi))),
      ∀s:(NormalBranch.K D g.val).pCoreIn 2,(c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)) s) := by
  let := second_normal_in_core d h g hK
  let := upper_elementary d h e htilde hU g hg hK hp a hi
  have hk : (restrictedActor d hK a hi).ker =
      ((NormalBranch.K D g.val).pCoreIn 2).subgroupOf (NormalBranch.K D g.val) := by
    rw [restrictedActor_ker_eq_twoCore d hK a hi e]
    exact (comap_map_eq_self_of_injective (NormalBranch.K D g.val).subtype_injective _).symm
  exact Representation.BinaryConjugationSection.exists_canonical
    (NormalBranch.K D g.val) ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val)
    (pCoreIn_le 2 _) (second_le_core d h g hgn hK hL a hi)
    (pair_normalizes_core g) (second_normalized d h g hK)
    (restrictedActor d hK a hi) (restrictedActor_surjective d hK a hi) hk

theorem upper_root_bounds (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) (NormalBranch.K D g.val) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val) ρ)
    (u : NormalBranch.K D g.val) (hu : u.val ∈ D.UH) :
    LinearMap.range (ρ u-1) ≤ c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) ∧
    ∀v∈c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2),ρ u v=v := by
  have hUS : ⁅D.UH,(NormalBranch.K D g.val).pCoreIn 2⁆ ≤
      D.UH⊓(NormalBranch.K D g.val).pCoreIn 2 :=
    le_inf (le_normalizer_iff_commutator_le_left.mp
      (SourceCoreProduct.core_normalizes_closure d h e g hK a hi))
      (le_normalizer_iff_commutator_le_right.mp
        ((show D.UH≤NormalBranch.K D g.val from le_sup_left).trans (pair_normalizes_core g)))
  have hUW : ⁅D.UH,D.UH⊓(NormalBranch.K D g.val).pCoreIn 2⁆ ≤ second D g.val :=
    ((commutator_mono le_rfl inf_le_left).trans
      (derived_le_of_frattini_image_le h.g2_hypothesis.U_isPGroup h.frattini_UH_le_point)).trans
        ((h.point_lt.le.trans h.plus_le).trans le_sup_left)
  exact ⟨c.displacement_range_le_imageSpace_of_commutator_le D.UH _ hUS u hu,
    c.fixed_on_imageSpace_of_commutator_le D.UH _ hUW u hu⟩

theorem upper_marked_complement (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val∈NormalBranch.K D g.val)
    (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) (NormalBranch.K D g.val) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val) ρ) :
    IsCompl (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2))
      (c.imageSpace (conjugate (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) g.val)) ∧
    c.imageSpace (conjugate (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) g.val) =
      (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2)).map
        (ρ (⟨g.val,hg⟩:NormalBranch.K D g.val)⁻¹) := by
  let S := (NormalBranch.K D g.val).pCoreIn 2
  let W := D.UH⊓S
  let X := conjugate W g.val
  have hVW : D.Vplus≤W := le_inf (le_conjugateSpanBy _ _)
    (h.plus_le.trans (module_le_core d h (seed_identity d h) g hK hL a hi))
  have hVgX : conjugate D.Vplus g.val≤X := map_mono hVW
  have hVV := SourceUpperAction.seed_join d h g hgn
  have hprod : (D.V:Set G)=(D.Vplus:Set G)*(conjugate D.Vplus g.val:Set G) := by
    rw [←hVV]
    apply coe_mul_of_right_le_normalizer_left
    have hnorm : D.V≤normalizer (D.Vplus:Set G) := by
      let := h.elementary
      exact ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative D.V)).trans
        (centralizer_le h.plus_le)).trans (Subgroup.centralizer_le_normalizer _)
    exact (le_sup_right.trans hVV.le).trans hnorm
  have hES : D.UH⊓conjugate D.UH g.val≤S :=
    le_sup_right.trans (second_le_core d h g hgn hK hL a hi)
  have hEX : D.UH⊓conjugate D.UH g.val≤X := by
    change D.UH⊓conjugate D.UH g.val≤conjugate (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) g.val
    rw [conjugate_marked g hg]
    exact le_inf inf_le_right hES
  have hsecondprod : (second D g.val:Set G) =
      (D.V:Set G)*(D.UH⊓conjugate D.UH g.val : Subgroup G) :=
    coe_mul_of_right_le_normalizer_left _ _
      ((hES.trans (core_centralizes_module d h e g hK a hi)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hdis : Disjoint (c.imageSpace W) (c.imageSpace X) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hv'
    obtain ⟨b,hb,hbv⟩ := (c.mem_imageSpace_iff _ _).mp hv
    obtain ⟨x,hx,hxv⟩ := (c.mem_imageSpace_iff _ _).mp hv'
    have he : b.val*x.val⁻¹∈second D g.val := by
      apply (c.coordinates_eq_one_iff (b*x⁻¹)).mp
      rw [map_mul,map_inv,Multiplicative.toAdd.injective (hbv.trans hxv.symm),mul_inv_cancel]
    change b.val*x.val⁻¹∈(second D g.val:Set G) at he
    rw [hsecondprod] at he
    obtain ⟨z,hz,t,ht,hzt⟩ := he
    rw [hprod] at hz
    obtain ⟨v₀,hv₀,v₁,hv₁,hvv⟩ := hz
    have heq : v₀⁻¹*b.val=v₁*t*x.val := by
      rw [←hvv] at hzt
      change v₀*v₁*t=b.val*x.val⁻¹ at hzt
      calc
        _ = v₀⁻¹*((b.val*x.val⁻¹)*x.val) := by group
        _ = v₀⁻¹*((v₀*v₁*t)*x.val) := by rw [←hzt]
        _ = _ := by group
    have hw : v₀⁻¹*b.val∈W := W.mul_mem (W.inv_mem (hVW hv₀)) hb
    have hx' : v₀⁻¹*b.val∈X := by
      rw [heq]
      exact X.mul_mem (X.mul_mem (hVgX hv₁) (hEX ht)) hx
    have hker : v₀⁻¹*b.val∈second D g.val :=
      mem_sup_right ⟨hw.1,(map_mono (show W≤D.UH from inf_le_left)) hx'⟩
    have hbV : b.val∈second D g.val := by
      have hh := (second D g.val).mul_mem (mem_sup_left (h.plus_le hv₀)) hker
      simpa only [mul_inv_cancel_left] using hh
    exact hbv.symm.trans (show (c.coordinates b).toAdd=0 from
      congrArg Multiplicative.toAdd ((c.coordinates_eq_one_iff b).mpr hbV))
  refine ⟨⟨hdis,?_⟩,c.imageSpace_conjBy W inf_le_right (⟨g.val,hg⟩:NormalBranch.K D g.val)⁻¹⟩
  let f : Subgroup (Multiplicative E)≃oSubmodule (ZMod 2) E :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  change Codisjoint (f ((W.subgroupOf S).map c.coordinates))
    (f ((X.subgroupOf S).map c.coordinates))
  rw [codisjoint_iff,←f.map_sup,←f.map_top]
  apply congrArg f
  apply codisjoint_iff.mp
  apply Subgroup.codisjoint_map c.onto
  have hcod (B : Subgroup G) (hb : B=W⊔X) : Codisjoint (W.subgroupOf B) (X.subgroupOf B) := by
    subst B
    exact codisjoint_subgroupOf_sup _ _
  exact hcod S (ClosureLayers.core_generated d h e htilde hU g hg hK hp a hi)

theorem local_image_eq_normalizer (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (D.L₁.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)=
      normalizer (((D.UH.subgroupOf (NormalBranch.K D g.val)).map
        (restrictedActor d hK a hi)) : Set (alternatingGroup (Fin 5))) := by
  let J := NormalBranch.K D g.val
  let U := D.UH.subgroupOf J
  let f := restrictedActor d hK a hi
  let B := (D.L₁.subgroupOf J).map f
  let N := normalizer (U.map f : Set (alternatingGroup (Fin 5)))
  have hBN : B≤N := by
    have hLU : D.L₁≤normalizer (D.UH:Set G) :=
      (le_sup_left.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
    have hl : D.L₁.subgroupOf J≤normalizer (U:Set J) := by
      intro l hl
      apply mem_normalizer_iff.mpr
      intro u
      exact mem_normalizer_iff.mp (hLU hl) u.val
    exact (map_mono hl).trans (U.le_normalizer_map f)
  have hBcard : Nat.card B=12 := SourceUpperBorel.local_image_card d h g hK hL a hi
  have hUcard : Nat.card (U.map f)=4 :=
    ClosureLayers.closure_image_card d h e htilde hU g hK a hi
  have hBindex : B.index=5 := by
    have hh := B.card_mul_index
    rw [hBcard,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hNne : N≠⊤ := by
    intro he
    let : (U.map f).Normal := normalizer_eq_top_iff.mp he
    have hUp : IsPGroup 2 (U.map f) :=
      ((show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).comap_subtype).map f
    have hcore : U.map f≤pCore 2 (alternatingGroup (Fin 5)) := le_sSup ⟨inferInstance,hUp⟩
    rw [FivePair.alternating_five_twoCore] at hcore
    have hz := le_bot_iff.mp hcore
    rw [hz,card_bot] at hUcard
    contradiction
  rcases eq_or_lt_of_le hBN with he|hlt
  · exact he
  · have hd := index_dvd_of_le hlt.le
    rw [hBindex] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with he|he
    · exact (hNne (index_eq_one.mp he)).elim
    · have hh := index_strictAnti hlt
      rw [he,hBindex] at hh
      omega

theorem upper_marked_model (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    ∃ m : alternatingGroup (Fin 5) ≃* SL(2,F4),
      (((D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)).map
        m.toMonoidHom) = RootGroup F4 standardPoint.val := by
  let U := (D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)
  have hUp : IsPGroup 2 U :=
    ((show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).comap_subtype).map _
  have hc : Nat.card U=4 := ClosureLayers.closure_image_card d h e htilde hU g hK a hi
  have hidx : U.index=15 := by
    have hh := U.card_mul_index
    rw [hc,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  let P : Sylow 2 (alternatingGroup (Fin 5)) := hUp.toSylow (by rw [hidx];decide)
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four field_card
  let e₀ : alternatingGroup (Fin 5)≃*SL(2,F4) :=
    eA.symm.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F:=F4)).symm
  let R : Sylow 2 SL(2,F4) := P.mapSurjective (f:=e₀.toMonoidHom) e₀.surjective
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq SL(2,F4) R
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F4 2)
  refine ⟨e₀.trans (MulAut.conj b),?_⟩
  rw [root_standardPoint]
  have hh := congrArg (fun Q:Sylow 2 SL(2,F4)=>(Q:Subgroup SL(2,F4))) hb
  change (U.map e₀.toMonoidHom).map (MulAut.conj b).toMonoidHom =
    Matrix.SpecialLinearGroup.upperUnipotent F4 at hh
  rw [map_map] at hh
  exact hh

theorem mover_not_borel (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val∈NormalBranch.K D g.val)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    restrictedActor d hK a hi ⟨g.val,hg⟩ ∉ normalizer
      (((D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)) :
        Set (alternatingGroup (Fin 5))) := by
  intro hh
  rw [←local_image_eq_normalizer d h e htilde hU g hK hL a hi] at hh
  obtain ⟨l,hl,he⟩ := hh
  let k : NormalBranch.K D g.val := ⟨g.val,hg⟩
  have hdiff : l⁻¹*k∈(restrictedActor d hK a hi).ker := by
    change restrictedActor d hK a hi (l⁻¹*k)=1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  rw [restrictedActor_ker_eq_twoCore d hK a hi e] at hdiff
  have hs : l.val⁻¹*g.val∈D.Gz :=
    ((core_centralizes_module d h e g hK a hi).trans
      (centralizer_le (h.point_lt.le.trans h.plus_le)))
        (mem_map_of_mem (NormalBranch.K D g.val).subtype hdiff)
  have hlG : l.val∈D.Gz := ((map_subtype_le _).trans inf_le_right) hl
  apply hgn
  simpa only [mul_inv_cancel_left] using D.Gz.mul_mem hlG hs

theorem upper_borel_invariant (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val) (σ.comp (restrictedActor d hK a hi)))
    (x : alternatingGroup (Fin 5))
    (hx : x∈normalizer (((D.UH.subgroupOf (NormalBranch.K D g.val)).map
      (restrictedActor d hK a hi)) : Set (alternatingGroup (Fin 5)))) :
    (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2)).map (σ x)=
      c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) := by
  rw [←local_image_eq_normalizer d h e htilde hU g hK hL a hi] at hx
  obtain ⟨l,hl,rfl⟩ := hx
  let W := D.UH⊓(NormalBranch.K D g.val).pCoreIn 2
  have hnW : D.L₁≤normalizer (W:Set G) :=
    (le_inf ((le_sup_left.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
      (hL.trans (pair_normalizes_core g))).trans inf_normalizer_le_normalizer_inf
  have he : W.conjBy l.val=W := mem_normalizer_iff_map_conj_eq.mp (hnW hl)
  have hm := c.imageSpace_conjBy W inf_le_right l
  rw [he] at hm
  exact hm.symm
theorem natural_coordinates (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val∈NormalBranch.K D g.val)
    (hK : NormalBranch.K D g.val ≤ D.L) (hL : D.L₁ ≤ NormalBranch.K D g.val)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val) (σ.comp (restrictedActor d hK a hi))) :
    let := (ZMod.algebra F4 2).toModule
    ∃ (m : alternatingGroup (Fin 5)≃*SL(2,F4)) (s : ℕ)
      (q : E≃ₗ[ZMod 2](Fin s→Fin 2→F4)),
      ∀x v j,q (σ x v) j=Matrix.mulVec (m x).val (q v j) := by
  let := (ZMod.algebra F4 2).toModule
  let f := restrictedActor d hK a hi
  let W := D.UH⊓(NormalBranch.K D g.val).pCoreIn 2
  let U := (D.UH.subgroupOf (NormalBranch.K D g.val)).map f
  let k : NormalBranch.K D g.val := ⟨g.val,hg⟩
  obtain ⟨m,hm⟩ := upper_marked_model d h e htilde hU g hK a hi
  let τ := σ.comp m.symm.toMonoidHom
  let t := m (f k⁻¹)
  have hne : standardPoint.val≠standardPoint.val.map (Representation.specialLinearNatural 2 t) := by
    intro he
    have ht := mem_root_normalizer_of_map_eq standardPoint.val t he.symm
    change t∈normalizer (RootGroup F4 standardPoint.val:Set SL(2,F4)) at ht
    rw [←hm,←map_normalizer_eq_of_bijective _ m.bijective] at ht
    have hi' := mem_map_equiv.mp ht
    change m.symm (m (f k⁻¹))∈normalizer (U:Set (alternatingGroup (Fin 5))) at hi'
    rw [m.symm_apply_apply,map_inv] at hi'
    exact mover_not_borel d h e htilde hU g hgn hg hK hL a hi
      (by simpa only [inv_inv] using (normalizer (U:Set (alternatingGroup (Fin 5)))).inv_mem hi')
  obtain ⟨hcompl,hmove⟩ := upper_marked_complement d h e htilde hU g hgn hg hK hL hp a hi
    (σ.comp f) c
  have ht : τ t=σ (f k⁻¹) := by
    change σ (m.symm (m (f k⁻¹)))=σ (f k⁻¹)
    rw [m.symm_apply_apply]
  have hcompl' : IsCompl (c.imageSpace W) ((c.imageSpace W).map (τ t)) := by
    rw [ht]
    exact hmove ▸ hcompl
  have hroot : ∀x∈RootGroup F4 standardPoint.val,
      LinearMap.range (τ x-1)≤c.imageSpace W ∧ ∀v∈c.imageSpace W,τ x v=v := by
    intro x hx
    rw [←hm] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    obtain ⟨u,hu,rfl⟩ := hy
    have hh := upper_root_bounds d h e g hK a hi (σ.comp f) c u hu
    simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,m.symm_apply_apply] using hh
  have hN : ∀x∈normalizer (RootGroup F4 standardPoint.val:Set SL(2,F4)),
      (c.imageSpace W).map (τ x)=c.imageSpace W := by
    intro x hx
    rw [←hm,←map_normalizer_eq_of_bijective _ m.bijective] at hx
    exact upper_borel_invariant d h e htilde hU g hK hL a hi σ c (m.symm x)
      (mem_map_equiv.mp hx)
  obtain ⟨φ,_,_,hcriterion⟩ := exists_orbit_criterion τ standardPoint (c.imageSpace W) t
    hne hcompl' hN hroot
  obtain ⟨s,q,hq⟩ := ChapterG.Section01.SL2FourRecognition.naturalCopies hcriterion
  refine ⟨m,s,q,?_⟩
  intro x v j
  simpa only [τ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,m.symm_apply_apply] using hq (m x) v j
/-- The original hypotheses construct the pair and its literal natural upper section. -/
theorem exists_source_natural_upper (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬IsMulCommutative D.UH) :
    ∃ (a : alternatingGroup (Fin 6)) (g : D.L) (_hgn : g.val∉D.Gz)
      (hg : g.val∈NormalBranch.K D g.val) (hK : NormalBranch.K D g.val≤D.L)
      (_hL : D.L₁≤NormalBranch.K D g.val) (hp : IsPPerfect 2 (NormalBranch.K D g.val))
      (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
        FivePair.five.map (MulAut.conj a.val).toMonoidHom),
      let := second_normal_in_core d h g hK
      let := upper_elementary d h e htilde hU g hg hK hp a hi
      let := (ZMod.algebra F4 2).toModule
      ∃ (σ : Representation (ZMod 2) (alternatingGroup (Fin 5))
          (Additive ((NormalBranch.K D g.val).pCoreIn 2 ⧸
            (second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2))))
        (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
          ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val) (σ.comp (restrictedActor d hK a hi)))
        (m : alternatingGroup (Fin 5)≃*SL(2,F4)) (s : ℕ)
        (q : Additive ((NormalBranch.K D g.val).pCoreIn 2 ⧸
          (second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2))≃ₗ[ZMod 2](Fin s→Fin 2→F4)),
        (∀u:(NormalBranch.K D g.val).pCoreIn 2,(c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)) u)) ∧
        ∀x v j,q (σ x v) j=Matrix.mulVec (m x).val (q v j) := by
  obtain ⟨a,g,hgn,hg,hK,hL,hp,_,_,hi⟩ := ClosurePair.exists_source_pair_of_tilde d h e htilde hU
  refine ⟨a,g,hgn,hg,hK,hL,hp,hi,?_⟩
  let := second_normal_in_core d h g hK
  let := upper_elementary d h e htilde hU g hg hK hp a hi
  let := (ZMod.algebra F4 2).toModule
  obtain ⟨σ,c,hc⟩ := upper_action d h e htilde hU g hgn hg hK hL hp a hi
  obtain ⟨m,s,q,hq⟩ := natural_coordinates d h e htilde hU g hgn hg hK hL hp a hi σ c
  exact ⟨σ,c,m,s,q,hc,hq⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ClosureUpper
