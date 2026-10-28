module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearOrbitPair
public import Theory.Representation.PSL3Two.NaturalDualSum
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearFullQuotient
public import Theory.Representation.PSL3Two.FanoSylowFixed
public import Theory.Representation.ElementarySeedSaturation

/-!
# The whole original linear orbit module

The component fills the full two-core quotient. A point- or line-core orbit
therefore has the same Sylow fixed plane as the original omega-center: its
four fixed vectors embed into that center of order four. The orbit contains
the center and is invariant under the full join, so it is the whole module.
Together with the opposite-natural comparison, this proves all the actual
six-dimensional module alternatives in the linear branch of 13.4.7.
The preceding Structural1222 and Source1332OneTwo premises remain explicit.
Source: Aschbacher–Smith 13.4.7, printed pp.900–901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open BinaryLinearThree.FanoDecomposition Representation.BinaryOffender
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original omega orbit is natural plus dual, point-core, or line-core,
under one marking of its actual component and both original parabolics. -/
theorem original_pair_linear_whole_module
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let X := A ⊔ B
    let C := K.map X.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z X
    ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := Representation.elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion
          ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))
      ∃ e : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
        let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
        (A.subgroupOf C).map f = Matrix.PSL3Two.pointParabolicSL ∧
        (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL ∧
        ((T : Subgroup G).subgroupOf C).map f = Matrix.PSL3Two.borelSL ∧
        (Nonempty (Representation.Equiv
            ((BinaryLinearThree.W.prod BinaryLinearThree.W.dual).comp f) ρ) ∨
          Nonempty (Representation.Equiv (BinaryLinearThree.U₂.comp f) ρ) ∨
          Nonempty (Representation.Equiv (lineCoreRepresentation.comp f) ρ)) ∧
        Nat.card U = 64 := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hred.elementary
  let he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom (subgroupOfEquivOfLe hUX).symm.injective
  let := he
  obtain ⟨e,hA,hB,hS⟩ := original_pair_linear_parabolic_pair h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨he₁,he₂,hm₁,hm₂⟩ := original_pair_linear_same_marking_models h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK e hA hB
  let := he₁
  let := he₂
  refine ⟨he,e,hA,hB,hS,?_⟩
  have hs := original_pair_component_fixed_line_spans h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  have hkernel := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).2.2.2
  let Q := X.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := hkernel.symm.le.trans inf_le_left
  have hQU : Q ≤ centralizer (U : Set G) := hkernel.symm.le.trans inf_le_right
  have hUC : U ≤ Q := by
    intro u hu
    exact mem_map_of_mem X.subtype (hred.le_pCore (show (⟨u,hUX hu⟩ : X) ∈ U.subgroupOf X from hu))
  have hUT : U ≤ (T : Subgroup G) := hUC.trans hQT
  have hgen := (original_pair_linear_core_supplement h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK).2
  change C ⊔ Q = X at hgen
  have hgenX : K ⊔ pCore 2 X = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have hZcard := (original_pair_fixed_lines h structural D m hout
    hindexL hindexA hindexB (pair_fixed_subgroups_ne hTA hTB eA eB hne hres)).1
  have saturate (P : Subgroup G) [IsElementaryAbelian 2 P]
      (hPU : P ≤ U) (hCP : C ≤ normalizer (P : Set G))
      {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
      (eP : Representation.Equiv (σ.comp f)
        (Representation.elementaryRepresentation (p := 2)
          (P.normalizerMonoidHom.comp (inclusion hCP))))
      (hcard : Nat.card (fixedSpace σ Matrix.PSL3Two.borelSL) = 4) :
      Nonempty (Representation.Equiv (σ.comp f)
        (Representation.elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion
            ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X)))))) := by
    have hQP : Q ≤ centralizer (P : Set G) := hQU.trans (centralizer_le hPU)
    have hXP : X ≤ normalizer (P : Set G) := by
      rw [←hgen]
      exact sup_le hCP (hQP.trans (Subgroup.centralizer_le_normalizer _))
    have hTsup : (T : Subgroup G) ≤ ((T : Subgroup G) ⊓ C) ⊔ centralizer (P : Set G) := by
      intro t ht
      obtain ⟨c,hc,q,hq,hcq⟩ := mem_sup_of_normal_right.mp
        (hgenX ▸ mem_top (⟨t,(hTA.trans le_sup_left) ht⟩ : X))
      have hqT : q.val ∈ (T : Subgroup G) := hQT (mem_map_of_mem X.subtype hq)
      have hcT : c.val ∈ (T : Subgroup G) := by
        have hh := congrArg (fun x : X => x.val) hcq
        change c.val * q.val = t at hh
        rw [←mul_div_cancel_right c.val q.val]
        exact (T : Subgroup G).div_mem (hh ▸ ht) hqT
      have hcC : c.val ∈ C := mem_map_of_mem X.subtype hc
      have hqP := hQP (mem_map_of_mem X.subtype hq)
      have hh := ((T : Subgroup G) ⊓ C ⊔ centralizer (P : Set G)).mul_mem
        (mem_sup_left ⟨hcT,hcC⟩) (mem_sup_right hqP)
      have heq : c.val * q.val = t := congrArg (fun x : X => x.val) hcq
      rw [←heq]
      exact hh
    have hUP : U ≤ P := Representation.elementary_seed_saturation
      (T : Subgroup G) X C P (hPU.trans hUT) hCP hXP hTsup f σ eP (by rw [hS,hZcard]; exact hcard)
    let i : Representation.IntertwiningMap
        (Representation.elementaryRepresentation (p := 2)
          (P.normalizerMonoidHom.comp (inclusion hCP)))
        (Representation.elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion
            ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))) := {
      toLinearMap := (inclusion hPU).toAdditive.toZModLinearMap 2
      isIntertwining' c := by apply LinearMap.ext; intro v; rfl }
    have hi : Function.Bijective i := ⟨inclusion_injective hPU, fun v =>
      ⟨Additive.ofMul ⟨v.toMul.val,hUP v.toMul.property⟩,rfl⟩⟩
    exact ⟨eP.trans (i.ofBijective hi)⟩
  have card_of_model {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
      (eP : Representation.Equiv (σ.comp f)
        (Representation.elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion
            ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))))
      (hc : Nat.card M = 64) : Nat.card U = 64 :=
    (Nat.card_congr eP.toLinearEquiv.toEquiv).symm.trans hc
  have hpfix : Nat.card (fixedSpace BinaryLinearThree.U₂ Matrix.PSL3Two.borelSL) = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    have hh := BinaryLinearThree.FanoSylowFixed.point_finrank flagSylow
    rw [flagSylow_coe,markedFlag_stabilizer] at hh
    rw [hh]
    rfl
  have hlfix : Nat.card (fixedSpace lineCoreRepresentation Matrix.PSL3Two.borelSL) = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    have hh := BinaryLinearThree.FanoSylowFixed.line_finrank flagSylow
    rw [flagSylow_coe,markedFlag_stabilizer] at hh
    rw [hh]
    rfl
  rcases hm₁ with hn | hc
  · obtain ⟨a⟩ := hn
    rcases hm₂ with hn | hc
    · obtain ⟨b⟩ := hn
      obtain ⟨_,he,hcard⟩ := BinaryLinearThree.NaturalDualSum.subgroup_sum f hf
        ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))
        (le_normalizer_conjugateSpanBy _ C) (le_normalizer_conjugateSpanBy _ C)
        hs.symm a b
      exact ⟨Or.inl he,hcard⟩
    · obtain ⟨b⟩ := hc
      obtain ⟨eU⟩ := saturate _ (conjugateSpanBy_mono inf_le_left (map_subtype_le K))
        (le_normalizer_conjugateSpanBy _ C) lineCoreRepresentation b hlfix
      refine ⟨Or.inr (Or.inr ⟨eU⟩),card_of_model _ eU ?_⟩
      let : Nonempty Line := ⟨Matrix.PSL3Two.flagLine⟩
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        BinaryPermutation.finrank_core,Matrix.PSL3Two.Fano.card_line]
      rfl
  · obtain ⟨a⟩ := hc
    obtain ⟨eU⟩ := saturate _ (conjugateSpanBy_mono inf_le_left (map_subtype_le K))
      (le_normalizer_conjugateSpanBy _ C) BinaryLinearThree.U₂ a hpfix
    refine ⟨Or.inr (Or.inl ⟨eU⟩),card_of_model _ eU ?_⟩
    let : Nonempty BinaryLinearThree.Point := ⟨Matrix.PSL3Two.flagPoint⟩
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_core,Matrix.PSL3Two.Fano.card_point]
    rfl

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
