module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpacesLines
public import Theory.Representation.CentralCoverOriginalAction.Quadratic
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutionCentralizer
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Cubic-fixed two-core elements on the original natural layer

An element of T fixing Z_S pointwise induces a field-linear action on the
natural layer: semilinearity and the nonzero fixed field line kill its field
automorphism. If the element commutes with the original cubic, its action
is trivial. First prove this for involutions, using determinant one and
SL2(4) = A5; induction on a two-power annihilating exponent proves the
whole two-element assertion.

Consequently C_{O2(N)}(c) centralizes the natural layer. This fixed core is
normalized by C_K(c), so it also centralizes the closure of that layer under
the literal C_K(c). Apply these conclusions to the fixed involution in the
contained S5 branch of the same original W/Z_S witness.

No vanishing of the fixed core or elementary lift is asserted. Excluding
this remaining S5 branch, the mixed-amalgam contradiction, original 6.1.4–5,
omega escape and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`),
using the marked natural-action normalizer calculation of B.4.2(1).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveFixedLayer

private theorem linear_involution_eq_one
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (b : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (hb : b * b = 1)
    (c : SL(2,F)) (hc : orderOf c = 3)
    (hbc : ∀ v, b (c.val *ᵥ v) = c.val *ᵥ b v) : b = 1 := by
  let A := LinearMap.toMatrix' b.toLinearMap
  have hA : A * A = 1 := by
    rw [← LinearMap.toMatrix'_mul]
    have hh : b.toLinearMap * b.toLinearMap = 1 := congrArg LinearEquiv.toLinearMap hb
    simpa only [LinearMap.toMatrix'_one] using congrArg LinearMap.toMatrix' hh
  have hdet : A.det = 1 := by
    have hh : A.det ^ 2 = 1 := by rw [pow_two,←det_mul,hA,det_one]
    rcases sq_eq_one_iff.mp hh with hh | hh
    · exact hh
    · simpa only [CharTwo.neg_eq] using hh
  let a : SL(2,F) := ⟨A,hdet⟩
  have ha2 : a^2=1 := by
    rw [pow_two]
    exact Subtype.ext hA
  have hac : Commute a c := by
    apply Subtype.ext
    change A*c.val=c.val*A
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simpa only [A,toLin'_mul,LinearMap.comp_apply,toLin'_toMatrix',toLin'_apply,LinearEquiv.coe_coe] using hbc v
  let e := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  have ha : a=1 := by
    by_contra hne
    have hao : orderOf a=2 := orderOf_eq_prime ha2 hne
    have hea : orderOf ((e a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))=2 :=
      (orderOf_coe (e a)).trans ((e.orderOf_eq a).trans hao)
    have hec : orderOf ((e c : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))=3 :=
      (orderOf_coe (e c)).trans ((e.orderOf_eq c).trans hc)
    exact Equiv.Perm.three_not_commute_even_involution_five (e a) (e c) hea
      (e a).property hec ((hac.map e.toMonoidHom).map (alternatingGroup (Fin 5)).subtype)
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  change A = LinearMap.toMatrix' (1 : Module.End F (Fin 2 → F))
  rw [LinearMap.toMatrix'_one]
  exact congrArg Subtype.val ha


private theorem linear_two_element_eq_one
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (b : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (k : ℕ) (hb : b^(2^k)=1)
    (c : SL(2,F)) (hc : orderOf c = 3)
    (hbc : ∀ v, b (c.val *ᵥ v) = c.val *ᵥ b v) : b=1 := by
  have hp (m : ℕ) : ∀ v, (b^m) (c.val *ᵥ v) = c.val *ᵥ (b^m) v := by
    induction m with
    | zero => intro v; rfl
    | succ m ih =>
      intro v
      rw [pow_succ']
      change b ((b^m) (c.val *ᵥ v)) = c.val *ᵥ b ((b^m) v)
      rw [ih,hbc]
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have hh : (b^(2^k))*(b^(2^k))=1 := by
      rw [←pow_two,←pow_mul,←Nat.pow_succ]
      exact hb
    exact ih (linear_involution_eq_one hF (b^(2^k)) hh c hc (hp _))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveFixedLayer

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- A Sylow element fixing the central line and commuting with the
original cubic centralizes the whole natural layer. -/
theorem natural_four_cubic_fixed_centralizes_layer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    {c t : G} (hcL : c ∈ L) (hc3 : orderOf c=3)
    (htT : t ∈ (T : Subgroup G)) (htI : t ∈ Escape.I (T : Subgroup G) L R)
    (htc : Commute t c) : t ∈ centralizer (layer L R : Set G) := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnat
  let := ZMod.algebra F 2
  let B := layer L R
  let X := sylowSpace (T : Subgroup G) e
  let b := vectorActor f ⟨t,h.sylow_normalizes_layer htT⟩
  have hX : X.toAddSubgroup = coordinateSpace f (ZS (T : Subgroup G) L R) :=
    AddSubgroup.ext (mem_sylowSpace_iff (T : Subgroup G) e f hf)
  have hfix : ∀ v ∈ X, b v=v := by
    intro v hv
    apply (vectorActor_fixed_iff f _ v).mpr
    apply mem_centralizer_singleton_iff.mpr
    exact htI _ (show (f.symm (Multiplicative.ofAdd v) : G) ∈ ZS (T : Subgroup G) L R from
      (show v ∈ coordinateSpace f (ZS (T : Subgroup G) L R) from hX ▸ hv))
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp h.ZS_ne_bot
  let v := (f ⟨z,z.property.1⟩).toAdd
  have hv : v ∈ X := by
    change v ∈ X.toAddSubgroup
    rw [hX]
    simp [v]
  have hv0 : v ≠ 0 := by
    intro he
    apply hz
    apply Subtype.ext
    have hh : f ⟨z,z.property.1⟩=1 := congrArg Multiplicative.ofAdd he
    exact congrArg (fun x : B => (x : G)) (f.injective (hh.trans f.map_one.symm))
  obtain ⟨s,hs⟩ :=
    Representation.OneCohomology.CentralCoverOriginalAction.normalizer_semilinear
      (Representation.specialLinearNatural 2 (k := F))
      (fun k hk => Representation.SL2NaturalOffenders.centralizer_scalar k hk)
      (quotientActor e ⟨t,h.sylow_normalizes_L htT⟩) b
      (vectorActor_intertwines e f hf ⟨t,h.sylow_normalizes_L htT⟩
        (h.sylow_normalizes_layer htT))
  have hs_id : ∀ a : F, s a=a := by
    intro a
    apply smul_left_injective F hv0
    change s a • v = a • v
    calc
      s a • v = b (a • v) := by rw [hs,hfix v hv]
      _ = a • v := hfix _ (X.smul_mem a hv)
  let bF : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
    { b.toAddEquiv with map_smul' := fun a w => by change b (a • w)=a • b w; rw [hs,hs_id] }
  obtain ⟨k,hk⟩ := T.isPGroup' ⟨t,htT⟩
  have htk : t^(2^k)=1 := congrArg Subtype.val hk
  have hpow (m : ℕ) (w : Fin 2 → F) :
      (f.symm (Multiplicative.ofAdd ((bF^m) w)) : G) =
        t^m*(f.symm (Multiplicative.ofAdd w) : G)*(t^m)⁻¹ := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ']
      change (f.symm (Multiplicative.ofAdd (b ((bF^m) w))) : G) = _
      rw [vectorActor_coe,ih,pow_succ']
      group
  have hbF : bF^(2^k)=1 := by
    apply LinearEquiv.ext
    intro w
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    have hh := hpow (2^k) w
    rw [htk] at hh
    simpa only [one_mul,inv_one,mul_one,LinearEquiv.coe_one,id_eq] using hh
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let cL : L := ⟨c,hcL⟩
  have hcL3 : orderOf cL=3 := (Subgroup.orderOf_mk c hcL).trans hc3
  have hqne : q cL ≠ 1 := by
    intro hq
    have hm := e.injective (hq.trans e.map_one.symm)
    have hm' : cL ∈ pCore 2 L := (QuotientGroup.eq_one_iff cL).mp hm
    have hh := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨cL,hm'⟩ : pCore 2 L)
    rw [Subgroup.orderOf_mk,hcL3] at hh
    norm_num at hh
  have hqc : orderOf (q cL)=3 := orderOf_eq_prime
    (by rw [←map_pow,←hcL3,pow_orderOf_eq_one,map_one]) hqne
  have hnat (w : Fin 2 → F) :
      (f.symm (Multiplicative.ofAdd ((q cL).val *ᵥ w)) : G) =
        c*(f.symm (Multiplicative.ofAdd w) : G)*c⁻¹ := by
    have hh := hf cL (f.symm (Multiplicative.ofAdd w))
    rw [f.apply_symm_apply] at hh
    exact hh
  have hcomm (w : Fin 2 → F) : bF ((q cL).val *ᵥ w) = (q cL).val *ᵥ bF w := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    change (f.symm (Multiplicative.ofAdd (b ((q cL).val *ᵥ w))) : G) = _
    rw [vectorActor_coe,hnat,hnat]
    change _ = c*(f.symm (Multiplicative.ofAdd (b w)) : G)*c⁻¹
    rw [vectorActor_coe]
    calc
      t*(c*(f.symm (Multiplicative.ofAdd w) : G)*c⁻¹)*t⁻¹ =
          (t*c)*(f.symm (Multiplicative.ofAdd w) : G)*(t*c)⁻¹ := by group
      _ = (c*t)*(f.symm (Multiplicative.ofAdd w) : G)*(c*t)⁻¹ := by rw [htc.eq]
      _ = _ := by group
  have hb := NaturalFiveFixedLayer.linear_two_element_eq_one hF bF k hbF (q cL) hqc hcomm
  intro x hx
  have hh : b (f ⟨x,hx⟩).toAdd = (f ⟨x,hx⟩).toAdd :=
    congrArg (fun k : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) => k (f ⟨x,hx⟩).toAdd) hb
  have hcx := (vectorActor_fixed_iff f _ _).mp hh
  simpa only [ofAdd_toAdd,f.symm_apply_apply,mem_centralizer_singleton_iff] using hcx

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- Every cubic-fixed point in the original normalizer two-core
centralizes the actual natural layer. -/
theorem natural_four_core_cubic_centralizer_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    {c : G} (hcL : c ∈ L) (hc3 : orderOf c=3) :
    (Escape.H (T : Subgroup G) L R).pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ≤
      centralizer (layer L R : Set G) := by
  have hQT : (Escape.H (T : Subgroup G) L R).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTN : (T : Subgroup G) ≤ Escape.H (T : Subgroup G) L R := h.sylow_normalizes_ZS
    have hh := pCoreIn_le_sylow (Escape.H (T : Subgroup G) L R) (T.subtype hTN)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] at hh
  intro t ht
  exact natural_four_cubic_fixed_centralizes_layer h hnat hcL hc3
    (hQT ht.1) (natural_four_normalizer_core_centralizes h hnat ht.1)
    (show Commute t c from (ht.2 c (mem_zpowers c)).symm)

/-- The full fixed core centralizes the natural layers generated by the
literal cubic centralizer in K. This uses normality in the original N. -/
theorem natural_four_fixed_core_centralizes_fixed_span
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKN : K ≤ Escape.H (T : Subgroup G) L R)
    {c : G} (hcL : c ∈ L) (hc3 : orderOf c=3) :
    (Escape.H (T : Subgroup G) L R).pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ≤
      centralizer (conjugateSpanBy (layer L R) (K ⊓ centralizer (zpowers c : Set G)) : Set G) := by
  let N := Escape.H (T : Subgroup G) L R
  let D := N.pCoreIn 2 ⊓ centralizer (zpowers c : Set G)
  let C := K ⊓ centralizer (zpowers c : Set G)
  have hn : C ≤ normalizer (D : Set G) :=
    (le_inf ((inf_le_left.trans hKN).trans (N.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
      (inf_le_right.trans (centralizer (zpowers c : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  apply le_centralizer_iff.mpr
  exact conjugateSpanBy_le (le_centralizer_iff.mp
    (natural_four_core_cubic_centralizer_le h hnat hcL hc3))
    (hn.trans (normalizer_le_normalizer_centralizer D))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- On the same W/Z_S witness, the contained S5 obstruction lies in
the centralizer of the natural layers generated by the cubic centralizer. -/
theorem exists_ambient_amalgam_or_five_fixed_layer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveCubicParabolicData T L R P N ∧
            NaturalThreeInvariantParabolicData T L R P N M ∧
            (NaturalEscapingAmalgamData T L R P N M ∨
              (NaturalFiveContainedParabolicData T P N M ∧
                NaturalFiveElementaryRestriction P N ∧
                NaturalFiveCubicFixedData T L R P N ∧
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∈ centralizer (layer L R : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (layer L R)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_fixed_core h hnat hE hs hNS hab
  let := hZ
  let := hX
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  apply ham.imp_right
  rintro ⟨hd,hno,hfixed,c,t,hcL,hcN,hc3,ht,ht2,hct,htZ⟩
  have htc : t ∈ centralizer (zpowers c : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh : c ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hct)
    exact (mem_centralizer_singleton_iff.mp (zpowers_le.mpr hh hx))
  have hKN := hcover.1.trans hIN
  refine ⟨hd,hno,hfixed,c,t,hcL,hcN,hc3,ht,ht2,hct,htZ,?_,?_⟩
  · exact natural_four_core_cubic_centralizer_le (hn ▸ h) (hn ▸ hnat) hcL hc3 ⟨ht,htc⟩
  · exact natural_four_fixed_core_centralizes_fixed_span (hn ▸ h) (hn ▸ hnat)
      _ hKN hcL hc3 ⟨ht,htc⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
