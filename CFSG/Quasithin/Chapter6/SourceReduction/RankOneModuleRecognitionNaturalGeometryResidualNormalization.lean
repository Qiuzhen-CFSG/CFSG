module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCentralKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySolvableFactors

/-!
# Cubic normalization of every literal factor residual

The faithful central cover identifies each factor preimage with its marked
S₃, L₃(2), or S₅ model. Transport through the original embedding gives a
subnormal S₃ in the solvable case; its cubic residual is normalized by the
preceding ternary-plane argument. The other factors use their already proved
component lifts. The conclusion concerns O² of the full preimage under the
same covering map, followed by the same ambient embedding.

The escape application retains every earlier action equation, kernel identity,
and product coordinate on the literal W/Z_S witness. This discharges the
solvable residual-normalization step of Aschbacher–Smith 6.1.19, printed p.675.
Full-factor normalization and the parabolic/amalgam contradiction, initial
6.1.4–5 and the remaining escape geometry stay with the natural-reduction
owner; unconditional 6.1.27 is not asserted.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open Subgroup Theory.GroupTheory
universe v

/-- On the original central-cover maps, every ambient cubic normalizes the
literal two-residual of each factor preimage, including the solvable S₃ row. -/
theorem SmallTransvectionProductModel.cubic_normalizes_residual_preimages
    {A N : Type*} {B V : Type v}
    [Group A] [Finite A] [Group N] [Finite N] [Group B] [Finite B]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) B V} (product : SmallTransvectionProductModel ρ)
    (φ : A →* B) (hφ : Function.Bijective φ)
    (j : A →* N) (hj : Function.Injective j) (hjn : j.range.IsSubnormal)
    (Q : Subgroup N) (hr : primeRank 3 N ≤ 2)
    (hres : ∀ K ∈ product.factors, FactorResidualLift φ j Q K) :
    ∀ K ∈ product.factors, ∀ c : N, c^3=1 →
      c ∈ normalizer ((((pResidual 2 (K.comap φ)).map (K.comap φ).subtype).map j) : Set N) := by
  intro K hK c hc
  let H := K.comap φ
  let eH : H ≃* K := MulEquiv.ofBijective (φ.subgroupComap K)
    ⟨fun x y he => Subtype.ext (hφ.1 (congrArg Subtype.val he)),
      φ.subgroupComap_surjective_of_surjective K hφ.2⟩
  rcases hres K hK with ⟨⟨e⟩,hcard⟩ | ⟨hrK,C,hC,hcomp,hmap,hCN,he,hCQ,hn,hm⟩
  · have hKn : K.Normal := by
      obtain ⟨t,_,rfl,_⟩ := product.marked K hK
      infer_instance
    let := hKn
    have hH : H.IsSubnormal := (inferInstance : H.Normal).isSubnormal
    have hJ : (H.map j).IsSubnormal := by
      have hh := (hH.map j.rangeRestrict_surjective).trans' hjn
      simpa only [map_map,MonoidHom.subtype_comp_rangeRestrict] using hh
    let eJ := H.equivMapOfInjective j hj
    have hh := NaturalSolvableFactor.cubic_normalizes_residual (H.map j) hJ
      (eJ.symm.trans (eH.trans e)) hr c hc
    have heq : (pResidual 2 (H.map j)).map (H.map j).subtype =
        ((pResidual 2 H).map H.subtype).map j := by
      rw [←map_pResidual_of_surjective 2 eJ.toMonoidHom eJ.surjective,map_map,map_map]
      rfl
    rwa [heq] at hh
  · have hKres : pResidual 2 K=solvableResidual K :=
      map_injective K.subtype_injective hrK
    have hHres : pResidual 2 H=solvableResidual H := by
      apply map_injective (f:=eH.toMonoidHom) eH.injective
      calc
        (pResidual 2 H).map eH.toMonoidHom = pResidual 2 K :=
          map_pResidual_of_surjective 2 eH.toMonoidHom eH.surjective
        _ = solvableResidual K := hKres
        _ = (solvableResidual H).map eH.toMonoidHom :=
          (map_solvableResidual_eq eH.toMonoidHom eH.surjective).symm
    change c ∈ normalizer ((((pResidual 2 H).map H.subtype).map j) : Set N)
    rw [hHres,←hC]
    exact hn c hc

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Classical
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe v
open CFSG.Quasithin.ChapterE
variable {G : Type v} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- Every original factor residual, including the solvable S₃ row, is
normalized by every cubic of the ambient normalizer quotient. All actions,
quotient maps and product coordinates retain the same original witness. -/
theorem exists_ambient_cubic_residual_product
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
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
      ∃ (hPI : P ≤ I) (hPN : P ≤ N)
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
          closure {x : P ⧸ pCore 2 P | x ^ 2 = 1} = ⊤ ∧
          let θ := Representation.ofElementaryAbelianAction
            (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
          ∃ product : SmallTransvectionProductModel θ,
            (∀ K ∈ product.factors, FactorResidualLift φ j
              ((I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) K ∧
              ∀ c : N ⧸ pCore 2 N, c^3=1 →
                c ∈ Subgroup.normalizer ((((pResidual 2 (K.comap φ)).map
                  (K.comap φ).subtype).map j) : Set (N ⧸ pCore 2 N))) ∧
            ∃ e : (∀ K : {K // K ∈ product.factors}, K.val) ≃* (P ⧸ pCore 2 P),
              (∀ x, φ (e x) = product.productEquiv x) ∧
              (∀ K : {K // K ∈ product.factors}, ∀ a : P ⧸ pCore 2 P,
                a ∈ K.val.comap φ ↔ ∃ x : K.val,
                  e (Function.update 1 K x) = a) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,hres,e,he,hcoords⟩ :=
    d.exists_ambient_faithful_small_product h hnat hE hs hNS hab
  let N := Escape.H (T : Subgroup G) L R
  have hsq : IsSQTK KnownSimple.IsKnownSimple N := h.simpleQTKE.twoLocal_sqtk
    ⟨ZS (T : Subgroup G) L R,h.ZS_ne_bot,T.isPGroup'.to_le h.ZS_le_T,rfl⟩
  have hr : primeRank 3 (N ⧸ pCore 2 N) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin 3 (by decide) (by decide))
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,?_,e,he,hcoords⟩
  intro K hK
  exact ⟨hres K hK, product.cubic_normalizes_residual_preimages φ hφ j hj hjn _ hr hres K hK⟩

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
