module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates
public import CFSG.Quasithin.Chapter12.Section06.LocalAlternatives.NonTensor
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.PerfectImage
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ActionKernel

/-!
# The non-tensor exclusion on the original chosen module

Apply the local mixed-commutator and nonsingular cubic calculation to
the original V under SourceHypothesis. The actual T-conjugator supplies
the second C-component, and componenthood supplies two-perfectness and
mutual normalization. The cubic marking is stated on the original
conjugation-kernel quotient; full-coordinate equivariance transports it
to the local calculation. The final theorem constructs that marking from
an actual nonidentity cubic in K₁ ∩ L. The original kernel bridge
C_L(V) = O₂(L) ensures its quotient image is nonidentity, and fixation
of the selected point places it in the literal four-block residual.

The fixed-space vanishing of 12.6.23 and nonsingular-centralizer control
of 12.6.2 remain explicit earlier-source inputs, owned by
qt-d-12634-central. This owner still must construct the F.9 application,
the abelian span of 12.6.26, the local component and cubic selection, and
the filtration alternative. This conditional branch exclusion is not
an assertion of 12.6.33 or the natural reduction 12.6.34.

Source: Aschbacher--Smith, proof of Lemma 12.6.33, printed pp.837--838
(PDF pp.854--855), with the original setup in 12.6.1.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis K T L V) (D : OrthogonalMarking L V S.chosen.normalizes)
  (hZ : ZV L V = ⊥) (z : V)

/-- The non-tensor wreath filtration is excluded for the original chosen V
and its actual fixed-space and conjugation-kernel quotient markings. -/
theorem SourceHypothesis.original_nonTensor_wreath_impossible
    {H : Subgroup G} (h : ((D.fullSetup hZ T z).f9 H).Hypothesis)
    (habelian : IsMulCommutative ((D.fullSetup hZ T z).UH H))
    (r : Equiv.Perm (Fin 8))
    (hz : D.coordinates (Submodule.Quotient.mk (Additive.ofMul z)) =
      naturalRepresentation (Fin 8) r CubicMovement.point)
    (hpoint : ∀ u : V, D.Nonsingular u →
      centralizer ({(u : G)} : Set G) ≤ M L)
    (K₁ K₂ I : Subgroup H)
    (hK₁ : K₁.IsCComponent)
    (hcomm : ⁅K₁,K₂⁆ ≤ pCore 2 H)
    (hupper : ⁅⁅((D.fullSetup hZ T z).UH H).subgroupOf H,K₁⁆,K₂⁆ ≤ I)
    (hlower : ⁅⁅I,K₁⁆,K₂⁆ ≤ (D.fullSetup hZ T z).V₁.subgroupOf H)
    (hout : ¬ K₁.map H.subtype ≤ M L)
    (t : G) (ht : t ∈ (T : Subgroup G))
    (hswap : (K₁.map H.subtype).map (MulAut.conj t).toMonoidHom = K₂.map H.subtype)
    (x : H) (hx₁ : x ∈ K₁) (hxL : (x : G) ∈ L)
    (a : FourBlockResidual.Product) (ha : a ^ 3 = 1) (hne : a ≠ 1)
    (hactor : (D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker
      ⟨(x : G),hxL⟩)).val = r * FourBlockResidual.blockHom a * r⁻¹) : False := by
  have hK₂ : K₂.IsCComponent := by
    let tH : H := ⟨t,h.T_le_H ht⟩
    have he : K₁.map (MulAut.conj tH).toMonoidHom = K₂ := by
      apply map_injective H.subtype_injective
      calc
        (K₁.map (MulAut.conj tH).toMonoidHom).map H.subtype =
            (K₁.map H.subtype).map (MulAut.conj t).toMonoidHom := by
          rw [map_map,map_map]
          rfl
        _ = K₂.map H.subtype := hswap
    exact he ▸ hK₁.map_equiv (MulAut.conj tH)
  let : Group.IsPerfect K₁ := hK₁.perfect
  let : Group.IsPerfect K₂ := hK₂.perfect
  have hp₁ : IsPPerfect 2 K₁ := (pResidual_eq_top_iff 2 K₁).mp
    (pResidual_eq_top_of_isPerfect 2)
  have hp₂ : IsPPerfect 2 K₂ := (pResidual_eq_top_iff 2 K₂).mp
    (pResidual_eq_top_of_isPerfect 2)
  have hn₁ : K₁ ≤ normalizer (K₂ : Set H) :=
    (le_cComponentLayer hK₁).trans (cComponentLayer_le_normalizer hK₂)
  have hn₂ : K₂ ≤ normalizer (K₁ : Set H) :=
    (le_cComponentLayer hK₂).trans (cComponentLayer_le_normalizer hK₁)
  have hz' : ((D.fullSetup hZ T z).coordinates (D.fullSetup hZ T z).z).toAdd =
      naturalRepresentation (Fin 8) r CubicMovement.point :=
    (D.fullCoordinates_apply hZ z).trans hz
  apply (D.fullSetup hZ T z).nonTensor_wreath_impossible h habelian r hz' _ K₁ K₂ I hp₁ hp₂ hn₁ hn₂
    hcomm hupper hlower rfl hout t ht hswap x hx₁ (S.chosen.normalizes hxL) a ha hne
  · intro v
    have he := D.fullCoordinates_equivariant hZ (⟨(x : G),hxL⟩ : L) v
    rw [hactor] at he
    exact he
  · intro u hu
    exact hpoint u ((D.fullCoordinates_nonsingular_iff hZ u).mp hu)
/-- The original non-tensor exclusion needs only an actual nonidentity
cubic in K₁ ∩ L. The original action-kernel bridge shows that its quotient
image is nonidentity; point fixation constructs its four-block marking. -/
theorem SourceHypothesis.original_nonTensor_wreath_impossible_of_cubic
    {H : Subgroup G} (h : ((D.fullSetup hZ T z).f9 H).Hypothesis)
    (habelian : IsMulCommutative ((D.fullSetup hZ T z).UH H))
    (r : Equiv.Perm (Fin 8))
    (hz : D.coordinates (Submodule.Quotient.mk (Additive.ofMul z)) =
      naturalRepresentation (Fin 8) r CubicMovement.point)
    (hpoint : ∀ u : V, D.Nonsingular u →
      centralizer ({(u : G)} : Set G) ≤ M L)
    (K₁ K₂ I : Subgroup H)
    (hK₁ : K₁.IsCComponent)
    (hcomm : ⁅K₁,K₂⁆ ≤ pCore 2 H)
    (hupper : ⁅⁅((D.fullSetup hZ T z).UH H).subgroupOf H,K₁⁆,K₂⁆ ≤ I)
    (hlower : ⁅⁅I,K₁⁆,K₂⁆ ≤ (D.fullSetup hZ T z).V₁.subgroupOf H)
    (hout : ¬ K₁.map H.subtype ≤ M L)
    (t : G) (ht : t ∈ (T : Subgroup G))
    (hswap : (K₁.map H.subtype).map (MulAut.conj t).toMonoidHom = K₂.map H.subtype)
    (x : H) (hx₁ : x ∈ K₁) (hxL : (x : G) ∈ L)
    (hx3 : x ^ 3 = 1) (hxn : x ≠ 1) : False := by
  let l : L := ⟨(x : G),hxL⟩
  let q := QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker
  let f : L →* Equiv.Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (D.groupEquiv.toMonoidHom.comp q)
  have hl3 : l ^ 3 = 1 := Subtype.ext (congrArg (fun w : H => (w : G)) hx3)
  have hf3 : f l ^ 3 = 1 := by rw [←map_pow,hl3,map_one]
  have hfn : f l ≠ 1 := by
    intro he
    have hq : q l = 1 := D.groupEquiv.injective
      ((show D.groupEquiv (q l) = 1 from Subtype.ext he).trans D.groupEquiv.map_one.symm)
    have hlcore : l ∈ pCore 2 L := S.actionKernel_eq_core ▸
      (QuotientGroup.eq_one_iff l).mp hq
    let y : pCore 2 L := ⟨l,hlcore⟩
    have hy3 : y ^ 3 = 1 := Subtype.ext hl3
    have htwo : IsPGroup 2 (pCore 2 L) := pCore_isPGroup
    have hyone : y = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (htwo.orderOf_coprime (by decide : Nat.Coprime 2 3) y)
        dvd_rfl (orderOf_dvd_of_pow_eq_one hy3))
    apply hxn
    exact Subtype.ext (congrArg (fun w : pCore 2 L => ((w : L) : G)) hyone)
  have hfix : naturalRepresentation (Fin 8) (f l)
      (naturalRepresentation (Fin 8) r CubicMovement.point) =
        naturalRepresentation (Fin 8) r CubicMovement.point := by
    have hzl : conjugation L V S.chosen.normalizes l z = z := by
      apply Subtype.ext
      have hc := h.H_centralizes x.property (z : G) (mem_zpowers (z : G))
      change (x : G) * (z : G) * (x : G)⁻¹ = (z : G)
      rw [←hc,mul_inv_cancel_right]
    have he := D.fullCoordinates_equivariant hZ l z
    rw [hzl,D.fullCoordinates_apply hZ z,hz] at he
    exact he.symm
  obtain ⟨a,ha,han,he⟩ := CubicMovement.conjugate_cubic_marking_of_fixed r (f l) hf3 hfn hfix
  exact S.original_nonTensor_wreath_impossible D hZ z h habelian r hz hpoint K₁ K₂ I
    hK₁ hcomm hupper hlower hout t ht hswap x hx₁ hxL a ha han he
end CFSG.Quasithin.Chapter12.Section06
