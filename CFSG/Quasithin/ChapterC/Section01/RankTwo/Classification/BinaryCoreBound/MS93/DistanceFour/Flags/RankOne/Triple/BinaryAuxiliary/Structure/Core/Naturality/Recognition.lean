module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Recognition
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.ElementaryAbelianAction

/-!
# Recognition with the exact kernel of the full local actor

A finite elementary section of order at most four with nontrivial
two-residual action is identified with the literal binary matrix plane.
The quotient conjugation action supplies its coordinate map and ambient
action equation. A supplied onto actor map to SL₂(2) marks the desired
kernel: centralization gives one inclusion, and equal finite indices give
equality. Thus recognition preserves the whole actor, not just its residual.

This is the final coordinate step of the X calculation in
Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907. The source
order bound and residual movement are separate mathematical premises.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreNaturality

/-- Recognition of a literal elementary section, retaining a previously marked
full-actor kernel. The order bound and residual movement are explicit premises. -/
theorem markedFactor_of_elementary_quotient {G : Type*} [Group G]
    (P H N K : Subgroup G) [Finite P] [Finite H]
    (hPH : P ≤ normalizer H) (hPN : P ≤ normalizer N)
    (hN : (N.subgroupOf H).Normal)
    (hE : letI := hN; IsElementaryAbelian 2 (H ⧸ N.subgroupOf H))
    (hprime : primeToResidual 2 P = ⊤)
    (hmove : ¬ ⁅H, (pResidual 2 P).map P.subtype⁆ ≤ N)
    (hcard : N.relIndex H ≤ 4) (hK : ⁅H,K⁆ ≤ N)
    (π₀ : P →* SL2) (hπ₀ : Function.Surjective π₀)
    (hk₀ : π₀.ker = K.subgroupOf P) : Nonempty (MarkedFactor P H N K) := by
  let := hN
  let := hE
  let B := H ⧸ N.subgroupOf H
  obtain ⟨a, ha⟩ := exists_quotient_conjugation_action P H N hPH hPN hN
  let : MulDistribMulAction P B := MulDistribMulAction.compHom B a
  let ρ : Representation (ZMod 2) P (Additive B) :=
    Representation.ofElementaryAbelianAction
  let q : H →* Multiplicative (Additive B) :=
    (MulEquiv.multiplicativeAdditive (H := B)).symm.toMonoidHom.comp
      (QuotientGroup.mk' (N.subgroupOf H))
  have hq : Function.Surjective q :=
    (MulEquiv.multiplicativeAdditive (H := B)).symm.surjective.comp
      (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = N.subgroupOf H :=
    (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' _)
      (MulEquiv.multiplicativeAdditive (H := B)).symm.toMonoidHom
      (MulEquiv.multiplicativeAdditive (H := B)).symm.injective).trans
        (QuotientGroup.ker_mk' _)
  have hact (p : P) (x y : H) (hy : (y : G) = (p : G) * (x : G) * (p : G)⁻¹) :
      (q y).toAdd = ρ p (q x).toAdd := by
    change QuotientGroup.mk' _ y = a p (QuotientGroup.mk' _ x)
    rw [ha]
    congr 1
    exact Subtype.ext hy
  have hres : ¬ pResidual 2 P ≤ ρ.ker := by
    intro ht
    apply hmove
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro _ ⟨p, hp, rfl⟩ x hx
    let v : H := ⟨x, hx⟩
    let w : H := ⟨(p : G) * x * (p : G)⁻¹,
      (mem_normalizer_iff.mp (hPH p.property) x).mp hx⟩
    have he : q w = q v := by
      apply Multiplicative.toAdd.injective
      rw [hact p v w rfl, MonoidHom.mem_ker.mp (ht hp)]
      rfl
    have hz : w * v⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [hqker] at hz
    exact hz
  have hc : Nat.card (Additive B) ≤ 4 := hcard
  obtain ⟨π, hπ, e, he⟩ := exists_natural_sl2_of_residuals_card_le_four ρ hprime hres hc
  let f : H →* Multiplicative (Fin 2 → ZMod 2) :=
    e.toAddEquiv.toMultiplicative.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp hq
  have hfk : f.ker = N.subgroupOf H :=
    (MonoidHom.ker_comp_of_injective q e.toAddEquiv.toMultiplicative.toMonoidHom
      e.injective).trans hqker
  have hfa (p : P) (x y : H) (hy : (y : G) = (p : G) * (x : G) * (p : G)⁻¹) :
      (f y).toAdd = (π p).val.mulVec (f x).toAdd := by
    change e (q y).toAdd = (π p).val.mulVec (e (q x).toAdd)
    rw [hact p x y hy, he]
  have hk : K.subgroupOf P ≤ π.ker := by
    intro p hp
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    obtain ⟨x, hx⟩ := hf (Multiplicative.ofAdd v)
    let y : H := ⟨(p : G) * (x : G) * (p : G)⁻¹,
      (mem_normalizer_iff.mp (hPH p.property) x).mp x.property⟩
    have hz : y * x⁻¹ ∈ f.ker := by
      rw [hfk]
      exact (show ⁅K,H⁆ ≤ N by rwa [commutator_comm])
        (commutator_mem_commutator hp x.property)
    have hfx : f y = f x := by
      have hh := MonoidHom.mem_ker.mp hz
      rwa [map_mul, map_inv, mul_inv_eq_one] at hh
    have hh := hfa p x y rfl
    rw [hfx, hx] at hh
    simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
      toAdd_ofAdd] using hh.symm
  have hindex : (K.subgroupOf P).index = π.ker.index := by
    rw [← hk₀, index_ker, index_ker, MonoidHom.range_eq_top.mpr hπ₀,
      MonoidHom.range_eq_top.mpr hπ]
  have hker : π.ker = K.subgroupOf P := by
    apply le_antisymm ?_ hk
    have hr := relIndex_mul_index hk
    rw [hindex] at hr
    have hpos : 0 < π.ker.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hrel : (K.subgroupOf P).relIndex π.ker = 1 := by nlinarith
    exact relIndex_eq_one.mp hrel
  exact ⟨⟨⟨π, hπ, f, hf, hfk, hPH, hfa⟩, hker⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreNaturality
