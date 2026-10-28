module

public import Theory.Representation.BinaryOffender.HomogeneousOrbitKernel
public import Theory.Representation.BinaryOffender.CubicSection
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Cubic offenders on the original central orbit quotient

An elementary cubic subgroup disjoint from the component centralizer acts
faithfully on every noncentral homogeneous orbit quotient. Its literal
image under the kernel projection therefore has the same rank. Restriction
and quotienting cannot increase fixed codimension, so the cubic ratio on
that faithful quotient is bounded by the original actor's action ratio.
No irreducibility of the whole orbit or minimality of the actor is needed.

Source: Aschbacher--Smith, the faithful-component branch of 5.1.23,
printed pp.645--646, using the section inequality behind D.2.7.
-/

open Subgroup Theory.GroupTheory
open Representation Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
public noncomputable section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
theorem cubicRatio_kernelQuotient_le_actionRatio_of_faithful
    {A : Subgroup G} (hA : IsElementaryTwo A) (hc : IsCubic ρ A)
    (hf : ∀ a ∈ A, ρ a = 1 → a = 1) :
    cubicRatio (KernelQuotient.action ρ) ≤ actionRatio ρ A := by
  let q := KernelQuotient.projection ρ
  have hi : Function.Injective (q.comp A.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    exact Subtype.ext (hf a a.property (by
      have he := congrArg (KernelQuotient.action ρ) ha
      simpa only [q,MonoidHom.comp_apply,KernelQuotient.action_projection,
        MonoidHom.map_one,Subgroup.subtype_apply] using he))
  have hr : rank (A.map q) = rank A := by
    let e : A ≃* A.map q := MulEquiv.ofBijective (q.subgroupMap A)
      ⟨fun a b hab => hi (congrArg Subtype.val hab),q.subgroupMap_surjective A⟩
    exact congrArg (Nat.log 2) (Nat.card_congr e.toEquiv).symm
  let : IsElementaryAbelian 2 A := hA.2
  have hm : IsElementaryTwo (A.map q) := by
    refine ⟨?_,IsElementaryAbelian.map q⟩
    intro hb
    have hz : rank (A.map q) = 0 := by simp [rank,hb]
    have hp := hA.rank_pos
    omega
  have hd : fixedCodim ρ A = fixedCodim (KernelQuotient.action ρ) (A.map q) :=
    fixedCodim_map_equivariant ρ (KernelQuotient.action ρ) q (LinearEquiv.refl _ _)
      (fun _ _ => rfl) A
  have hc' := hc.map_equivariant ρ (KernelQuotient.action ρ) q
    (LinearEquiv.refl _ _) (fun _ _ => rfl)
  have hb : cubicRatio (KernelQuotient.action ρ) ≤
      actionRatio (KernelQuotient.action ρ) (A.map q) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨hm,hc'⟩ le_rfl)
  simpa only [actionRatio,←hd,hr] using hb

/-- A faithful cubic subgroup retains its rank on the actual central orbit quotient. -/
theorem orbitSection_cubicRatio_le_actionRatio
    {K P A : Subgroup G} [IsQuasisimple K]
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K P I)
    (hAP : A ≤ P) (hA : IsElementaryTwo A) (hc : IsCubic ρ A)
    (hdis : Disjoint A (centralizer (K : Set G))) :
    cubicRatio (KernelQuotient.action (orbitSectionRepresentation ρ hI)) ≤
      actionRatio ρ A := by
  let J := K ⊔ P
  let τ := ρ.comp J.subtype
  let W := invariantSubspace ρ J (orbitSpan ρ P I)
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
  let N := centralSectionFixedSubspace ρ K J (orbitSpan ρ P I)
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    (sup_le K.le_normalizer hI.normalizes)
  let σ := orbitSectionRepresentation ρ hI
  let A₀ := A.subgroupOf J
  have hAJ : A ≤ J := hAP.trans le_sup_right
  let : IsElementaryAbelian 2 A := hA.2
  have hA₀ : IsElementaryTwo A₀ := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAJ⟩
    intro hz
    change A.subgroupOf J = ⊥ at hz
    exact hA.1 (by rw [←map_subgroupOf_eq_of_le hAJ,hz,Subgroup.map_bot])
  have hc₀ : IsCubic τ A₀ := by
    intro a ha b hb c hc' v
    exact hc a ha b hb c hc' v
  have hσ : IsCubic σ A₀ := cubic_quotient W.toRepresentation N
    (cubic_subrepresentation τ W hc₀)
  have hk := centralSection_kernel_le_centralizer_of_not_fixed ρ K J le_sup_left
    (orbitSpan ρ P I)
    (fun hh => hI.isIrrPlus.not_le_fixedSpace ρ ((le_orbitSpan ρ P I).trans hh))
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    (sup_le K.le_normalizer hI.normalizes)
  have hf : ∀ a ∈ A₀, σ a = 1 → a = 1 := by
    intro a ha he
    apply Subtype.ext
    exact disjoint_iff_inf_le.mp hdis ⟨ha,(hk (mem_map_of_mem J.subtype he)).2⟩
  have hq := cubicRatio_kernelQuotient_le_actionRatio_of_faithful σ hA₀ hσ hf
  have hd : fixedCodim σ A₀ ≤ fixedCodim ρ A := by
    have hn := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation N A₀
    have hw := fixedCodim_subrepresentation_le τ W A₀
    rw [fixedCodim_subgroupOf ρ hAJ] at hw
    exact (Nat.le_add_right _ _).trans (hn.trans hw)
  apply hq.trans
  unfold actionRatio
  rw [rank_subgroupOf hAJ]
  exact ENNReal.div_le_div_right (by exact_mod_cast hd) _

end Representation.BinaryOffender
