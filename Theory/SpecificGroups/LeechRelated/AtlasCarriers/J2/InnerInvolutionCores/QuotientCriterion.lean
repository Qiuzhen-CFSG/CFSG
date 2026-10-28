module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.GroupAction.AutomorphismFixedResidual
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.SpecificGroups.AlternatingFiveCore

/-!
# The A₅ quotient criterion for inner J₂ fixed residuals

A surjection from a fixed subgroup onto A₅ with two-group kernel also maps
its solvable residual onto A₅. The residual has trivial three-core, since
its normal three-core maps trivially and cannot lie nontrivially in the
two-group kernel. The residual centralizer inside the fixed subgroup maps
into Z(A₅), so is a two-group as well.

In the actual degree-100 carrier, faithful inner conjugation identifies the
inner part of the two automorphism centralizers with a subgroup of that
residual centralizer. The proved two-group bound on Out(J₂) then makes the
entire intersection a two-group. This discharges exactly the two calculations
in `MulAut.FixedResidualThreeCoreData`, from a genuine quotient map.

Source: GLS3 Table 5.3g and notes (3)–(4), as used on Aschbacher--Smith
printed p.1137. The concrete quotient maps for both representatives and the
exhaustive fusion are supplied in the parent module `InnerInvolutionCores`.
No quotient map or centralizer description is assumed by that final theorem.
-/

open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.InnerInvolutionCores
private abbrev Alt5 := alternatingGroup (Fin 5)
local instance : IsSimpleGroup Alt5 := alternatingGroup.isSimpleGroup (by simp)
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem alt_perfect : Group.IsPerfect Alt5 := by
  constructor
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Alt5) inferInstance with h | h
  · have hc : IsMulCommutative Alt5 := (commutator_eq_bot_iff Alt5).mp h
    have hn := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
    norm_num at hn
  · exact h

private theorem alt_threeCore : pCore 3 Alt5 = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 3 Alt5) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 3 Alt5 := by
      have ht : IsPGroup 3 (⊤ : Subgroup Alt5) := h ▸ pCore_isPGroup
      exact ht.of_equiv topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hc : Nat.Coprime 2 (Nat.card Alt5) := hn ▸ (by decide : Nat.Coprime 2 3).pow_right n
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    change Nat.Coprime 2 60 at hc
    norm_num at hc

private theorem threeCore_of_quotient {F : Type*} [Group F]
    (f : F →* Alt5) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : pCore 3 F = ⊥ := by
  have hm : (pCore 3 F).map f ≤ pCore 3 Alt5 :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  have hle : pCore 3 F ≤ f.ker := by
    rw [alt_threeCore] at hm
    exact ((pCore 3 F).map_eq_bot_iff).mp (le_bot_iff.mp hm)
  exact le_bot_iff.mp ((le_inf le_rfl hle).trans
    (IsPGroup.disjoint_of_coprime (pCore_isPGroup (p := 3)) hk (by decide)).eq_bot.le)

private theorem residual_surjective {F : Type*} [Group F] [Finite F]
    (f : F →* Alt5) (hf : Function.Surjective f) :
    Function.Surjective (f.comp (solvableResidual F).subtype) := by
  let := alt_perfect
  have hm : (solvableResidual F).map f = ⊤ := by
    rw [map_solvableResidual_eq f hf, solvableResidual_eq_top]
  intro x
  obtain ⟨y, hy, hxy⟩ := hm.symm ▸ (mem_top x)
  exact ⟨⟨y, hy⟩, hxy⟩

private theorem residual_threeCore {F : Type*} [Group F] [Finite F]
    (f : F →* Alt5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    pCore 3 (solvableResidual F) = ⊥ := by
  apply threeCore_of_quotient (f.comp (solvableResidual F).subtype) (residual_surjective f hf)
  exact hk.comap_of_injective _ (solvableResidual F).subtype_injective

private theorem residual_centralizer_isTwoGroup {F : Type*} [Group F] [Finite F]
    (f : F →* Alt5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    IsPGroup 2 (centralizer (solvableResidual F : Set F)) := by
  apply hk.to_le
  intro x hx
  change f x = 1
  apply mem_bot.mp
  rw [← alternatingGroup.center_eq_bot (α := Fin 5) (by simp)]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z, rfl⟩ := residual_surjective f hf y
  exact (map_mul f _ _).symm.trans ((congrArg f (hx z z.property)).trans (map_mul f _ _))

private theorem conj_injective : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
  intro x y h
  have hxy : ExceptionalParabolics.intoExtension x = ExceptionalParabolics.intoExtension y :=
    ExceptionalParabolics.extensionAction_injective (by
      simpa only [ExceptionalParabolics.extensionAction_inner] using h)
  exact (Subgroup.inclusion_injective
    (show generated ≤ ExceptionalParabolics.extension from le_sup_left)) hxy

private noncomputable def residualInnerEquiv (a : MulAut Carrier) :
    solvableResidual a.fixedSubgroup ≃* MulAut.fixedPerfectResidualInner a :=
  ((solvableResidual a.fixedSubgroup).equivMapOfInjective a.fixedSubgroup.subtype
    a.fixedSubgroup.subtype_injective).trans
    ((MulAut.fixedPerfectResidual a).equivMapOfInjective MulAut.conj conj_injective)

private theorem automorphism_centralizer_isTwoGroup (a : MulAut Carrier)
    (hF : IsPGroup 2 (centralizer (solvableResidual a.fixedSubgroup : Set a.fixedSubgroup))) :
    IsPGroup 2 (centralizer ({a} : Set (MulAut Carrier)) ⊓
      centralizer (MulAut.fixedPerfectResidualInner a : Set (MulAut Carrier)) :
        Subgroup (MulAut Carrier)) := by
  let C : Subgroup (MulAut Carrier) := centralizer ({a} : Set (MulAut Carrier)) ⊓
    centralizer (MulAut.fixedPerfectResidualInner a : Set (MulAut Carrier))
  let q : C →* MulAut.Outer Carrier :=
    (QuotientGroup.mk' (MulAut.innerSubgroup Carrier)).comp C.subtype
  let K : Subgroup a.fixedSubgroup := centralizer (solvableResidual a.fixedSubgroup : Set a.fixedSubgroup)
  let j : a.fixedSubgroup →* MulAut Carrier := MulAut.conj.comp a.fixedSubgroup.subtype
  have hker : IsPGroup 2 q.ker := by
    have hle : q.ker ≤ (K.map j).comap C.subtype := by
      intro b hb
      have hbinner : (b : MulAut Carrier) ∈ MulAut.innerSubgroup Carrier :=
        (QuotientGroup.eq_one_iff _).mp hb
      obtain ⟨x, hx⟩ := hbinner
      have hcomm : MulAut.conj x * a = a * MulAut.conj x := by
        rw [hx]
        exact mem_centralizer_singleton_iff.mp b.property.1
      have hfixed : a x = x := by
        apply conj_injective
        have he : MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
          ext z
          simp
        rw [he, ← hcomm, mul_inv_cancel_right]
      let y : a.fixedSubgroup := ⟨x, (MulAut.mem_fixedSubgroup a x).mpr hfixed⟩
      refine ⟨y, ?_, hx⟩
      intro z hz
      apply Subtype.ext
      apply conj_injective
      have hzi : MulAut.conj (z : Carrier) ∈ MulAut.fixedPerfectResidualInner a :=
        mem_map_of_mem _ (mem_map_of_mem a.fixedSubgroup.subtype hz)
      have hc := b.property.2 (MulAut.conj (z : Carrier)) hzi
      rw [← hx] at hc
      change MulAut.conj ((z : Carrier) * x) = MulAut.conj (x * (z : Carrier))
      simpa only [map_mul] using hc
    exact ((hF.map j).comap_of_injective C.subtype C.subtype_injective).to_le hle
  have hout : IsPGroup 2 (⊤ : Subgroup (MulAut.Outer Carrier)) := outer_isTwoGroup.to_subgroup ⊤
  have hp := hout.comap_of_ker_isPGroup q hker
  rw [comap_top] at hp
  exact hp.of_equiv topEquiv

/-- A two-group kernel and an actual A₅ quotient of the fixed subgroup suffice
for both literal fixed-perfect-residual calculations. -/
public theorem fixedResidualThreeCoreData_of_quotient (a : MulAut Carrier)
    (f : a.fixedSubgroup →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    MulAut.FixedResidualThreeCoreData a := by
  constructor
  · rw [← pCore_map_iso 3 (residualInnerEquiv a), residual_threeCore f hf hk, Subgroup.map_bot]
  · obtain ⟨n, hn⟩ := (automorphism_centralizer_isTwoGroup a
      (residual_centralizer_isTwoGroup f hf hk)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n

end Sporadic.LeechRelated.J2.InnerInvolutionCores
