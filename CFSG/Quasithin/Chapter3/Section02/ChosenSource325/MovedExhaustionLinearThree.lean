module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizer
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveComponentAction
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.Representation.SL3OddNaturalNormalizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Intrinsic

/-!
# Inner actors on the remaining odd-degree natural SL₃ seed

The natural SL₃ image has odd index in its binary linear normalizer when
its defining degree is odd. Restricting to the literal seed therefore puts
every stabilizing two-subgroup in the component image. The original
pointwise kernel centralizes the quasisimple component, so the original
actor induces inner automorphisms on that component. The lift is a
homomorphism with exactly the component-centralizer kernel. Normality and
Sylow maximality place its image in the original Sylow subgroup, so it
also realizes the action on any subspace fixed by that Sylow centralizer.
Its faithful seed image has rank at most twice the field degree.

The application in `SeedAlternativesMovedExhaustionLinearThree` identifies
this kernel with C_A(L), giving the denominator bound in the final D.3.10
argument. Component-support and section-FF exclusions, U = W and Source325
assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.19 and the final D.3.10 argument, pp.203--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

private def naturalRestrictionEquiv
    (K : Subgroup H) (I : Submodule (ZMod 2) E)
    (hKI : K ≤ subspaceStabilizer ρ I) (F : BinaryField)
    (e : ActionEquiv (invariantSubspace ρ K I hKI).toRepresentation (linearNatural F 3)) :
    ActionEquiv ((subspaceImageRepresentation ρ I).comp
      (restrictedSubgroup ρ I K).subtype) (linearNatural F 3) := by
  let f := restrictedActionSurjection ρ I K hKI
  have hi : Function.Injective f := by
    intro a b he
    apply e.groupEquiv.injective
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
    have hh := congrArg (fun q : restrictedSubgroup ρ I K =>
      subspaceImageRepresentation ρ I q.val w) he
    exact (e.intertwines a w).symm.trans
      ((congrArg e.linearEquiv hh).trans (e.intertwines b w))
  let c : K ≃* restrictedSubgroup ρ I K :=
    MulEquiv.ofBijective f ⟨hi,restrictedActionSurjection_surjective ρ I K hKI⟩
  refine ⟨c.symm.trans e.groupEquiv,e.linearEquiv,?_⟩
  intro k v
  obtain ⟨k,rfl⟩ := c.surjective k
  change e.linearEquiv (subspaceImageRepresentation ρ I (c k).val v) =
    linearNatural F 3 (e.groupEquiv (c.symm (c k))) (e.linearEquiv v)
  rw [c.symm_apply_apply]
  exact e.intertwines k v

/-- On a natural SL₃ constituent of odd field degree, the literal image
of any stabilizing two-subgroup lies in the component image. -/
theorem restricted_two_subgroup_le_odd_linearThree
    (K : Subgroup H) [K.Normal] (I : Submodule (ZMod 2) E)
    (hKI : K ≤ subspaceStabilizer ρ I) (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (invariantSubspace ρ K I hKI).toRepresentation (linearNatural F 3))
    (A : Subgroup H) (hA : IsPGroup 2 A) :
    restrictedSubgroup ρ I A ≤ restrictedSubgroup ρ I K := by
  let P := restrictedSubgroup ρ I K
  let : P.Normal := Normal.map inferInstance (subspaceActionHom ρ I)
    (stabilizerRepresentation ρ I).asGroupHom.rangeRestrict_surjective
  let a := naturalRestrictionEquiv ρ K I hKI F e
  let σ := subspaceImageRepresentation ρ I
  let τ := a.linearEquiv.conjRingEquiv.toMonoidHom.comp σ
  have hf : Function.Injective τ := a.linearEquiv.conjRingEquiv.injective.comp
    (subspaceImageRepresentation_injective ρ I)
  have hn (k : P) (v : Fin 3 → F.Carrier) :
      τ k v = Matrix.mulVec (a.groupEquiv k).val v := by
    change a.linearEquiv (σ k (a.linearEquiv.symm v)) = _
    exact (a.intertwines k (a.linearEquiv.symm v)).trans
      (congrArg (linearNatural F 3 (a.groupEquiv k)) (a.linearEquiv.apply_symm_apply v))
  exact SL3OddNaturalNormalizer.two_subgroup_le_of_natural
    F.degree_pos ho F.card_eq P a.groupEquiv τ hf hn
    (restrictedSubgroup ρ I A) (hA.comap_subtype.map (subspaceActionHom ρ I))

/-- The same marked image has elementary rank at most twice the field degree. -/
theorem restricted_rank_le_odd_linearThree [Finite H]
    (K : Subgroup H) [K.Normal] (I : Submodule (ZMod 2) E)
    (hKI : K ≤ subspaceStabilizer ρ I) (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (invariantSubspace ρ K I hKI).toRepresentation (linearNatural F 3))
    (A : Subgroup H) (hAI : A ≤ subspaceStabilizer ρ I)
    (hA : IsElementaryAbelian 2 A) :
    rank (restrictedSubgroup ρ I A) ≤ 2 * F.degree := by
  let := hA
  let P := restrictedSubgroup ρ I K
  let B := restrictedSubgroup ρ I A
  have hBP : B ≤ P := restricted_two_subgroup_le_odd_linearThree ρ K I hKI F ho e A
    (hA.isPGroup 2 A)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_surjective
    (restrictedActionSurjection ρ I A hAI) (restrictedActionSurjection_surjective ρ I A hAI)
  let : IsElementaryAbelian 2 (B.subgroupOf P) := IsElementaryAbelian.subgroupOf hBP
  have hp : primeRank 2 P = 2 * F.degree := by
    rw [primeRank_congr 2 (naturalRestrictionEquiv ρ K I hKI F e).groupEquiv]
    exact Representation.HermitianTensorThree.ImageOuter.OuterRank.specialLinearThree_twoRank
      F.Carrier F.degree_pos F.card_eq
  change rank B ≤ 2 * F.degree
  by_cases hz : B = ⊥
  · simp only [hz,BinaryOffender.rank_bot,Nat.zero_le]
  have hn : B.subgroupOf P ≠ ⊥ := by
    intro he
    apply hz
    rw [←map_subgroupOf_eq_of_le hBP,he,Subgroup.map_bot]
  have hb : IsElementaryTwo (B.subgroupOf P) := ⟨hn,inferInstance⟩
  have hr := IsElementaryAbelian.primeRank_ge_of_card (B.subgroupOf P) hb.card_eq_two_pow_rank
  rwa [hp,rank_subgroupOf hBP] at hr
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

/-- The original stabilizing actor induces inner automorphisms on the
component, rather than merely having an abstract special-linear image. -/
theorem inner_on_component_of_odd_linearThree [Finite H]
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (I : Submodule (ZMod 2) E) (hKI : K ≤ subspaceStabilizer ρ I)
    (hIn : ¬ I ≤ fixedSpace ρ K)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (invariantSubspace ρ K I hKI).toRepresentation (linearNatural F 3))
    (A : Subgroup H) (hAI : A ≤ subspaceStabilizer ρ I) (hA : IsPGroup 2 A) :
    ∀ a ∈ A, ∃ k ∈ K, ∀ l ∈ K, a*l*a⁻¹ = k*l*k⁻¹ := by
  have hle := restricted_two_subgroup_le_odd_linearThree ρ K I hKI F ho e A hA
  intro a ha
  obtain ⟨k,hk,he⟩ := hle (show subspaceActionHom ρ I ⟨a,hAI ha⟩ ∈
    restrictedSubgroup ρ I A from ⟨⟨a,hAI ha⟩,ha,rfl⟩)
  have hker : k.val⁻¹ * a ∈ subspaceKernel ρ I ⊤ := by
    refine ⟨mem_top _,fun v hv => ?_⟩
    have hev : ρ k.val v = ρ a v :=
      congrArg (fun q : subspaceActionImage ρ I => (q.val.val ⟨v,hv⟩ : E)) he
    rw [map_mul,Module.End.mul_apply,←hev,←Module.End.mul_apply,←map_mul,
      inv_mul_cancel,map_one,Module.End.one_apply]
  have hcent := subspaceKernel_le_component_centralizer ρ K I hKI hIn ⊤ hker
  refine ⟨k.val,hk,fun l hl => ?_⟩
  have hh := hcent l hl
  have heq : a*l = k.val*l*k.val⁻¹*a := by
    calc
      a*l = k.val*((k.val⁻¹*a)*l) := by group
      _ = k.val*(l*(k.val⁻¹*a)) := congrArg (fun x => k.val*x) hh.symm
      _ = k.val*l*k.val⁻¹*a := by group
  rw [heq]
  group
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

/-- Inner coordinates for the entire stabilizing two-subgroup, as a
homomorphism to the literal component with its exact centralizer kernel. -/
theorem exists_inner_lift_of_odd_linearThree
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (I : Submodule (ZMod 2) E) (hKI : K ≤ subspaceStabilizer ρ I)
    (hIn : ¬ I ≤ fixedSpace ρ K)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (invariantSubspace ρ K I hKI).toRepresentation (linearNatural F 3))
    (A : Subgroup H) (hAI : A ≤ subspaceStabilizer ρ I) (hA : IsPGroup 2 A) :
    ∃ f : A →* K,
      (∀ (a : A) (v : I), ρ (f a : H) v.val = ρ a.val v.val) ∧
      (∀ (a : A) (l : K), a.val*l.val*a.val⁻¹ = (f a : H)*l.val*(f a : H)⁻¹) ∧
      f.ker = (centralizer (K : Set H)).subgroupOf A := by
  let P := restrictedSubgroup ρ I K
  let b := naturalRestrictionEquiv ρ K I hKI F e
  have hle := restricted_two_subgroup_le_odd_linearThree ρ K I hKI F ho e A hA
  let q : A →* P := (subgroupActionHom ρ I A hAI).codRestrict P (fun a =>
    hle ⟨⟨a.val,hAI a.property⟩,a.property,rfl⟩)
  let f : A →* K := (b.groupEquiv.trans e.groupEquiv.symm).toMonoidHom.comp q
  have he (a : A) (v : I) : ρ (f a : H) v.val = ρ a.val v.val := by
    have hh := b.intertwines (q a) v
    have hk := e.intertwines (f a) v
    have hm : e.groupEquiv (f a) = b.groupEquiv (q a) := e.groupEquiv.apply_symm_apply _
    rw [hm] at hk
    have ht := e.linearEquiv.injective (hk.trans hh.symm)
    exact congrArg Subtype.val ht
  have hcent (a : A) : (f a : H)⁻¹*a.val ∈ centralizer (K : Set H) := by
    apply subspaceKernel_le_component_centralizer ρ K I hKI hIn ⊤
    refine ⟨mem_top _,fun v hv => ?_⟩
    rw [map_mul,Module.End.mul_apply,←he a ⟨v,hv⟩,
      ←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  refine ⟨f,he,?_,?_⟩
  · intro a l
    have hh := hcent a l.val l.property
    calc
      a.val*l.val*a.val⁻¹ = (f a : H)*(((f a : H)⁻¹*a.val)*l.val)*a.val⁻¹ := by group
      _ = (f a : H)*(l.val*((f a : H)⁻¹*a.val))*a.val⁻¹ := by rw [←hh]
      _ = (f a : H)*l.val*(f a : H)⁻¹ := by group
  · ext a
    change f a = 1 ↔ a.val ∈ centralizer (K : Set H)
    constructor
    · intro hz
      simpa only [hz,Subgroup.coe_one,inv_one,one_mul] using hcent a
    · intro hc
      have hcomm : (f a : H) ∈ centralizer (K : Set H) := by
        have hmem := (centralizer (K : Set H)).mul_mem hc
          ((centralizer (K : Set H)).inv_mem (hcent a))
        simpa only [mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left] using hmem
      have hz : Odd (Nat.card (center K)) := by
        rw [Nat.card_congr (centerCongr e.groupEquiv).toEquiv]
        exact Matrix.SL3.odd_card_center F.Carrier
      let z : center K := ⟨f a,mem_center_iff.mpr (fun l =>
        Subtype.ext (hcomm l.val l.property))⟩
      obtain ⟨r,hr⟩ := hA a
      have hp : z ^ 2 ^ r = 1 := by
        apply Subtype.ext
        change (f a)^2^r = 1
        rw [←map_pow,hr,map_one]
      have hzone : z = 1 := orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (hz.coprime_two_right.pow_right r)
          (orderOf_dvd_natCard z) (orderOf_dvd_of_pow_eq_one hp))
      exact congrArg Subtype.val hzone
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H : Type*} [Group H] [Finite H]
/-- An inner lift of an actor in the original Sylow subgroup lies in its
intersection with the normal component. -/
theorem inner_lift_mem_sylow
    (S : Sylow 2 H) (K A : Subgroup H) [K.Normal]
    (hAS : A ≤ S) (f : A →* K)
    (he : ∀ (a : A) (l : K), a.val*l.val*a.val⁻¹ = (f a : H)*l.val*(f a : H)⁻¹) :
    ∀ a : A, (f a : H) ∈ S := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hn : f.range ≤ normalizer (P : Set K) := by
    apply le_normalizer_iff.mpr
    rintro k ⟨a,rfl⟩ l hl
    rw [hP] at hl ⊢
    change (f a : H)*l.val*(f a : H)⁻¹ ∈ S
    rw [←he]
    exact (S : Subgroup H).mul_mem ((S : Subgroup H).mul_mem (hAS a.property) hl)
      ((S : Subgroup H).inv_mem (hAS a.property))
  have hp : IsPGroup 2 f.range := (S.isPGroup'.to_le hAS).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hle : f.range ≤ P := by
    calc
      f.range ≤ f.range ⊓ normalizer (P : Set K) := le_inf le_rfl hn
      _ = f.range ⊓ (P : Subgroup K) := hp.inf_normalizer_sylow P
      _ ≤ P := inf_le_right
  intro a
  have hh := hle (show f a ∈ f.range from ⟨a,rfl⟩)
  rwa [hP] at hh
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

/-- When the Sylow component centralizer fixes W, the same inner lift acts
correctly on all of W, and its image stays in the original Sylow subgroup. -/
theorem exists_sylow_inner_lift_on_fixed_subspace
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (I W : Submodule (ZMod 2) E) (hKI : K ≤ subspaceStabilizer ρ I)
    (hIn : ¬ I ≤ fixedSpace ρ K)
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (invariantSubspace ρ K I hKI).toRepresentation (linearNatural F 3))
    (S : Sylow 2 H) (hW : W ≤ fixedSpace ρ ((S : Subgroup H) ⊓ centralizer (K : Set H)))
    (A : Subgroup H) (hAS : A ≤ S) (hAI : A ≤ subspaceStabilizer ρ I) :
    ∃ f : A →* K,
      f.ker = (centralizer (K : Set H)).subgroupOf A ∧
      (∀ a : A, (f a : H) ∈ S) ∧
      (∀ (a : A) (l : K), a.val*l.val*a.val⁻¹ = (f a : H)*l.val*(f a : H)⁻¹) ∧
      (∀ (a : A) (v : W), ρ (f a : H) v.val = ρ a.val v.val) := by
  obtain ⟨f,hi,he,hker⟩ := exists_inner_lift_of_odd_linearThree
    ρ K I hKI hIn F ho e A hAI (S.isPGroup'.to_le hAS)
  have hs := inner_lift_mem_sylow S K A hAS f he
  refine ⟨f,hker,hs,he,?_⟩
  intro a v
  have hc : (f a : H)⁻¹*a.val ∈ centralizer (K : Set H) := by
    apply subspaceKernel_le_component_centralizer ρ K I hKI hIn ⊤
    refine ⟨mem_top _,fun w hw => ?_⟩
    rw [map_mul,Module.End.mul_apply,←hi a ⟨w,hw⟩,
      ←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hf := hW v.property ⟨(f a : H)⁻¹*a.val,
    (S : Subgroup H).mul_mem ((S : Subgroup H).inv_mem (hs a)) (hAS a.property),hc⟩
  change ρ ((f a : H)⁻¹*a.val) v.val = v.val at hf
  calc
    ρ (f a : H) v.val = ρ (f a : H) (ρ ((f a : H)⁻¹*a.val) v.val) := congrArg _ hf.symm
    _ = ρ a.val v.val := by rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel_left]
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
