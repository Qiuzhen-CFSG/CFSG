module
public import Theory.Representation.SLThreeCentralExtension.CoverOrbits
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
public import Theory.Representation.NormalElementaryQuotient.BestOffender
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.GroupTheory.SubgroupProductCard

/-!
# Thompson fixed vectors in a central natural binary three-space cover

In dimension four every best offender is a four-group fixing a plane.
Two such subgroups of a two-group in SL₃(2) intersect nontrivially, so their
fixed planes agree. The actual maximum-elementary images therefore have a
common fixed vector outside the central kernel. Transitivity outside that
kernel gives a fixed representative in every orbit of the original cover.

Source: Aschbacher--Smith, B.2.5 and B.4.8(2), used in 10.2.9, pp.76,91,751.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) BinaryLinearThree.Group V)
  (p : σ.IntertwiningMap W) (hp : IsCover p)
  (hd : Module.finrank (ZMod 2) V = 4)

include p hp hd

private theorem best_dimensions {A : Subgroup BinaryLinearThree.Group}
    (hA : IsBestOffender σ A) :
    Nat.card A = 4 ∧ Module.finrank (ZMod 2) (fixedSpace σ A) = 2 := by
  let : IsElementaryAbelian 2 A := hA.1.2
  let f := MulAut.conj (G := BinaryLinearThree.Group)
  have hi : Function.Injective f :=
    MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have hc := FourGroupGeometry.elementary_card_le_four (A.map f)
    (IsElementaryAbelian.map f)
  rw [Subgroup.card_map_of_injective hi] at hc
  have hr : rank A ≤ 2 := Nat.log_monotone (b := 2) hc
  obtain ⟨a,ha,hne⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hinv := NaturalExtension.involution_codim_of_commutator_top σ hd hp.2.2 a ho
  have hmono := Submodule.finrank_mono
    (fixedSpace_antitone σ (zpowers_le.mpr ha))
  have hf := fixedCodim_add_finrank σ (zpowers a)
  have hAfix := fixedCodim_add_finrank σ A
  have hoff := (hA.isOffender σ).2
  have hr' : rank A = 2 := by omega
  refine ⟨?_,by omega⟩
  rw [hA.1.card_eq_two_pow_rank,hr']
  decide

private theorem best_fixed_eq {A B R : Subgroup BinaryLinearThree.Group}
    (hR : IsPGroup 2 R) (hAR : A ≤ R) (hBR : B ≤ R)
    (hA : IsBestOffender σ A) (hB : IsBestOffender σ B) :
    fixedSpace σ A = fixedSpace σ B := by
  obtain ⟨S,hRS⟩ := hR.exists_le_sylow
  have hS : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity,Matrix.PSL3Two.card_SL]
    decide +kernel
  obtain ⟨hAc,hAf⟩ := best_dimensions σ p hp hd hA
  obtain ⟨hBc,hBf⟩ := best_dimensions σ p hp hd hB
  have hne : A ⊓ B ≠ ⊥ := by
    intro hz
    let f : ((A : Set BinaryLinearThree.Group) * (B : Set BinaryLinearThree.Group)) → (S : Subgroup BinaryLinearThree.Group) :=
      fun x => ⟨x,by
        obtain ⟨a,ha,b,hb,he⟩ := x.property
        rw [←he]
        exact (S : Subgroup BinaryLinearThree.Group).mul_mem (hRS (hAR ha)) (hRS (hBR hb))⟩
    have hi : Function.Injective f := fun a b he => Subtype.ext (congrArg (fun z : (S : Subgroup BinaryLinearThree.Group) => (z : BinaryLinearThree.Group)) he)
    have hle := Nat.card_le_card_of_injective f hi
    have hc := card_set_mul_mul_card_inf A B
    rw [hz,card_bot,mul_one,hAc,hBc] at hc
    rw [hS] at hle
    omega
  obtain ⟨a,ha,ha1⟩ := (A ⊓ B).bot_or_exists_ne_one.resolve_left hne
  let : IsElementaryAbelian 2 A := hA.1.2
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha.1) ha1
  have hinv := NaturalExtension.involution_codim_of_commutator_top σ hd hp.2.2 a ho
  have hdim : Module.finrank (ZMod 2) (fixedSpace σ (zpowers a)) = 2 := by
    have := fixedCodim_add_finrank σ (zpowers a)
    omega
  exact (Submodule.eq_of_le_of_finrank_eq
    (fixedSpace_antitone σ (zpowers_le.mpr ha.1)) (hAf.trans hdim.symm)).trans
    (Submodule.eq_of_le_of_finrank_eq
      (fixedSpace_antitone σ (zpowers_le.mpr ha.2)) (hBf.trans hdim.symm)).symm

variable {H : Type*} [_root_.Group H] [Finite H]

/-- The original maximum-elementary Thompson subgroup fixes a vector outside
its module's central kernel. The actor map is the literal conjugation map. -/
theorem thompson_fixed_outside_kernel
    (U S : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (hS : IsPGroup 2 S)
    (π : H →* BinaryLinearThree.Group) (hπ : π.ker = centralizer (U : Set H))
    (E : Additive U ≃ₗ[ZMod 2] V)
    (he : ∀ h u, E (NoncentralChiefRefinement.normalRepresentation U h u) = σ (π h) (E u)) :
    ∃ x : V, p x ≠ 0 ∧ ∀ j ∈ elementaryAbelianMaxJ S, σ (π j) x = x := by
  let q := π.rangeRestrict
  have hk : q.ker = centralizer (U : Set H) := π.ker_rangeRestrict.trans hπ
  let ρ := NormalElementaryQuotient.representation U q π.rangeRestrict_surjective hk
  have heq : ∀ g u, E (ρ g u) = σ g.val (E u) := by
    intro g u
    obtain ⟨h,rfl⟩ := π.rangeRestrict_surjective g
    have hr : ρ (q h) u = NoncentralChiefRefinement.normalRepresentation U h u := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply U q π.rangeRestrict_surjective hk h u
    rw [hr]
    exact he h u
  have hbest (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups S)
      (hne : A.map π ≠ ⊥) : IsBestOffender σ (A.map π) := by
    have hn : A.map q ≠ ⊥ := by
      intro hz
      apply hne
      have hmap : (A.map q).map π.range.subtype = A.map π := by rw [map_map]; rfl
      rw [←hmap,hz,Subgroup.map_bot]
    have hb := NormalElementaryQuotient.maxElementary_isBestOffender U q
      π.rangeRestrict_surjective hk S A hUS hA hn
    have ht := hb.map_of_fixedCodim ρ σ π.range.subtype π.range.subtype_injective
      (fixedCodim_map_equivariant ρ σ π.range.subtype E heq)
    have hmap : (A.map q).map π.range.subtype = A.map π := by rw [map_map]; rfl
    rwa [hmap] at ht
  have hkd : Module.finrank (ZMod 2) p.toLinearMap.ker = 1 := by
    have h := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp.1,finrank_top,Module.finrank_fin_fun,hd] at h
    omega
  by_cases hex : ∃ A ∈ elementaryAbelianMaxSubgroups S, A.map π ≠ ⊥
  · obtain ⟨A,hA,hAn⟩ := hex
    have hAb := hbest A hA hAn
    have hnle : ¬ fixedSpace σ (A.map π) ≤ p.toLinearMap.ker := by
      intro hle
      have h := Submodule.finrank_mono hle
      rw [(best_dimensions σ p hp hd hAb).2,hkd] at h
      omega
    obtain ⟨x,hx,hpx⟩ := SetLike.not_le_iff_exists.mp hnle
    refine ⟨x,hpx,?_⟩
    let : MulAction BinaryLinearThree.Group V := MulAction.compHom V σ
    let St : Subgroup H := (MulAction.stabilizer BinaryLinearThree.Group x).comap π
    have hj : elementaryAbelianMaxJ S ≤ St := by
      apply sSup_le
      intro B hB b hb
      by_cases hBn : B.map π = ⊥
      · have hz : π b = 1 := mem_bot.mp (hBn ▸ mem_map_of_mem π hb)
        change σ (π b) x = x
        rw [hz,map_one]
        rfl
      · have hf := best_fixed_eq σ p hp hd (hS.map π) (map_mono hA.1)
          (map_mono hB.1) hAb (hbest B hB hBn)
        exact (hf ▸ hx) ⟨π b,mem_map_of_mem π hb⟩
    exact fun j hj' => hj hj'
  · push Not at hex
    obtain ⟨x,hx⟩ := hp.1 (![1,0,0] : Vector)
    refine ⟨x,by rw [hx]; decide,?_⟩
    have hj : elementaryAbelianMaxJ S ≤ π.ker :=
      sSup_le fun A hA => (map_eq_bot_iff A).mp (hex A hA)
    intro j hj'
    rw [show π j = 1 from hj hj',map_one]
    rfl

/-- Every vector of the literal central cover is fixed by a conjugate of
the original Thompson image, including vectors in the fixed kernel. -/
theorem thompson_conjugate_fixed
    (U S : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (hS : IsPGroup 2 S)
    (π : H →* BinaryLinearThree.Group) (hπ : π.ker = centralizer (U : Set H))
    (E : Additive U ≃ₗ[ZMod 2] V)
    (he : ∀ h u, E (NoncentralChiefRefinement.normalRepresentation U h u) = σ (π h) (E u))
    (v : V) : ∃ g : BinaryLinearThree.Group,
      ∀ j ∈ elementaryAbelianMaxJ S, σ (g * π j * g⁻¹) v = v := by
  by_cases hv : p v = 0
  · exact ⟨1,fun j _ => hp.2.1 hv _⟩
  obtain ⟨x,hx,hJ⟩ := thompson_fixed_outside_kernel σ p hp hd U S hUS hS π hπ E he
  have hkn : p.toLinearMap.ker ≠ ⊥ := by
    intro hz
    have h := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp.1,finrank_top,Module.finrank_fin_fun,hz,finrank_bot,hd] at h
    omega
  obtain ⟨g,hg⟩ := transitive_outside_kernel_of_cover p hp hkn x v hx hv
  refine ⟨g,fun j hj => ?_⟩
  rw [←hg,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,σ.inv_self_apply,hJ j hj]
end Representation.OneCohomology.SLThreeCentralExtension
