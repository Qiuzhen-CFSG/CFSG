module
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.SmallTwoSubgroups
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.TwoFactorGeometry
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.NineSupport
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.Quotient
public import Theory.Representation.RepEquiv
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NineReducible
public import Theory.Representation.BinaryOffender.MovedDimension
/-!
# The irreducible ambient extension of the elementary-nine endpoint

The normal nine-core has two cubic supports and hence embeds the ambient
action into O₄⁺(2). Cubic ratio two excludes an elementary four-group, so
Sylow two-subgroups have order at most four. The inverted order-eighteen
endpoint is reducible; ambient irreducibility therefore forces order 36
and cyclic Sylow subgroups of order four. The literal nine-kernel is then
the two-residual.

Source: Aschbacher–Smith 15.1.2(5), printed p.1086.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
set_option synthInstance.maxSize 10000

private theorem cyclic_of_card_four_not_elementary {B : Type*} [Group B] [Finite B]
    (hB : Nat.card B = 4) (hne : ¬ IsElementaryAbelian 2 B) : IsCyclic B := by
  by_contra hn
  apply hne
  let : IsMulCommutative B := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hB
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro b
  have hd := orderOf_dvd_natCard b
  rw [hB] at hd
  have h4 : orderOf b ≠ 4 := fun h => hn (isCyclic_of_orderOf_eq_card b (h.trans hB.symm))
  have hdiv : orderOf b ∣ 2 := by
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf b ∣ 2^2 by simpa using hd)
    rw [he]
    interval_cases i <;> norm_num at he h4 ⊢; omega
  exact orderOf_dvd_iff_pow_eq_one.mp hdiv

theorem nine_sylow_card_le_four (hf : Function.Injective ρ)
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (hdim : Module.finrank (ZMod 2) V = 4)
    (hm : subspaceCommutator ρ ⊤ P = ⊤) (hq : cubicRatio ρ = 2) (S : Sylow 2 G) :
    Nat.card S ≤ 4 := by
  obtain ⟨d⟩ := FittingConfigurations.supportFactors_of_nine_four_moved ρ hf P hP hdim hm
  obtain ⟨c,f,hfi,hcoord⟩ := d.exists_isometry_embedding ρ hf (d.factor_conj_closed ρ hf)
  let L := (S : Subgroup G).map f
  have he : S ≃* L := Subgroup.equivMapOfInjective (S : Subgroup G) f hfi
  rw [Nat.card_congr he.toEquiv]
  apply OrthogonalFourBinary.SylowGeometry.two_subgroup_no_four_card_le_four L (S.isPGroup'.map f)
  intro A hA hc
  let : IsElementaryAbelian 2 A := hA
  let B := A.comap he.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.comap_of_injective _ he.injective A
  let C := B.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have hcB : Nat.card B = 4 := by
    have hmap : B.map he.toMonoidHom = A := map_comap_eq_self_of_surjective he.surjective A
    exact (card_map_of_injective he.injective).symm.trans (hmap ▸ hc)
  have hcC : Nat.card C = 4 := (card_map_of_injective (S : Subgroup G).subtype_injective).trans hcB
  exact no_elementary_four_of_four_dimensional_cubicRatio_two ρ hdim hq C inferInstance hcC

theorem LocalGeneration.nine_ambient_extension
    (hf : Function.Injective ρ) (K : Subgroup G) [K.Normal]
    (l : LocalGeneration (ρ.comp K.subtype)) (hq : cubicRatio ρ = 2)
    (hi : IsIrreducible ρ) :
    letI := BinaryGroupAction.action (ρ.comp K.subtype)
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := l.normal
    Section02.ElementaryNineEndpoint (V := Multiplicative V) l.kernel l.involution →
    Nat.card G = 36 ∧ l.kernel.map K.subtype = pResidual 2 G ∧
      (∀ S : Sylow 2 G, IsCyclic S ∧ Nat.card S = 4) := by
  let := BinaryGroupAction.action (ρ.comp K.subtype)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let := l.normal
  intro h9
  let := h9.kernel_elementary
  have hk := l.kernel_eq_threeCore_of_elementary_nine h9.kernel_elementary h9.card_kernel
  let P := l.kernel.map K.subtype
  let : P.Normal := by
    change (l.kernel.map K.subtype).Normal
    rw [hk]
    infer_instance
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.map _
  have hcP : Nat.card P = 9 := (card_map_of_injective K.subtype_injective).trans h9.card_kernel
  have hdim : Module.finrank (ZMod 2) V = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hc : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact hc.symm.trans ((Nat.card_congr (Multiplicative.toAdd (α := V))).symm.trans h9.card_module)
  have hm : subspaceCommutator ρ ⊤ P = ⊤ := by
    rw [←subspaceCommutator_comp_map]
    exact l.moved
  obtain ⟨d⟩ := FittingConfigurations.supportFactors_of_nine_four_moved ρ hf P hcP hdim hm
  have hupper := SmallThree.two_supports_card_dvd_seventy_two ρ hf P d
  have hcK : Nat.card K = 18 := by
    have ht : Nat.card (zpowers l.involution) = 2 := by rw [Nat.card_zpowers,l.order_two]
    have hd : Disjoint l.kernel (zpowers l.involution) := IsPGroup.disjoint_of_coprime
      (IsElementaryAbelian.isPGroup 3 l.kernel)
      (IsPGroup.of_card (n := 1) (by simpa using ht)) (by decide)
    have hcard := card_sup_eq_mul_of_normalizes_of_disjoint l.kernel (zpowers l.involution)
      le_normalizer_of_normal hd
    rw [l.generated,card_top,h9.card_kernel,ht] at hcard
    exact hcard
  have hne : K ≠ ⊤ := by
    intro htop
    have hir : IsIrreducible (ρ.comp K.subtype) :=
      (irreducible_comp_surjective_iff K.subtype (by
        intro a
        exact ⟨⟨a,htop ▸ mem_top a⟩,rfl⟩) ρ).mpr hi
    exact l.not_irreducible_of_elementary_nine (hf.comp K.subtype_injective) h9 hir
  have hlower : 18 ∣ Nat.card G := hcK ▸ K.card_subgroup_dvd_card
  have hcG : Nat.card G = 36 := by
    obtain ⟨n,hn⟩ := hlower
    have hd : n ∣ 4 := by
      apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 18)).mp
      simpa only [hn] using hupper
    have hnpos : 0 < n := by have := Nat.card_pos (α := G); omega
    have hnle : n ≤ 4 := Nat.le_of_dvd (by decide) hd
    interval_cases n
    · exfalso
      apply hne
      apply eq_top_of_card_eq
      omega
    · omega
    · norm_num at hd
    · have hS := nine_sylow_card_le_four hf P hcP hdim hm hq (Classical.choice (inferInstance : Nonempty (Sylow 2 G)))
      rw [Sylow.card_eq_multiplicity,hn] at hS
      have h72 : Nat.factorization 72 2 = 3 := by decide +kernel
      norm_num only [h72,show 18*4=72 from rfl] at hS
  have hres : pResidual 2 G = P := by
    apply le_antisymm
    · apply (pResidual_le_iff_isPGroup_quotient 2 P).mpr
      apply IsPGroup.of_card (n := 2)
      have hh := P.card_mul_index
      rw [hcP,hcG] at hh
      rw [←Subgroup.index_eq_card]
      omega
    · intro a ha
      apply mem_pResidual_of_orderOf_coprime
      have hd : orderOf a ∣ 9 := by
        have hh := orderOf_dvd_natCard (⟨a,ha⟩ : P)
        rw [← orderOf_injective P.subtype P.subtype_injective, hcP] at hh
        exact hh
      exact (by decide : Nat.Coprime 2 9).of_dvd_right hd
  refine ⟨hcG,hres.symm,?_⟩
  intro S
  have hcS : Nat.card S = 4 := by
    rw [Sylow.card_eq_multiplicity,hcG]
    decide +kernel
  refine ⟨cyclic_of_card_four_not_elementary hcS ?_,hcS⟩
  intro hS
  exact no_elementary_four_of_four_dimensional_cubicRatio_two ρ hdim hq (S : Subgroup G) hS hcS

end CFSG.Quasithin.ChapterD.CyclicSource
