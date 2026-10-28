module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedEndpointConstruction
public import Theory.Representation.SL2FourNaturalOrbits.CubicFixedSpace
public import Theory.SpecificGroups.SymmetricSix.CubicCentralizerOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.GroupTheory.CoprimeSubgroupCentralizer

/-!
# The actual cubic centralizer in the full sixteen normalizer

The marked natural action makes a cubic fixed-free on the original radical.
Coprime centralizer lifting therefore identifies its full normalizer
centralizer with the centralizer of its literal six-letter quotient image.
The latter has order eighteen. No ambient cubic-centralizer recognition or
relation between different endpoint reflections is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} [IsElementaryAbelian 2 A]

omit [Finite G] in
/-- Every cubic in the chosen natural endpoint fixes only the identity in
its original elementary radical. -/
theorem NaturalEndpointData.cubic_radical_centralizer
    (d : NaturalEndpointData A) (t : G) (ht : t ∈ d.carrier) (ht3 : orderOf t = 3) :
    A ⊓ centralizer ({t} : Set G) = ⊥ := by
  let T : d.carrier := ⟨t,ht⟩
  have hT : orderOf T = 3 := (orderOf_coe T).symm.trans ht3
  have hk : IsPGroup 2 d.quotient.ker := by
    rw [d.quotient_kernel]
    exact (IsElementaryAbelian.isPGroup (p := 2) (G := A)).comap_subtype
  have hqT : orderOf (d.quotient T) = 3 :=
    (d.quotient.orderOf_map_eq_of_coprime_of_isPGroup_ker hk T
      (by rw [hT]; decide)).trans hT
  apply bot_unique
  rintro a ⟨ha,hac⟩
  let aA : A := ⟨a,ha⟩
  have hfix : A.normalizerMonoidHom (inclusion d.normalizes T) aA = aA := by
    apply Subtype.ext
    change t*a*t⁻¹=a
    rw [← mem_centralizer_singleton_iff.mp hac,mul_inv_cancel_right]
  have hn := d.action T aA
  rw [hfix] at hn
  have hz := Representation.SL2FourNatural.cubic_fixed_eq_zero (d.quotient T) hqT
    (d.coordinates aA).toAdd (congrArg Multiplicative.toAdd hn).symm
  have he : aA=1 := d.coordinates.injective (by
    apply Multiplicative.toAdd.injective
    simpa using hz)
  exact congrArg Subtype.val he

/-- The full original sixteen-normalizer has an order-eighteen cubic
centralizer, identified by the same quotient map with its six-letter
centralizer. The original elementary radical is the whole quotient kernel. -/
theorem NaturalEndpointData.cubic_full_normalizer_centralizer
    (d : NaturalEndpointData A) (t : G) (ht : t ∈ d.carrier) (ht3 : orderOf t = 3) :
    Nat.card (normalizer (A : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 18 ∧
    ∃ f : normalizer (A : Set G) →* Equiv.Perm (Fin 6), Function.Surjective f ∧
      f.ker = A.subgroupOf (normalizer (A : Set G)) ∧
      orderOf (f ⟨t,d.normalizes ht⟩) = 3 ∧
      ∃ e : (normalizer (A : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ≃*
          centralizer ({f ⟨t,d.normalizes ht⟩} : Set (Equiv.Perm (Fin 6))),
        ∀ x, (e x : Equiv.Perm (Fin 6)) = f ⟨x,x.property.1⟩ := by
  let N := normalizer (A : Set G)
  let K := A.subgroupOf N
  let σ := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  let f : N →* Equiv.Perm (Fin 6) := σ.toMonoidHom.comp
    (d.symplectic_quotient.toMonoidHom.comp (QuotientGroup.mk' K))
  have hf : Function.Surjective f := σ.surjective.comp
    (d.symplectic_quotient.surjective.comp (QuotientGroup.mk'_surjective K))
  have hk : f.ker=K := by
    ext x
    change σ (d.symplectic_quotient (QuotientGroup.mk x)) = 1 ↔ (x : G) ∈ A
    rw [σ.map_eq_one_iff,d.symplectic_quotient.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (IsElementaryAbelian.isPGroup (p := 2) (G := A)).comap_subtype
  have hA16 : Nat.card A = 16 := by
    rw [Nat.card_congr d.coordinates.toEquiv]
    exact (Nat.card_eq_fintype_card (α := Representation.SL2FourNatural.V)).trans
      Representation.SL2FourNatural.card_vector
  have hk16 : Nat.card f.ker=16 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv,hA16]
  let T : N := ⟨t,d.normalizes ht⟩
  have hT : orderOf T=3 := (orderOf_coe T).symm.trans ht3
  have hfT : orderOf (f T)=3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hkp T (by rw [hT]; decide)).trans hT
  have himage : (centralizer ({T} : Set N)).map f =
      centralizer ({f T} : Set (Equiv.Perm (Fin 6))) := by
    have hp : IsPGroup 3 (zpowers T) := IsPGroup.of_card (n:=1)
      (by rw [Nat.card_zpowers,hT,pow_one])
    have hh := map_centralizer_eq_of_isPGroup_of_surjective_coprime 3 (zpowers T) hp f hf
      (by rw [hk16]; decide)
    rw [MonoidHom.map_zpowers] at hh
    simpa only [zpowers_eq_closure,centralizer_closure] using hh
  let C := N ⊓ centralizer ({t} : Set G)
  let j : C →* N := inclusion inf_le_left
  let q : C →* centralizer ({f T} : Set (Equiv.Perm (Fin 6))) :=
    (f.comp j).codRestrict _ (fun x => mem_centralizer_singleton_iff.mpr (by
      change f (j x) * f T = f T * f (j x)
      rw [←map_mul,←map_mul]
      exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))))
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    apply bot_unique
    intro x hx
    have hxk : j x ∈ f.ker := congrArg Subtype.val hx
    have hxA : (x : G) ∈ A := by
      have hh : j x ∈ K := hk ▸ hxk
      exact hh
    have hxe : (x : G) ∈ A ⊓ centralizer ({t} : Set G) := ⟨hxA,x.property.2⟩
    rw [d.cubic_radical_centralizer t ht ht3] at hxe
    exact Subtype.ext hxe
  have hqs : Function.Surjective q := by
    intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ (centralizer ({T} : Set N)).map f :=
      himage.symm ▸ y.property
    obtain ⟨x,hx,hxy⟩ := hy
    have hxC : (x : G) ∈ C := ⟨x.property,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
    exact ⟨⟨x,hxC⟩,Subtype.ext hxy⟩
  let e := MulEquiv.ofBijective q ⟨hqi,hqs⟩
  have hC18 : Nat.card C=18 := (Nat.card_congr e.toEquiv).trans
    (Theory.SpecificGroups.SymmetricSix.cubic_centralizer_card (f T) hfT)
  exact ⟨hC18,f,hf,hk,hfT,e,fun _ => rfl⟩

end CFSG.Quasithin.HigmanSims
