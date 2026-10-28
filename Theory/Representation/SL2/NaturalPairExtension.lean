module
public import Theory.Representation.SL2.NaturalSelfExtension
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.SL2.OddMinimalNatural
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryConjugationSection.NaturalCentralExtension
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.Representation.BinaryConjugationSection.QuotientSection

/-!
# A natural-pair central extension for SL₂

A binary module whose submodule and quotient are both natural splits by
the existing natural self-extension theorem. Projecting its two natural
coordinates gives two invariant group kernels with intersection W.
The natural-by-natural central-extension theorem makes each corresponding
quotient elementary, so every square of the original Q lies in W.

The final theorem permits different field markings and covering maps on
the two layers. Their common kernel constructs the actual comparison
homomorphism; all coordinate maps and original conjugation actions are
retained. The DGS85 (12.9) consumer uses this as the precise instance of
(5.17) needed on printed p.190.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
local instance naturalPairBinaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable [AddCommGroup V] [Module (ZMod 2) V]

/-- Natural constituents split with actual equivariant coordinates. -/
theorem pair_equiv_of_natural_factors
    (ρ : Representation (ZMod 2) SL(2,F) V) (U : Subrepresentation ρ)
    (hU : BinarySmall.IsNatural U.toRepresentation)
    (hQ : BinarySmall.IsNatural U.quotientRepresentation) :
    Nonempty (ρ.Equiv ((BinarySmall.natural (K := F)).prod BinarySmall.natural)) := by
  obtain ⟨eU⟩ := hU
  obtain ⟨eQ⟩ := hQ
  obtain ⟨K,hK,eK,heK⟩ := SL2NaturalSelfExtension.exists_natural_complement ρ U
    eU.toLinearEquiv eQ.toLinearEquiv
    (fun g v => LinearMap.congr_fun (eU.isIntertwining' g) v)
    (fun g v => LinearMap.congr_fun (eQ.isIntertwining' g) v)
  let p := Submodule.prodEquivOfIsCompl U.toSubmodule K.toSubmodule hK
  let e := p.symm.trans (eU.toLinearEquiv.prodCongr eK)
  refine ⟨Representation.Equiv.mk e ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨⟨u,k⟩,rfl⟩ := p.surjective v
  have hp : ρ g (p (u,k)) = p (U.toRepresentation g u,K.toRepresentation g k) := by
    change ρ g ((u : V)+(k : V)) = _
    rw [map_add]
    rfl
  change e (ρ g (p (u,k))) = _
  rw [hp]
  change (eU (p.symm (p (U.toRepresentation g u,K.toRepresentation g k))).1,
    eK (p.symm (p (U.toRepresentation g u,K.toRepresentation g k))).2) = _
  rw [p.symm_apply_apply]
  have he : e (p (u,k)) = (eU u,eK k) := by
    change (eU.toLinearEquiv.prodCongr eK) (p.symm (p (u,k))) = _
    rw [p.symm_apply_apply]
    rfl
  change (eU (U.toRepresentation g u),eK (K.toRepresentation g k)) =
    (BinarySmall.natural.prod BinarySmall.natural) g (e (p (u,k)))
  rw [he]
  apply Prod.ext
  · exact LinearMap.congr_fun (eU.isIntertwining' g) u
  · exact heK g k

variable {G : Type*} [Group G]
/-- Central extensions with a natural quotient and a pair of natural kernel modules
are elementary for the same nonbinary covering actor. -/
theorem natural_pair_central_extension_elementary
    (H Q C W : Subgroup G) (hCQ : C ≤ Q) (hQH : Q ≤ H)
    [(W.subgroupOf Q).Normal]
    (π : H →* SL(2,F)) (hπ : Function.Surjective π) (hk : π.ker = Q.subgroupOf H)
    (cC : BinaryConjugationSection H C W
      (((BinarySmall.natural (K := F)).prod BinarySmall.natural).comp π))
    (cQ : BinaryConjugationSection H Q C ((BinarySmall.natural (K := F)).comp π))
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc : ⁅Q,C⁆ ≤ W) :
    IsElementaryAbelian 2 (Q ⧸ W.subgroupOf Q) := by
  let N := Fin 2 → F
  let f₁ : C →* Multiplicative N :=
    (MonoidHom.fst (Multiplicative N) (Multiplicative N)).comp cC.coordinates
  let f₂ : C →* Multiplicative N :=
    (MonoidHom.snd (Multiplicative N) (Multiplicative N)).comp cC.coordinates
  let Z₁ := f₁.ker.map C.subtype
  let Z₂ := f₂.ker.map C.subtype
  have hZ₁C : Z₁ ≤ C := map_subtype_le _
  have hZ₂C : Z₂ ≤ C := map_subtype_le _
  have hmem₁ (x : C) : (x : G) ∈ Z₁ ↔ f₁ x = 1 := by
    change x ∈ (f₁.ker.map C.subtype).comap C.subtype ↔ _
    rw [comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  have hmem₂ (x : C) : (x : G) ∈ Z₂ ↔ f₂ x = 1 := by
    change x ∈ (f₂.ker.map C.subtype).comap C.subtype ↔ _
    rw [comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  have hW₁ : W ≤ Z₁ := by
    intro x hx
    apply (hmem₁ ⟨x,cC.kernel_le hx⟩).mpr
    change (cC.coordinates ⟨x,cC.kernel_le hx⟩).toAdd.1 = 0
    rw [(cC.coordinates_eq_one_iff _).mpr hx]
    rfl
  have hW₂ : W ≤ Z₂ := by
    intro x hx
    apply (hmem₂ ⟨x,cC.kernel_le hx⟩).mpr
    change (cC.coordinates ⟨x,cC.kernel_le hx⟩).toAdd.2 = 0
    rw [(cC.coordinates_eq_one_iff _).mpr hx]
    rfl
  let c₁ : BinaryConjugationSection H C Z₁ ((BinarySmall.natural (K := F)).comp π) := {
    section_le := cC.section_le
    kernel_le := hZ₁C
    normalized := cC.normalized
    coordinates := f₁
    onto := by
      intro v
      obtain ⟨c,hcc⟩ := cC.onto (Multiplicative.ofAdd (v.toAdd,0))
      exact ⟨c,congrArg (fun z => Multiplicative.ofAdd z.toAdd.1) hcc⟩
    kernel_eq := by ext x; exact (hmem₁ x).symm
    equivariant g c := congrArg Prod.fst (cC.equivariant g c) }
  let c₂ : BinaryConjugationSection H C Z₂ ((BinarySmall.natural (K := F)).comp π) := {
    section_le := cC.section_le
    kernel_le := hZ₂C
    normalized := cC.normalized
    coordinates := f₂
    onto := by
      intro v
      obtain ⟨c,hcc⟩ := cC.onto (Multiplicative.ofAdd (0,v.toAdd))
      exact ⟨c,congrArg (fun z => Multiplicative.ofAdd z.toAdd.2) hcc⟩
    kernel_eq := by ext x; exact (hmem₂ x).symm
    equivariant g c := congrArg Prod.snd (cC.equivariant g c) }
  let : (Z₁.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    (hQH.trans c₁.kernel_normalized)
  let : (Z₂.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    (hQH.trans c₂.kernel_normalized)
  have he₁ := (BinaryConjugationSection.natural_central_extension_elementary H Q C Z₁
    hCQ hZ₁C c₁.kernel_normalized π hπ hk c₁ cQ a ha0 ha1 (hc.trans hW₁)).2
  have he₂ := (BinaryConjugationSection.natural_central_extension_elementary H Q C Z₂
    hCQ hZ₂C c₂.kernel_normalized π hπ hk c₂ cQ a ha0 ha1 (hc.trans hW₂)).2
  have hZ : Z₁ ⊓ Z₂ ≤ W := by
    intro x hx
    have hxC := hZ₁C hx.1
    apply (cC.coordinates_eq_one_iff ⟨x,hxC⟩).mp
    apply Multiplicative.toAdd.injective
    exact Prod.ext ((hmem₁ ⟨x,hxC⟩).mp hx.1) ((hmem₂ ⟨x,hxC⟩).mp hx.2)
  have hs (q : Q ⧸ W.subgroupOf Q) : q^2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf Q) q
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply hZ
    constructor
    · have hh := he₁.exponent_dvd_p
      have hs := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hh)
        (QuotientGroup.mk' (Z₁.subgroupOf Q) x)
      rw [←map_pow] at hs
      exact (QuotientGroup.eq_one_iff (N := Z₁.subgroupOf Q) (x^2)).mp hs
    · have hh := he₂.exponent_dvd_p
      have hs := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hh)
        (QuotientGroup.mk' (Z₂.subgroupOf Q) x)
      rw [←map_pow] at hs
      exact (QuotientGroup.eq_one_iff (N := Z₂.subgroupOf Q) (x^2)).mp hs
  exact {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hs z)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
/-- Reindex the actual small constituents along a second covering actor, then
apply the two natural projections to the central extension. -/
theorem natural_pair_extension_elementary_of_small_factors
    {K : Type*} [Field K] [Finite K] [CharP K 2] [Finite V]
    (H Q C W : Subgroup G) (hCQ : C ≤ Q) (hQH : Q ≤ H)
    [(W.subgroupOf Q).Normal]
    (π : H →* SL(2,F)) (hπ : Function.Surjective π) (hk : π.ker = Q.subgroupOf H)
    (π₀ : H →* SL(2,K)) (hπ₀ : Function.Surjective π₀) (hk₀ : π₀.ker = Q.subgroupOf H)
    (ρ : Representation (ZMod 2) SL(2,K) V)
    (cE : BinaryConjugationSection H C W (ρ.comp π₀))
    (cQ : BinaryConjugationSection H Q C ((BinarySmall.natural (K := F)).comp π))
    (U : Subrepresentation ρ) [U.toRepresentation.IsIrreducible]
    [U.quotientRepresentation.IsIrreducible]
    {m : ℕ} (hm : Odd m) (hm2 : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (hu : Nat.card U.toSubmodule = Nat.card F ^ (2 : ℕ))
    (hq : Nat.card (V ⧸ U.toSubmodule) = Nat.card F ^ (2 : ℕ))
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hc : ⁅Q,C⁆ ≤ W) :
    IsElementaryAbelian 2 (Q ⧸ W.subgroupOf Q) := by
  let δ : SL(2,F) →* SL(2,K) := π.liftOfSurjective hπ ⟨π₀,by rw [hk,hk₀]⟩
  have hδ (h : H) : δ (π h) = π₀ h := π.liftOfRightInverse_comp_apply _ _ _ h
  have hδs : Function.Surjective δ := by
    intro g
    obtain ⟨h,rfl⟩ := hπ₀ g
    exact ⟨π h,hδ h⟩
  let σ := ρ.comp δ
  let U' : Subrepresentation σ := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule g := U.apply_mem_toSubmodule (δ g) }
  let : U'.toRepresentation.IsIrreducible :=
    (irreducible_comp_surjective_iff δ hδs U.toRepresentation).mpr inferInstance
  let : U'.quotientRepresentation.IsIrreducible :=
    (irreducible_comp_surjective_iff δ hδs U.quotientRepresentation).mpr inferInstance
  obtain ⟨hnU,hnQ,_⟩ := natural_factors_and_cubic_fixed_of_card σ U' hm hm2 hcard hu hq
  obtain ⟨d⟩ := pair_equiv_of_natural_factors σ U' hnU hnQ
  let cE' : BinaryConjugationSection H C W (σ.comp π) := {
    section_le := cE.section_le
    kernel_le := cE.kernel_le
    normalized := cE.normalized
    coordinates := cE.coordinates
    onto := cE.onto
    kernel_eq := cE.kernel_eq
    equivariant h c := by
      rw [cE.equivariant]
      change ρ (π₀ h) _ = ρ (δ (π h)) _
      rw [hδ] }
  exact natural_pair_central_extension_elementary H Q C W hCQ hQH π hπ hk
    (cE'.relabel π d) cQ a ha0 ha1 hc

end Representation.SL2
