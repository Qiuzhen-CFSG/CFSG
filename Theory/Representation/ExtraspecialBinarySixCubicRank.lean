module
public import Theory.Representation.ExtraspecialBinarySix
public import Theory.Representation.SL3FourNaturalContainment
public import Theory.GroupTheory.PrimeRankCoprimeIndex

/-!
# Cubic rank of an extraspecial binary six-space

An extraspecial subgroup of order 27 acting faithfully in binary degree six
has Schur field of order four. If its center is central in the whole acting
group, every operator is linear over that field. For a group of order 648,
the faithful image in GL₃(4) has index 280, prime to three. Coprime-index
rank transfer and the diagonal cubic subgroup give three-rank at least three.

This avoids any assumption that the extension by SL₂(3) splits.
Source application: Aschbacher–Smith 14.7.15(3), printed p.1047,
refs/quasithin.pdf.
-/

public noncomputable section
open scoped MonoidAlgebra TensorProduct
open Subgroup Representation Theory.GroupTheory
namespace Representation.ExtraspecialBinarySixCubicRank
variable {P V : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private noncomputable def centerScalar (σ : Representation (ZMod 2) P V) :
    center P →* Module.End (ZMod 2)[P] σ.asModule :=
  (IntertwiningMap.equivAlgEnd σ).toMonoidHom.comp
    { toFun := fun z => IntertwiningMap.centralMul σ z z.property
      map_one' := by
        apply IntertwiningMap.toLinearMap_injective
        exact σ.map_one
      map_mul' _ _ := by
        apply IntertwiningMap.toLinearMap_injective
        exact σ.map_mul _ _ }

omit [Finite P] [IsExtraspecial 3 P] [FiniteDimensional (ZMod 2) V] in
private theorem centerScalar_injective (σ : Representation (ZMod 2) P V)
    (hf : Function.Injective σ) : Function.Injective (centerScalar σ) := by
  intro z w he
  apply Subtype.ext
  apply hf
  exact congrArg IntertwiningMap.toLinearMap ((IntertwiningMap.equivAlgEnd σ).injective he)

variable {G : Type*} [Group G] [Finite G]
  (ρ : Representation (ZMod 2) G V) (F : Subgroup G)

/-- A faithful binary six-space with a central extraspecial cubic center
and acting group of order 648 has cubic rank at least three. -/
theorem three_le_primeRank [IsExtraspecial 3 F] (hf : Function.Injective ρ)
    (hF : Nat.card F = 27) (hd : Module.finrank (ZMod 2) V = 6)
    (hZ : (center F).map F.subtype ≤ center G)
    (hcard : Nat.card G = 648) : 3 ≤ primeRank 3 G := by
  let σ : Representation (ZMod 2) F V := ρ.comp F.subtype
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    (hf.comp F.subtype_injective) hF hd
  let E := Module.End (ZMod 2)[F] σ.asModule
  let : Finite σ.asModule := Module.finite_of_finite (ZMod 2)
  let : Module.Finite E σ.asModule := Module.Finite.of_finite
  obtain ⟨hE,hdE⟩ := ExtraspecialBinarySix.schur_card σ (hf.comp F.subtype_injective) hF hd
  let φ : center F →* Eˣ := MonoidHom.toHomUnits (centerScalar σ)
  have hφ : Function.Injective φ := by
    intro a b he
    exact centerScalar_injective σ (hf.comp F.subtype_injective) (congrArg Units.val he)
  have honto : Function.Surjective φ := (hφ.bijective_of_nat_card_le (by
    rw [Nat.card_units,hE,IsExtraspecial.center_order_p 3 F])).2
  have hcomm (g : G) (f : IntertwiningMap σ σ) (v : V) : ρ g (f v) = f (ρ g v) := by
    let e : E := (IntertwiningMap.equivAlgEnd σ) f
    by_cases he : e = 0
    · have hz : f = 0 := (IntertwiningMap.equivAlgEnd σ).injective (by simpa [e] using he)
      simp [hz]
    obtain ⟨z,hz⟩ := honto (Units.mk0 e he)
    have heq : f = IntertwiningMap.centralMul σ z z.property := by
      apply (IntertwiningMap.equivAlgEnd σ).injective
      exact (congrArg Units.val hz).symm
    rw [heq]
    change ρ g (ρ (z.val : G) v) = ρ (z.val : G) (ρ g v)
    simp only [← Module.End.mul_apply,← map_mul]
    have hc := mem_center_iff.mp (hZ ⟨z,z.property,rfl⟩) g
    exact congrArg (fun a : G => ρ a v) hc
  let τ : Representation E G σ.asModule :=
    { toFun := fun g => SchurOperator.linear σ (ρ g) (hcomm g)
      map_one' := by
        apply LinearMap.ext
        intro v
        apply σ.asModuleEquiv.injective
        change ρ 1 (σ.asModuleEquiv v) = σ.asModuleEquiv v
        simp
      map_mul' g h := by
        apply LinearMap.ext
        intro v
        apply σ.asModuleEquiv.injective
        change ρ (g*h) (σ.asModuleEquiv v) = ρ g (ρ h (σ.asModuleEquiv v))
        rw [map_mul,Module.End.mul_apply] }
  have hτ : Function.Injective τ := by
    intro g h he
    apply hf
    ext v
    exact congrArg σ.asModuleEquiv (LinearMap.congr_fun he (σ.asModuleEquiv.symm v))
  let b := Module.finBasisOfFinrankEq E σ.asModule hdE
  let eMat := Matrix.GeneralLinearGroup.toLin' b
  let τM : G →* Matrix.GeneralLinearGroup (Fin 3) E := eMat.symm.toMonoidHom.comp τ.asGroupHom
  have hτM : Function.Injective τM := by
    intro g h he
    apply hτ
    exact congrArg Units.val (eMat.symm.injective he)
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) E) = 181440 := by
    classical
    let : Fintype E := Fintype.ofFinite E
    rw [Matrix.card_GL_field]
    rw [show Fintype.card E = 4 by simpa [Nat.card_eq_fintype_card] using hE]
    norm_num [Fin.prod_univ_succ]
  have hR : Nat.card τM.range = 648 :=
    (Nat.card_congr (MonoidHom.ofInjective hτM).toEquiv).symm.trans hcard
  have hi := τM.range.card_mul_index
  rw [hR,hGL] at hi
  have hindex : τM.range.index = 280 := by omega
  have hr := Subgroup.primeRank_eq_of_not_dvd_index (p := 3) τM.range
    (by rw [hindex]; decide)
  rw [←primeRank_equiv 3 (MonoidHom.ofInjective hτM)] at hr
  rw [hr]
  exact Representation.SL3FourNaturalContainment.three_le_generalLinear_rank hE

end Representation.ExtraspecialBinarySixCubicRank
