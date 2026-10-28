module
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree
public import Theory.Representation.SchurLinearOperator
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The scalar field of a faithful extraspecial binary six-space

The extraspecial group of order27 acts irreducibly in binary degree6.
Its absolutely irreducible degree is3, so its actual Schur field has order4.
Consequently its ambient faithful centralizer has order at most3 and lies
in the extraspecial subgroup. These are the field and centralizer inputs
for the finite-linear endgame of Aschbacher–Smith D.2.29, pp.191–192.
-/

@[expose] public section
open scoped MonoidAlgebra TensorProduct
open Subgroup Representation
namespace Representation.ExtraspecialBinarySix
variable {P V : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual Schur field has four elements, and the scalar degree is three. -/
theorem schur_card (σ : Representation (ZMod 2) P V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hP : Nat.card P = 27)
    (hd : Module.finrank (ZMod 2) V = 6) :
    Nat.card (Module.End (ZMod 2)[P] σ.asModule) = 4 ∧
      Module.finrank (Module.End (ZMod 2)[P] σ.asModule) σ.asModule = 3 := by
  let E := Module.End (ZMod 2)[P] σ.asModule
  let L := AlgebraicClosure E
  let : Finite σ.asModule := Module.finite_of_finite (ZMod 2)
  let : Module.Finite E σ.asModule := Module.Finite.of_finite
  let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let τ := extendScalars L σ.endFieldRep
  let : IsIrreducible τ := IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep L
  have hσ : Function.Injective σ.endFieldRep := by
    intro x y he
    apply hf
    ext v
    exact congrArg σ.asModuleEquiv (LinearMap.congr_fun he (σ.asModuleEquiv.symm v))
  have hτ : Function.Injective τ := (extendScalars_faithful_iff L σ.endFieldRep).mp hσ
  have hchar : ringChar L = 2 :=
    (Algebra.ringChar_eq E L).symm.trans
      ((Algebra.ringChar_eq (ZMod 2) E).symm.trans (ZMod.ringChar_zmod_n 2))
  have hdeg : Module.finrank L (L ⊗[E] σ.asModule) = 3 := by
    simpa only [pow_one] using
      finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
        (q := 3) (n := 1) τ hτ hP (by rw [hchar,hP]; decide)
  rw [Module.finrank_baseChange] at hdeg
  have ht := Module.finrank_mul_finrank (ZMod 2) E σ.asModule
  rw [hdeg,σ.asModuleEquiv.finrank_eq,hd] at ht
  have hE : Module.finrank (ZMod 2) E = 2 := by omega
  refine ⟨?_,hdeg⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hE]
  norm_num

variable {G : Type*} [Group G] [Finite G]
  (ρ : Representation (ZMod 2) G V) (F : Subgroup G)

private def centralizerEnd (g : centralizer (F : Set G)) :
    IntertwiningMap (ρ.comp F.subtype) (ρ.comp F.subtype) where
  toLinearMap := ρ g
  isIntertwining' f := by
    change ρ (g : G) * ρ (f : G) = ρ (f : G) * ρ (g : G)
    rw [← map_mul,← map_mul]
    exact congrArg ρ ((mem_centralizer_iff.mp g.property) f f.property).symm

private noncomputable def centralizerHom : centralizer (F : Set G) →*
    Module.End (ZMod 2)[F] (Representation.asModule (ρ.comp F.subtype)) :=
  (IntertwiningMap.equivAlgEnd (ρ.comp F.subtype)).toMonoidHom.comp
    { toFun := centralizerEnd ρ F
      map_one' := by
        apply IntertwiningMap.toLinearMap_injective
        exact ρ.map_one
      map_mul' g h := by
        apply IntertwiningMap.toLinearMap_injective
        exact ρ.map_mul g h }

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem centralizerHom_injective (hf : Function.Injective ρ) :
    Function.Injective (centralizerHom ρ F) := by
  intro g h he
  apply Subtype.ext
  apply hf
  exact congrArg IntertwiningMap.toLinearMap
    ((IntertwiningMap.equivAlgEnd (ρ.comp F.subtype)).injective he)

/-- Every faithful binary six-dimensional extraspecial27 subgroup contains
its full ambient centralizer. No normality or ambient source classification
is assumed. -/
theorem centralizer_le [IsExtraspecial 3 F] (hf : Function.Injective ρ)
    (hF : Nat.card F = 27) (hd : Module.finrank (ZMod 2) V = 6) :
    centralizer (F : Set G) ≤ F := by
  let σ : Representation (ZMod 2) F V := ρ.comp F.subtype
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    (hf.comp F.subtype_injective) hF hd
  let E := Module.End (ZMod 2)[F] σ.asModule
  have hE : Nat.card E = 4 := (schur_card σ (hf.comp F.subtype_injective) hF hd).1
  let φ : centralizer (F : Set G) →* Eˣ := MonoidHom.toHomUnits (centralizerHom ρ F)
  have hφ : Function.Injective φ := by
    intro a b he
    exact centralizerHom_injective ρ F hf (congrArg Units.val he)
  have hC : Nat.card (centralizer (F : Set G)) ≤ 3 := by
    have hh := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_units,hE] at hh
  let Z := (center F).map F.subtype
  have hZC : Z ≤ centralizer (F : Set G) := by
    rintro z ⟨c,hc,rfl⟩
    rw [mem_centralizer_iff]
    intro f hf
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨f,hf⟩)
  have hZ : Nat.card Z = 3 := by
    rw [show Nat.card Z = Nat.card (center F) from
      (Nat.card_congr ((center F).equivMapOfInjective F.subtype F.subtype_injective).toEquiv).symm]
    exact IsExtraspecial.center_order_p 3 F
  have he : Z = centralizer (F : Set G) := eq_of_le_of_card_ge hZC (by omega)
  rw [← he]
  rintro _ ⟨z,_,rfl⟩
  exact z.property


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

private theorem determinant_kernel_card {E : Type*} [Field E] [Finite E]
    (hc : Nat.card E = 4) :
    Nat.card (Matrix.GeneralLinearGroup.det.ker :
      Subgroup (Matrix.GeneralLinearGroup (Fin 3) E)) = 60480 := by
  classical
  let : Fintype E := Fintype.ofFinite E
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) E) = 181440 := by
    rw [Matrix.card_GL_field]
    rw [show Fintype.card E = 4 by simpa [Nat.card_eq_fintype_card] using hc]
    norm_num [Fin.prod_univ_succ]
  let det : Matrix.GeneralLinearGroup (Fin 3) E →* Eˣ := Matrix.GeneralLinearGroup.det
  have hrange : det.range = ⊤ := MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective
  have hindex : det.ker.index = 3 := by
    rw [Subgroup.index_ker,hrange,Subgroup.card_top,Nat.card_units,hc]
  have hmul : Nat.card det.ker * 3 = 181440 := by
    simpa only [hindex,hGL] using det.ker.card_mul_index
  change Nat.card det.ker = 60480
  omega

/-- An involution-generated binary six-space centralizing the cubic center
of a faithful extraspecial27 subgroup has order dividing SL₃(4). The original
action supplies the scalar structure; no ambient model is assumed. -/
theorem card_dvd_specialLinear [IsExtraspecial 3 F] (hf : Function.Injective ρ)
    (hF : Nat.card F = 27) (hd : Module.finrank (ZMod 2) V = 6)
    (hZ : (center F).map F.subtype ≤ center G)
    (hgen : closure {t : G | t ≠ 1 ∧ t ^ 2 = 1} = ⊤) : Nat.card G ∣ 60480 := by
  let σ : Representation (ZMod 2) F V := ρ.comp F.subtype
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    (hf.comp F.subtype_injective) hF hd
  let E := Module.End (ZMod 2)[F] σ.asModule
  let : Finite σ.asModule := Module.finite_of_finite (ZMod 2)
  let : Module.Finite E σ.asModule := Module.Finite.of_finite
  obtain ⟨hE,hdE⟩ := schur_card σ (hf.comp F.subtype_injective) hF hd
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
  let det : G →* Eˣ := Matrix.GeneralLinearGroup.det.comp τM
  have hdet : ∀ g, det g = 1 := by
    have hle : closure {t : G | t ≠ 1 ∧ t ^ 2 = 1} ≤ det.ker := by
      apply (Subgroup.closure_le _).mpr
      intro t ht
      change det t = 1
      apply orderOf_eq_one_iff.mp
      apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
      · exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow,ht.2,map_one])
      · have hh := orderOf_dvd_natCard (det t)
        have hu : Nat.card Eˣ = 3 := by
          rw [Nat.card_units]
          rw [show Nat.card E = 4 from hE]
        rw [hu] at hh
        exact hh
    rw [hgen] at hle
    exact fun g => hle (mem_top g)
  let τK : G →* (Matrix.GeneralLinearGroup.det.ker : Subgroup (Matrix.GeneralLinearGroup (Fin 3) E)) :=
    τM.codRestrict _ hdet
  have hτK : Function.Injective τK := by
    intro g h he
    exact hτM (congrArg Subtype.val he)
  exact (Subgroup.card_dvd_of_injective τK hτK).trans
    (determinant_kernel_card hE).dvd

end Representation.ExtraspecialBinarySix
