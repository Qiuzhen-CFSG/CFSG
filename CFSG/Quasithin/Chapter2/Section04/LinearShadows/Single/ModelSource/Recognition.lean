module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModelSource.Geometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SplitRecognition
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.DerivedModel
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.ResidualModel
/-!
# Original 2.4.8(4): recognition of the single natural block

The source geometry constructs the splitting and forces the center to
have order one or q. The marked natural-cover comparison and Gaschütz
splitting identify L with the actual derived maximal parabolic of PSL₃(q)
or Sp₄(q). The symplectic branch retains the original conjugate torus and
its regular action on the nonidentity center. No recognition callback or
module-identification premise is added to the original source hypotheses.
Source: Aschbacher–Smith, Lemma 2.4.8(4), printed pp.529–530.
-/
public section
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Subgroup Representation
open ChapterC.Section05.ConjugateSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Original 2.4.8(4): the actual block is the derived maximal parabolic of
PSL₃(q) or Sp₄(q), with the specified center and original conjugate torus. -/
theorem lemma_2_4_8_4
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let L := d.block.map d.H.subtype
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let Z := (center L).map L.subtype
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2^n ∧
      ∃ D : Subgroup G, D ≤ M ⊓ L ∧ IsCyclic D ∧ Nat.card D = 2^n-1 ∧
      ∃ x ∈ T, x ∉ S ∧
      let E := D.map (MulAut.conj x⁻¹).toMonoidHom
      E ≤ normalizer (L : Set G) ∧
      ((center L = ⊥ ∧ IsCoatom (Matrix.PSL3.LinearThree.pointParabolic F) ∧
        Nonempty (L ≃* solvableResidual (Matrix.PSL3.LinearThree.pointParabolic F)) ∧
        Nonempty (L ≃* commutator (Matrix.PSL3.LinearThree.pointParabolic F))) ∨
       (Nat.card (center L) = 2^n ∧ Nonempty (center L ≃* Multiplicative F) ∧
        IsCoatom (Theory.SpecificGroups.SymplecticFour.planeParabolic (F:=F)) ∧
        Nonempty (L ≃* solvableResidual (Theory.SpecificGroups.SymplecticFour.planeParabolic (F:=F))) ∧
        Nonempty (L ≃* commutator (Theory.SpecificGroups.SymplecticFour.planeParabolic (F:=F))) ∧
        E ≤ normalizer (Z : Set G) ∧
        ∀ z : Z, z ≠ 1 → ∀ w : Z, w ≠ 1 →
          ∃! a : E, (a:G)*(z:G)*(a:G)⁻¹ = (w:G))) := by
  let L := d.block.map d.H.subtype
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hcore := source_block_core_eq_module d hG T hST hsingle
  let := hK.2.1.elementary
  let := hK.2.1.module_elementary
  obtain ⟨hsplit,D,hDM,hcyc,hDcard,x,hxT,hxS,hEL,hZ⟩ :=
    source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
  obtain ⟨F,_,_,hF,_hPSL,r,⟨m⟩,hm⟩ := hK.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hK.1
  refine ⟨F,inferInstance,inferInstance,inferInstance,hF,D,hDM,hcyc,hDcard,x,hxT,hxS,hEL,?_⟩
  rcases hZ with hz | ⟨hc,hEN,hregular⟩
  · obtain ⟨e⟩ := ChapterC.split_natural_model hK.2.1 m hm hcore hsplit hz
    exact Or.inl ⟨hz,Matrix.PSL3.LinearThree.pointParabolic_isCoatom F,
      ⟨e.trans (Matrix.PSL3.LinearThree.pointParabolicResidualEquivAffine F h4).symm⟩,
      ⟨e.trans (Matrix.PSL3.LinearThree.pointParabolicDerivedEquivAffine F h4).symm⟩⟩
  · obtain ⟨e⟩ := ChapterC.split_orthogonal_model hK.2.1 m hm hK.1 hF hcore hsplit
      (hK.center_le_module hcore) hc
    have heZ := ChapterC.center_equiv_additive_field hK hcore (hc.trans hF.symm)
    exact Or.inr ⟨hc,heZ,
      (Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalCover.maximal_parabolic_residual_model hF hK.1).1,
      ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalCover.residualEquiv hF hK.1).symm⟩,
      ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalCover.derivedEquiv hF hK.1).symm⟩,
      hEN,hregular⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
