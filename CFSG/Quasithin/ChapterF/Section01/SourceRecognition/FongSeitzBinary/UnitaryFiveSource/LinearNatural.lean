module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.LinearFrattini
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.ReflectedRoots
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryLinearActions
public import Theory.Representation.IrreducibleFixedPoints

/-!
# Natural coordinates for the actual linear U₅ section

The source linear Frattini section is irreducible of binary dimension 4n.
The small-module classifier leaves the natural and Hermitian possibilities;
the exceptional degree-three field cannot occur. The crossed unitary root
has order q³, center q and a central Frattini kernel. It would supply at
least q² fixed vectors, whereas the Hermitian module has only q. Thus the
section is natural for the actual SL₂(q²) actor.

The coordinates retain the reflection-pinned actor and every positive
binary degree, including q = 2 and q = 4. LinearApplication supplies the
original profile and literal quotient representatives. Matching these
coordinates with the SU₃ labels remains part of the source construction.
Source: Fong--Seitz I (6A)(c); II (8C), pp.203,208, (8.14), (8.32)--(8.33).
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative MonoidAlgebra
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {X K E : Type*} [Group X] [Field K] [Finite K] [CharP K 2]
  [Field E] [Finite E] [CharP E 2] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) (n : ℕ) [NeZero n]
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (μ₀ : localGroup Q split i ≃* PSL(2,K))
  (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  (hBj : Nat.card (simpleRoot Q split j) = (2^n)^3)
  (hcardV : Nat.card (simpleRemainder Q split i) = (2^n)^8)

include hK hE hfixed hJ hm hij hVi hVj s ν hBj hcardV

/-- The actual SL₂ Frattini section is natural for the same pinned actor,
including the smallest two binary fields. -/
theorem aligned_linear_frattini_natural :
    SL2.BinarySmall.IsNatural (linearFrattiniRepresentation Q split i hVi
      (GTwoSource.alignedPinning Q split i hVi μ₀ s).symm) := by
  let μ := (GTwoSource.alignedPinning Q split i hVi μ₀ s).symm
  let σ := linearFrattiniRepresentation Q split i hVi μ
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)
  obtain ⟨_,hc,hi⟩ := unitary_linear_frattini_irreducible Q split J (NeZero.pos n) hK hE hfixed hJ
    hm i j hij hVi hVj s μ ν hcardV
  let : ρ.IsIrreducible := hi
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff μ.symm.toMonoidHom μ.symm.surjective ρ).mpr hi
  have hd : Module.finrank (ZMod 2)
      (Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))) = 4*n := by
    have hp := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)))
    rw [Nat.card_zmod] at hp
    change Nat.card ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)) = _ at hp
    rw [hc,←pow_mul,Nat.mul_comm n 4] at hp
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hp).symm
  have hnt : ∃ g, σ g ≠ 1 := by
    by_contra! htriv
    let : Nontrivial (Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))) :=
      Subrepresentation.irreducible_module_nontrivial σ
    obtain ⟨v,hv⟩ := exists_ne (0 : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i)))
    have hf : v ∈ OneCohomology.fixed σ := fun g => LinearMap.congr_fun (htriv g) v
    rw [OneCohomology.fixed_eq_bot_of_irreducible_finrank σ (by rw [hd]; have := NeZero.pos n; omega)] at hf
    exact hv hf
  have hK' : Nat.card K = 2^(2*n) := by rw [hK,←pow_mul,Nat.mul_comm n 2]
  rcases ChapterG.Section09.DefiningCharacteristic.binary_small_module_alternatives σ hnt
    (2*n) (by have := NeZero.pos n; omega) hK' (by rw [hd]; omega) with hnat | hherm | htriple
  · exact hnat.2.2
  · obtain ⟨heq,_,hs,hh⟩ := hherm
    have heqn : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] σ.asModule) = n := by omega
    have hh' : SL2.BinarySmall.IsHermitian σ n := by simpa only [heqn] using hh
    have hroot : ((rankOne Q split i).subtype.comp
        (μ.symm.toMonoidHom.comp (Matrix.SpecialLinearGroup.upperUnipotentHom K))).range = simpleRoot Q split i :=
      GTwoSource.alignedSimpleParameter_range Q split i hVi μ₀ s
    let a := GTwoSource.simpleRootFieldEquiv Q split i hVi μ₀
    let : IsElementaryAbelian 2 (Multiplicative K) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Multiplicative.toAdd.injective
        change (2 : ℕ) • x.toAdd = 0
        rw [two_nsmul]
        exact CharTwo.add_self_eq_zero _) }
    have hAi := IsElementaryAbelian.of_surjective (p := 2) a.toMonoidHom a.surjective
    have hA := (GTwoSource.simpleRoot_card Q split i hVi μ₀).trans hK
    have hcomm := unitary_opposite_commutator Q split J (NeZero.pos n) hK hE hfixed hJ
      hm i j hij hVi hVj s μ ν
    have hcentral := linear_frattini_central Q split J (NeZero.pos n) hE hfixed hJ
      hm i j hij hVi hVj s ν hAi hA hcomm
    have hb := hermitian_frattini_root_bound Q split hm i j hij hVi hVj μ hroot hcentral hh'
    have hDc : Nat.card (rootAt Q split j (Q.simple i)) = (2^n)^3 := by
      simp only [rootAt,card_rightConjugate,hBj]
    have hz := simpleRoot_derived_center_card Q split j hVj J (NeZero.pos n) hE hfixed hJ ν
    have hZ : Nat.card (center (simpleRoot Q split j)) = 2^n := by
      have hh := hz.2
      rw [hz.1,card_map_of_injective (simpleRoot Q split j).subtype_injective] at hh
      exact hh
    let eD := reflectedUnitaryChart Q split i j s (MulEquiv.refl (simpleRoot Q split j))
    have hZD : Nat.card (center (rootAt Q split j (Q.simple i))) = 2^n :=
      (Nat.card_congr (centerCongr eD).toEquiv).symm.trans hZ
    rw [hDc,hZD] at hb
    have hq : 1 < 2^n := Nat.one_lt_two_pow (NeZero.ne n)
    have hlt : (2^n)^2 < (2^n)^3 := Nat.pow_lt_pow_right hq (by decide)
    nlinarith
  · omega

/-- Construct an actual natural-coordinate equivalence, preserving every
matrix in the source reflection-pinned SL₂ actor. -/
theorem aligned_linear_frattini_coordinates :
    let : Algebra (ZMod 2) K := ZMod.algebra K 2
    ∃ c : Additive ((simpleRemainder Q split i) ⧸ frattini (simpleRemainder Q split i))
        ≃ₗ[ZMod 2] (Fin 2 → K),
      ∀ a v, c (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split i hVi)
        (GTwoSource.alignedPinning Q split i hVi μ₀ s a) v) = Matrix.mulVec a.val (c v) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨c⟩ := aligned_linear_frattini_natural Q split J n hK hE hfixed hJ hm i j hij hVi hVj s μ₀ ν hBj hcardV
  refine ⟨c.toLinearEquiv,fun a v => ?_⟩
  exact LinearMap.congr_fun (c.isIntertwining' a) v

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
