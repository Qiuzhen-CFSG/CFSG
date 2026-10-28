module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ComponentOrbitRecognition
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallDisplacementDegree
public import Theory.Representation.SL2NaturalOffenders.MarkedAlternatives
public import Theory.Representation.OrthogonalFourPlusMatrix.SymplecticNormalizerBounds
public import Theory.Representation.OrthogonalFourPlusMatrix.GaloisComparison
public import Theory.GroupTheory.PResidual.Quotient
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.MovedModule


/-!
# Excluding irreducible component orbits on the original large flag

The actual natural orthogonal component orbit has coefficient field F₄ under
both G.11.1(3) clauses. A small nonzero displacement bounds the field degree
in the low-rank clause. In the fixed-line clause, the coefficient image of
the elementary actor has order at most two, and its fixed field injects into
the original binary fixed line.

The preserved nondegenerate form makes conjugation on the determinant pair
faithful. Its automorphism-group order forces a two-group quotient, and
perfectness identifies the pair with the literal two-residual. Transport
through the original action-kernel quotient supplies the exact marked
Ω₄⁺(4) action consumed by the completed 14.4.9 source contradiction.

Consequently every component constituent containing the marked point is
totally isotropic. The final low-rank consumer removes the whole-orbit
remainder and retains only the exchanged natural symmetric constituents.
Proper-constituent multiplicities and exchanged recognition remain required
for catalogue exhaustiveness; no such conclusion is assumed here.

The fixed-field count adapts `MarkedSemilinearPlane.card_le_four_of_fixed_line`.
Source: Aschbacher--Smith G.11.7--8 and 14.4.2(3), 14.4.9,
printed pp.367--368,1006--1007,1009--1010; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.OrthogonalOrbit
open ChapterG.Section09 ChapterG.Section09.TwoComponents
attribute [local instance 2000] instAlgebraZModGaloisField
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {X N : Subgroup D}
  [IsElementaryAbelian 2 X]

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
private theorem matrix_coordinates {n : ℕ}
    (hq : Quasiequivalent (ρ.comp N.subtype) (fourOrthogonal n)) :
    ∃ e : N ≃* PairSL (F := GaloisField 2 n),
      ∃ f : W ≃ₗ[ZMod 2] Mat (F := GaloisField 2 n),
      ∀ (l : N) w, f (ρ l w) = representation (e l) (f w) := by
  obtain ⟨e,f,hf⟩ := hq
  refine ⟨e.trans elementaryEquiv.symm,f.trans (coordinates.restrictScalars (ZMod 2)),?_⟩
  intro l w
  change coordinates (f (ρ l w)) =
    representation (elementaryEquiv.symm (e l)) (coordinates (f w))
  have hl := hf l w
  change f (ρ l w) = fourOrthogonal n (e l) (f w) at hl
  rw [hl]
  change coordinates ((e l).val.val (f w)) = _
  generalize hb : e l = b
  obtain ⟨g,rfl⟩ := elementaryEquiv.surjective b
  rw [MulEquiv.symm_apply_apply]
  exact toOrthogonal_coordinates g (f w)

private theorem field_card_of_fixed_line
    {k : Type*} [Field k] [Finite k] [Algebra (ZMod 2) k]
    (τ : Representation (ZMod 2) D (Mat (F := k)))
    (φ : D →* (k ≃+* k))
    (hφ : ∀ a c w, τ a (c • w) = φ a c • τ a w)
    (v : Mat (F := k)) (hv : v ≠ 0)
    (hfix : fixedSpace τ X = Submodule.span (ZMod 2) {v}) : Nat.card k ≤ 4 := by
  classical
  let ψ := φ.comp X.subtype
  let C := ψ.range
  let : Finite C := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  let := Fintype.ofFinite C
  let : FaithfulSMul C k := ⟨fun h => Subtype.ext (RingEquiv.ext h)⟩
  let K := FixedPoints.subfield C k
  have hc : Nat.card C ≤ 2 := SL2NaturalOffenders.fieldAction_range_card_le_two X inferInstance ψ
  have hdegree : finrank K k = Nat.card C := by
    simpa only [K,Nat.card_eq_fintype_card] using FixedPoints.finrank_eq_card C k
  have hvfix : v ∈ fixedSpace τ X := hfix ▸ Submodule.mem_span_singleton_self v
  let f : K → fixedSpace τ X := fun c => ⟨(c : k) • v,by
    intro a
    change τ (a : D) ((c : k) • v) = (c : k) • v
    rw [hφ,show τ (a : D) v = v from hvfix a]
    change ψ a (c : k) • v = (c : k) • v
    rw [show ψ a (c : k) = (c : k) from c.property ⟨ψ a,⟨a,rfl⟩⟩]⟩
  have hfi : Function.Injective f := by
    intro a b he
    exact Subtype.ext (smul_left_injective k hv (congrArg Subtype.val he))
  have hk := Nat.card_le_card_of_injective f hfi
  rw [hfix,Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Submodule.span (ZMod 2) {v}),finrank_span_singleton hv,Nat.card_zmod,pow_one] at hk
  calc
    Nat.card k = Nat.card K ^ Nat.card C := by
      rw [Module.natCard_eq_pow_finrank (K := K),hdegree]
    _ ≤ 2 ^ Nat.card C := Nat.pow_le_pow_left hk _
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hc
    _ = 4 := by norm_num

/-- Both marked fixed-point clauses force the natural orthogonal coefficient field to be F₄. -/
theorem field_degree_eq_two [N.Normal] {n : ℕ} (hn : 1 < n)
    (hq : Quasiequivalent (ρ.comp N.subtype) (fourOrthogonal n))
    (v : W) (hv : v ≠ 0)
    (hfix : fixedSpace ρ X = Submodule.span (ZMod 2) {v} ∨
      ChapterG.Section11.LowRankWitness ρ v X) : n = 2 := by
  obtain ⟨e,f,hf⟩ := matrix_coordinates hq
  rcases hfix with hfix | hw
  · let τ : Representation (ZMod 2) D (Mat (F := GaloisField 2 n)) :=
      f.conjRingEquiv.toMonoidHom.comp ρ
    have hτ (a : D) (w : W) : τ a (f w) = f (ρ a w) := by
      change f (ρ a (f.symm (f w))) = _
      rw [f.symm_apply_apply]
    have hcoord (a : N) (w : Mat (F := GaloisField 2 n)) :
        τ a w = matrixAction (e a) w := by
      obtain ⟨w,rfl⟩ := f.surjective w
      exact (hτ a w).trans (hf a w)
    obtain ⟨φ,hφ⟩ := normal_ambient_semilinear N e τ hcoord
    have hfixed : fixedSpace τ X = Submodule.span (ZMod 2) {f v} := by
      have he : (fixedSpace ρ X).map f.toLinearMap = fixedSpace τ X := by
        ext w
        obtain ⟨w,rfl⟩ := f.surjective w
        rw [Submodule.mem_map_equiv,f.symm_apply_apply]
        constructor
        · intro hw x
          change τ x (f w) = f w
          rw [hτ]
          exact congrArg f (hw x)
        · intro hw x
          apply f.injective
          exact (hτ x w).symm.trans (hw x)
      rw [←he,hfix,Submodule.map_span,Set.image_singleton]
      rfl
    have hc := field_card_of_fixed_line τ φ hφ (f v)
      (fun hz => hv (f.map_eq_zero_iff.mp hz)) hfixed
    rw [GaloisField.card 2 n (by omega)] at hc
    have hpow : 2^n ≤ 2^2 := hc
    have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
    omega
  · obtain ⟨a,_,_,hp,hr,_⟩ := hw.exists_involution hv
    have hh := LowRankDegree.field_degree_eq_two_of_small_equivariant ρ N e f hf
      (by rw [GaloisField.finrank 2 (by omega : n ≠ 0)]; omega) a hp hr
    rwa [GaloisField.finrank 2 (by omega : n ≠ 0)] at hh
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.OrthogonalOrbit

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.OrthogonalOrbit
open Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
open Theory.GroupTheory.WreathTwoElementaryRank
open Binary
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) W] in
/-- The normal determinant pair is the literal two-residual of a faithful
ambient action preserving a nondegenerate binary form. -/
theorem residual_eq_of_coordinates
    (ρ : Representation (ZMod 2) D W) (hρ : Function.Injective ρ)
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.Nondegenerate)
    (hp : ∀ a u v, B (ρ a u) (ρ a v) = B u v)
    (N : Subgroup D) [N.Normal]
    (e : N ≃* Binary.G) (f : W ≃ₗ[ZMod 2] Binary.V)
    (hf : ∀ (a : N) w, f (ρ a w) = Binary.action (e a) (f w)) :
    pResidual 2 D = N := by
  let B' := LinearMap.BilinForm.congr f B
  have hB' : B'.Nondegenerate := hB.congr f
  have hp' (g : Binary.G) (u v : Binary.V) :
      B' (Binary.action g u) (Binary.action g v) = B' u v := by
    obtain ⟨a,rfl⟩ := e.surjective g
    obtain ⟨u,rfl⟩ := f.surjective u
    obtain ⟨v,rfl⟩ := f.surjective v
    rw [← hf,← hf]
    simpa only [B',LinearMap.BilinForm.congr_apply,f.symm_apply_apply] using hp a u v
  let γ : D →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
    { toFun a := f.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)).trans f)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        change f (ρ 1 (f.symm v)) = v
        rw [map_one,Module.End.one_apply,f.apply_symm_apply]
      map_mul' := by
        intro a b
        apply LinearEquiv.ext
        intro v
        change f (ρ (a*b) (f.symm v)) = f (ρ a (f.symm (f (ρ b (f.symm v)))))
        rw [f.symm_apply_apply,map_mul,Module.End.mul_apply] }
  have hγ (a : D) (w : W) : γ a (f w) = f (ρ a w) := by
    change f (ρ a (f.symm (f w))) = _
    rw [f.symm_apply_apply]
  have hγi : Function.Injective γ := by
    intro a b he
    apply hρ
    ext w
    apply f.injective
    exact (hγ a w).symm.trans ((LinearEquiv.congr_fun he (f w)).trans (hγ b w))
  have hres (a : N) : γ a = Binary.linearAction (e a) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨w,rfl⟩ := f.surjective w
    exact (hγ a w).trans (hf a w)
  have himage : N.map γ = Binary.linearAction.range := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨e ⟨a,ha⟩,(hres ⟨a,ha⟩).symm⟩
    · rintro ⟨a,rfl⟩
      obtain ⟨a,rfl⟩ := e.surjective a
      exact ⟨a,a.property,hres a⟩
  have hn (a : D) : γ a ∈ Binary.symplecticNormalizer B' := by
    constructor
    · rw [← himage]
      exact N.le_normalizer_map γ
        (mem_map_of_mem _ (show a ∈ normalizer (N : Set D) from
          le_normalizer_of_normal (mem_top a)))
    · intro u v
      obtain ⟨u,rfl⟩ := f.surjective u
      obtain ⟨v,rfl⟩ := f.surjective v
      rw [hγ,hγ]
      simpa only [B',LinearMap.BilinForm.congr_apply,f.symm_apply_apply] using hp a u v
  let j := γ.codRestrict (Binary.symplecticNormalizer B') hn
  have hj : Function.Injective j := fun _ _ he => hγi (congrArg Subtype.val he)
  let a := (Binary.symplecticConjugation B').comp j
  have ha : Function.Injective a := (Binary.symplecticConjugation_injective B' hB' hp').comp hj
  have hcardAut : Nat.card (MulAut Binary.G) = 28800 := by
    let e := (MulAut.congr Binary.alternatingPairEquiv).trans wreathEquiv.symm
    rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card]
    norm_num [Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Sym,Nat.card_perm,Nat.card_fin,C2,Nat.card_eq_fintype_card,
      Fintype.card_perm,Nat.factorial]
  have hdiv : Nat.card D ∣ 28800 := by
    rw [←hcardAut]
    exact card_dvd_of_injective a ha
  have hNcard : Nat.card N = 3600 := by
    rw [Nat.card_congr (e.trans Binary.alternatingPairEquiv).toEquiv,Nat.card_prod]
    change Nat.card (alternatingGroup (Fin 5)) * Nat.card (alternatingGroup (Fin 5)) = 3600
    rw [nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have hquot : IsPGroup 2 (D ⧸ N) := by
    apply (IsPGroup.iff_card).mpr
    have hi : N.index ∣ 2^3 := by
      have hh := N.card_mul_index
      rw [hNcard] at hh
      rw [←hh] at hdiv
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3600)).mp hdiv
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hi
    exact ⟨k,by rw [←N.index_eq_card,he]⟩
  apply le_antisymm ((pResidual_le_iff_isPGroup_quotient 2 N).mpr hquot)
  let : Group.IsPerfect Alt := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect Pair := ⟨by
    rw [_root_.commutator_def, ← top_prod_top, commutator_prod_prod]
    change (_root_.commutator Alt).prod (_root_.commutator Alt) = _
    simp only [Group.IsPerfect.commutator_eq_top]⟩
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := (e.trans Binary.alternatingPairEquiv).symm.toMonoidHom)
    (e.trans Binary.alternatingPairEquiv).symm.surjective
  apply le_pResidual_of_isPPerfect
  intro K hK hq
  let := hK
  let : Group.IsNilpotent (N ⧸ K) := hq.isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient (⊤ : Subgroup N) K)
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.OrthogonalOrbit
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open ClassicalOrthogonal.FourPlusMatrix
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open LargerDimension LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components CoreGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
attribute [local instance 2000] instAlgebraZModGaloisField

/-- On the original flag an irreducible component orbit has the actual
SL₂(4) × SL₂(4) determinant action. Both G.11 fixed-point clauses are used. -/
theorem source_large_irreducible_orbit_binary (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) :
    ∃ e : componentOrbit C ⊤ ≃* Binary.G,
      ∃ f : Additive F.Uhat ≃ₗ[ZMod 2] Binary.V,
        ∀ (a : componentOrbit C ⊤) w,
          f (F.terminalRepresentation a w) = Binary.action (e a) (f w) := by
  obtain ⟨n,hn,hmodel⟩ := source_large_irreducible_orbit_natural d earlier hq chosen
    structural alternatives classification F hne hZ hlarge g hgP hgH C hC hm h9
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} ∨ ChapterG.Section11.LowRankWitness
        F.terminalRepresentation v (F.terminalDot (F.X g)) := by
    rcases source_terminal_fixed_point_alternative d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
    · exact .inl hf
    · exact .inr ⟨a,a.property,hr,hv⟩
  let := h9.normal_H
  have hn2 := OrthogonalOrbit.field_degree_eq_two hn hmodel v hyp.point_ne_zero hfix
  subst n
  obtain ⟨e,f,hf⟩ := hmodel
  refine ⟨e.trans Binary.galoisGroupEquiv,f.trans Binary.galoisCoordinates,?_⟩
  intro a w
  change Binary.galoisCoordinates (f (F.terminalRepresentation a w)) = _
  have hh := hf a w
  change f (F.terminalRepresentation a w) = _ at hh
  rw [hh]
  exact Binary.galoisCoordinates_intertwines (e a) (f w)

/-- The component orbit is the literal terminal two-residual, with its
marked Ω₄⁺(4) action transported through the original action-kernel quotient. -/
theorem source_large_irreducible_orbit_marked (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) :
    ∃ κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃*
      ClassicalOrthogonal.OmegaPlus 2 Binary.F,
    ∃ e : Additive F.Uhat ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 2 Binary.F,
      let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) w,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives
          hne hZ)).representation k w) =
          ClassicalOrthogonal.subgroupNatural (ClassicalOrthogonal.OmegaPlus 2 Binary.F) (κ k) (e w) := by
  let := chosen.elementary
  let := F.U_normal
  let := h9.normal_H
  obtain ⟨e,f,hf⟩ := source_large_irreducible_orbit_binary d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm h9
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hres := OrthogonalOrbit.residual_eq_of_coordinates F.terminalRepresentation
    hyp.faithful B hyp.nondegenerate hyp.preserves (componentOrbit C ⊤) e f hf
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let R := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hR : R.map q.toMonoidHom = componentOrbit C ⊤ := by
    dsimp only [R]
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ q.surjective,hres]
  let eR : R ≃* componentOrbit C ⊤ :=
    (q.subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  refine ⟨(eR.trans e).trans elementaryEquiv, f.trans Binary.binaryCoordinates.symm,?_⟩
  dsimp only
  intro k w
  apply Binary.binaryCoordinates.injective
  change Binary.binaryCoordinates (Binary.binaryCoordinates.symm
    (f (F.terminalRepresentation (q k.val) w))) = _
  rw [Binary.binaryCoordinates.apply_symm_apply]
  change f (F.terminalRepresentation (eR k) w) =
    Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w)))
  rw [hf]
  rw [show Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w))) =
      Binary.action (e (eR k)) (Binary.binaryCoordinates (Binary.binaryCoordinates.symm (f w))) from
        toOrthogonal_coordinates (e (eR k)) (Binary.binaryCoordinates.symm (f w))]
  rw [Binary.binaryCoordinates.apply_symm_apply]

/-- No component orbit acts irreducibly on the original large extraspecial
module: its marked orthogonal residual is excluded by the original source geometry. -/
theorem source_no_irreducible_component_orbit (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) : False := by
  obtain ⟨κ,e,he⟩ := source_large_irreducible_orbit_marked d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm h9
  let := chosen.elementary
  exact Orthogonal.source_orthogonal_exclusion d earlier hq chosen structural alternatives
    F hne hZ κ e he

/-- The original marked irreducible constituent cannot be nondegenerate.
Its G.9 component hypotheses and the orthogonal contradiction are discharged. -/
theorem source_no_nondegenerate_component_constituent (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I)
    (hv : v ∈ I) (hnd : (B.restrict I).Nondegenerate) : False := by
  exact source_no_irreducible_component_orbit d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH C hC hm
    (source_large_componentHypothesis_of_nondegenerate d earlier hq chosen structural
      alternatives F hne hZ hlarge g hgP hgH hyp hC hm hI hv hnd)
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open LargerDimension LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every original component constituent containing the marked point is
totally isotropic; the possible whole nondegenerate orbit has been excluded. -/
theorem source_large_point_constituent_isotropic (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I)
    (hv : v ∈ I) : ∀ u ∈ I, ∀ w ∈ I, B u w = 0 := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  rcases hyp.constituent_isotropic_or_top_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv with hiso | ⟨_,hirr⟩
  · exact hiso
  · exact (source_no_irreducible_component_orbit d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH C hC hm
      (hyp.componentHypothesis_of_orbit_irreducible (source_terminal_cover F d chosen)
        hC hm hind hirr)).elim
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The low-rank source reduction has no whole-component-orbit remainder.
The only unrecognized branch consists of two exchanged nondegenerate
natural symmetric constituents, with the original actor and quotient action. -/
theorem source_large_lowRank_exchanged_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
      (IsIrreducible F.terminalRepresentation ∧
        ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
          ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
          ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
            ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
              (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
              v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry
                F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
              (∃ x : F.terminalDot (F.X g), I.map (F.terminalRepresentation x) ≠ I ∧
                IsCompl I (I.map (F.terminalRepresentation x))) ∧
              finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
              (finrank (ZMod 2) (Additive F.Uhat) = 8 ∨
                finrank (ZMod 2) (Additive F.Uhat) = 12) ∧
              (B.restrict I).Nondegenerate ∧
              ∃ n, 5 ≤ n ∧ n ≤ 8 ∧ n ≠ 7 ∧ ChapterG.Section06.HasModelOn
                (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
                  (componentOrbit C ⊤) (F.terminalDot (F.X g) ⊓
                    subspaceStabilizer F.terminalRepresentation I) I hI.invariant inf_le_right)) ⊤ ⊤
                (BinaryPermutation.naturalRepresentation (Fin n))) := by
  rcases source_large_lowRank_reduction d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH B v hyp hfix hw with hc | ⟨hi,_,C,hC,hm,horth,hwhole | hex⟩
  · exact .inl hc
  · exact (source_no_irreducible_component_orbit d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH C hC hm hwhole).elim
  · exact .inr ⟨hi,C,hC,hm,horth,hex⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
