module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineRecognition
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Eliminating the full five-point coefficient image

When the literal coefficient image is S₅, its even subgroup identifies the
original component centralizer with A₅. Perfectness forces its actual linear
coefficient matrices to have determinant one. Their faithful embedding fills
SL₂(4), so the original component and centralizer act on the whole module as
the determinant tensor. Inverse transpose on the component gives the required
right-inverse convention, and coefficient transport preserves the binary
action over the concrete field.

These coordinates identify the original two-residual. Transport through the
literal terminal quotient then applies the existing orthogonal exclusion to
the original flag. Only the transposition-centralizer coefficient case and
unmarked exchanged constituents remain; their recognition and the guarded
earlier-source assembly are still required. The independent MixedSizeInput
premise is retained exactly.
Source: Aschbacher--Smith G.11.8 and 14.4.2, printed pp.368--369,1006--1007;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Matrix
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {H : Subgroup D} (a : Coordinates ρ H)
local instance : Algebra (ZMod 2) Field := ZMod.algebra _ 2

private theorem centralizer_special
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (htop : a.coefficientFive.range = ⊤) :
    ∃ e : centralizer (H : Set D) ≃* SL(2,Field),
      ∀ c, (e c).val = (a.centralizerLinear c).val := by
  let e₀ := (a.centralizerFiveEquiv B hnd hB).trans
    (MulEquiv.subgroupCongr (show a.coefficientFive.range ⊓ alternatingGroup (Fin 5) =
      alternatingGroup (Fin 5) by rw [htop,top_inf_eq]))
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (centralizer (H : Set D)) :=
    Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
  have hd (c : centralizer (H : Set D)) : (a.centralizerLinear c).val.det = 1 := by
    have hh := Abelianization.commutator_subset_ker
      (Matrix.GeneralLinearGroup.det.comp a.centralizerLinear)
      (Group.IsPerfect.mem_commutator (g := c))
    exact congrArg Units.val hh
  let j : centralizer (H : Set D) →* SL(2,Field) :=
    { toFun c := ⟨(a.centralizerLinear c).val,hd c⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' c d := by
        apply Subtype.ext
        change (a.centralizerLinear (c*d)).val =
          (a.centralizerLinear c).val * (a.centralizerLinear d).val
        rw [map_mul,Units.val_mul] }
  have hj : Function.Injective j := by
    intro c d he
    apply a.centralizerLinear_injective
    apply Units.ext
    exact congrArg Subtype.val he
  have hcard : Nat.card (centralizer (H : Set D)) = Nat.card SL(2,Field) := by
    rw [Nat.card_congr e₀.toEquiv,nat_card_alternatingGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 2 (by decide)]
    norm_num [Nat.factorial]
  exact ⟨MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨hj,hcard⟩),
    fun _ => rfl⟩

private theorem transpose_mul (g h : SL(2,Field)) :
    SpecialLinearGroup.transpose (g*h) = SpecialLinearGroup.transpose h * SpecialLinearGroup.transpose g := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

private theorem transpose_transpose (g : SL(2,Field)) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g) = g := by
  apply Subtype.ext
  exact Matrix.transpose_transpose _

private theorem transpose_inv (g : SL(2,Field)) :
    SpecialLinearGroup.transpose g⁻¹ = (SpecialLinearGroup.transpose g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←transpose_mul,mul_inv_cancel]
  apply Subtype.ext
  exact Matrix.transpose_one

private def graph : MulAut SL(2,Field) where
  toFun g := (SpecialLinearGroup.transpose g)⁻¹
  invFun g := (SpecialLinearGroup.transpose g)⁻¹
  left_inv g := by dsimp only; rw [transpose_inv,transpose_transpose,inv_inv]
  right_inv g := by dsimp only; rw [transpose_inv,transpose_transpose,inv_inv]
  map_mul' g h := by rw [transpose_mul,_root_.mul_inv_rev]

private def matrixSpace : W ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) Field := a.space

private theorem component_matrix (h : H) (w : W) :
    a.matrixSpace (ρ h w) = a.matrixSpace w * (a.component h).val.transpose := by
  have hc : a.coefficient h = 1 := MonoidHom.mem_ker.mp (a.coefficient_kernel.symm ▸ h.property)
  funext i k
  change a.space (ρ h w) i k = ∑ j : Fin 2, a.space w i j * (a.component h).val k j
  have hh := a.equivariant h w i
  rw [hc,a.component_marking] at hh
  simp only [SL2AutomorphismNatural.action_conj] at hh
  have hh' := congrFun hh k
  fin_cases i <;> fin_cases k <;> simpa [matrixSpace,Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
    Fin.sum_univ_two,mul_comm] using hh'

private theorem centralizer_matrix (c : centralizer (H : Set D)) (w : W) :
    a.matrixSpace (ρ c w) = (a.centralizerLinear c).val * a.matrixSpace w := by
  funext i k
  change a.space (ρ c w) i k = ∑ j : Fin 2, (a.centralizerLinear c).val i j * a.space w j k
  have hh := congrFun (a.centralizer_action c w i) k
  simpa [matrixSpace,Matrix.mul_apply] using hh

include a in
private theorem component_disjoint : Disjoint H (centralizer (H : Set D)) := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro g hg
  have ha : a.automorphism g = 1 := MonoidHom.mem_ker.mp (a.automorphism_kernel.symm ▸ hg.2)
  have hh := a.component_marking ⟨g,hg.1⟩
  rw [ha] at hh
  have h1 : a.component ⟨g,hg.1⟩ = 1 :=
    (MulAut.conj_injective_of_center_eq_bot (Theory.PSL2.sl2_center_eq_bot Field))
      (hh.symm.trans (map_one MulAut.conj).symm)
  exact Subtype.ext_iff.mp (a.component.injective (h1.trans a.component.map_one.symm))

private def concreteSpace : Matrix (Fin 2) (Fin 2) Field ≃ₗ[ZMod 2] ClassicalOrthogonal.FourPlusMatrix.Binary.V where
  toFun v i j := SL2FourNatural.fieldEquiv.symm (v i j)
  invFun v i j := SL2FourNatural.fieldEquiv (v i j)
  left_inv v := by funext i j; exact SL2FourNatural.fieldEquiv.apply_symm_apply _
  right_inv v := by funext i j; exact SL2FourNatural.fieldEquiv.symm_apply_apply _
  map_add' v w := by funext i j; exact map_add SL2FourNatural.fieldEquiv.symm _ _
  map_smul' c v := by
    funext i j
    change SL2FourNatural.fieldEquiv.symm (c • v i j) = c • SL2FourNatural.fieldEquiv.symm (v i j)
    exact ZMod.map_smul SL2FourNatural.fieldEquiv.symm.toAddMonoidHom c (v i j)

private theorem concreteSpace_mul (A : Matrix (Fin 2) (Fin 2) Field) (v : Matrix (Fin 2) (Fin 2) Field) :
    concreteSpace (A*v) = A.map SL2FourNatural.fieldEquiv.symm * concreteSpace v := by
  funext i j
  change SL2FourNatural.fieldEquiv.symm (∑ k, A i k * v k j) =
    ∑ k, SL2FourNatural.fieldEquiv.symm (A i k) * SL2FourNatural.fieldEquiv.symm (v k j)
  simp only [map_sum,map_mul]

private theorem concreteSpace_mul_right (v : Matrix (Fin 2) (Fin 2) Field) (A : Matrix (Fin 2) (Fin 2) Field) :
    concreteSpace (v*A) = concreteSpace v * A.map SL2FourNatural.fieldEquiv.symm := by
  funext i j
  change SL2FourNatural.fieldEquiv.symm (∑ k, v i k * A k j) =
    ∑ k, SL2FourNatural.fieldEquiv.symm (v i k) * SL2FourNatural.fieldEquiv.symm (A k j)
  simp only [map_sum,map_mul]

/-- The full projective coefficient image gives the actual determinant
action of the original component-centralizer product on the whole module. -/
theorem orthogonal_coordinates_of_coefficient_top
    (B : LinearMap.BilinForm (ZMod 2) W) (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (htop : a.coefficientFive.range = ⊤) :
    ∃ (e : ↥(H ⊔ centralizer (H : Set D)) ≃* ClassicalOrthogonal.FourPlusMatrix.Binary.G)
      (f : W ≃ₗ[ZMod 2] ClassicalOrthogonal.FourPlusMatrix.Binary.V),
      ∀ (g : ↥(H ⊔ centralizer (H : Set D))) w,
        f (ρ g w) = ClassicalOrthogonal.FourPlusMatrix.Binary.action (e g) (f w) := by
  obtain ⟨c,hc⟩ := a.centralizer_special B hnd hB htop
  obtain ⟨p,hp⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    H (centralizer (H : Set D)) a.component_disjoint
    (by intro h hh c hc; exact (hc h hh).symm)
  let e₀ := ((a.component.trans graph).prodCongr c).trans MulEquiv.prodComm
  let e₁ := SL2FourNatural.standardGroupEquiv.symm.prodCongr SL2FourNatural.standardGroupEquiv.symm
  let e := p.symm.trans (e₀.trans e₁)
  let f := a.matrixSpace.trans concreteSpace
  refine ⟨e,f,?_⟩
  intro g w
  obtain ⟨⟨h,k⟩,rfl⟩ := p.surjective g
  change concreteSpace (a.matrixSpace (ρ (p (h,k)) w)) = _
  rw [hp,map_mul,Module.End.mul_apply,a.component_matrix,a.centralizer_matrix,
    concreteSpace_mul_right,concreteSpace_mul]
  have he : e (p (h,k)) = (SL2FourNatural.standardGroupEquiv.symm (c k),
      SL2FourNatural.standardGroupEquiv.symm (graph (a.component h))) := by
    change e₁ (e₀ (p.symm (p (h,k)))) = _
    rw [p.symm_apply_apply]
    rfl
  rw [he,ClassicalOrthogonal.FourPlusMatrix.Binary.action_apply]
  have hl : (a.centralizerLinear k).val.map SL2FourNatural.fieldEquiv.symm =
      (SL2FourNatural.standardGroupEquiv.symm (c k)).val := by rw [←hc]; rfl
  have hr : (a.component h).val.transpose.map SL2FourNatural.fieldEquiv.symm =
      (SL2FourNatural.standardGroupEquiv.symm (graph (a.component h)))⁻¹.val := by
    rw [←map_inv]
    change _ = (SL2FourNatural.standardGroupEquiv.symm
      (((SpecialLinearGroup.transpose (a.component h))⁻¹)⁻¹)).val
    rw [inv_inv]
    rfl
  rw [hl,hr]
  rfl

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineSemilinear.Coordinates

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Theory.GroupTheory ClassicalOrthogonal.FourPlusMatrix
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
open Chapter14.Section03.NonabelianSource.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full S₅ coefficient case is orthogonal on the literal two-residual,
and is excluded by the original flag geometry. -/
theorem source_coefficient_top_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    {H : Subgroup F.TerminalHdot}
    (a : FixedLineSemilinear.Coordinates F.terminalRepresentation H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hnd : B.Nondegenerate)
    (hB : ∀ g u v, B (F.terminalRepresentation g u) (F.terminalRepresentation g v) = B u v)
    (htop : a.coefficientFive.range = ⊤) : False := by
  let := chosen.elementary
  let := F.U_normal
  obtain ⟨e,f,hf⟩ := a.orthogonal_coordinates_of_coefficient_top B hnd hB htop
  let N := H ⊔ centralizer (H : Set F.TerminalHdot)
  let : N.Normal := by
    change (H ⊔ centralizer (H : Set F.TerminalHdot)).Normal
    rw [←a.ambientField_kernel]
    infer_instance
  have hres := OrthogonalOrbit.residual_eq_of_coordinates F.terminalRepresentation
    F.terminalRepresentation_injective B hnd hB N e f hf
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let R := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hR : R.map q.toMonoidHom = N := by
    dsimp only [R]
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ q.surjective,hres]
  let eR : R ≃* N := (q.subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  apply Orthogonal.source_orthogonal_exclusion d earlier hq chosen structural alternatives F hne hZ
    ((eR.trans e).trans elementaryEquiv) (f.trans Binary.binaryCoordinates.symm)
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

namespace FixedLineReduction

/-- The original fixed-line data after excluding the full coefficient image.
The surviving coefficient isomorphism retains its actual permutation map. -/
@[expose] def TranspositionRemainder {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (B : LinearMap.BilinForm (ZMod 2) W)
    (v : W) (E : Submodule (ZMod 2) W) (X : Subgroup D) : Prop :=
  ∃ C : Subgroup D, IsComponent D C ∧ ⁅C,X⁆ ≠ ⊥ ∧
    ChapterG.Section10.ComponentOrthogonalData ρ B C ∧
    ∃ I : Submodule (ZMod 2) W,
      Representation.BinaryOffender.Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I ∧
      ((v ∈ I ∧ C.Normal ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) W = 8 ∧
        Nat.card X = 8 ∧
        Nat.card ((centralizer (componentOrbit C ⊤ : Set D)).subgroupOf X) = 2 ∧
        ∃ a : FixedLineSemilinear.Coordinates ρ (componentOrbit C ⊤),
          Function.Surjective (a.ambientField.comp X.subtype) ∧
          pCore 2 a.coefficientField.ker = ⊥ ∧
          (componentOrbit C ⊤ ⊔ centralizer (componentOrbit C ⊤ : Set D)).index = 2 ∧
          componentOrbit C ⊤ ⊔ centralizer (componentOrbit C ⊤ : Set D) ⊔ X = ⊤ ∧
          Function.Injective a.coefficientFive ∧
          pCore 2 (a.coefficientFive.range ⊓ alternatingGroup (Fin 5) : Subgroup (Equiv.Perm (Fin 5))) = ⊥ ∧
          Nat.card (X.map a.ambientFive) = 4 ∧
          (∀ P : Sylow 5 (Equiv.Perm (Fin 5)),
            ¬ a.coefficientFive.range ≤ normalizer ((P : Subgroup (Equiv.Perm (Fin 5))) : Set _)) ∧
          (∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
            ∃ e : a.coefficient.range ≃* centralizer ({t} : Set (Equiv.Perm (Fin 5))),
              ∀ b, (e b).val = a.coefficientFive b)) ∨
      (v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry ρ B v E X I))

/-- Apply the orthogonal exclusion to the recognized coefficient alternatives
of the same original flag, retaining the unmarked exchanged branch. -/
theorem source_large_transposition_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      TranspositionRemainder F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,hrem⟩ :=
    source_large_classified_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,?_⟩
  obtain ⟨C,hC,hm,horth,I,hI,ha | hx⟩ := hrem
  · obtain ⟨hv,hCn,hI4,hV8,hX8,hY,a,hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive,hmodels⟩ := ha
    rcases hmodels with ⟨e,he⟩ | ht
    · have htop : a.coefficientFive.range = ⊤ := MonoidHom.range_eq_top.mpr (by
        intro s
        obtain ⟨b,rfl⟩ := e.surjective s
        exact ⟨b,(he b).symm⟩)
      exact (source_coefficient_top_exclusion d earlier hq chosen structural alternatives F hne hZ
        a B hyp.nondegenerate hyp.preserves htop).elim
    · exact ⟨C,hC,hm,horth,I,hI,Or.inl ⟨hv,hCn,hI4,hV8,hX8,hY,a,
        hfield,hcore,hindex,hgen,hinj,heven,hfour,hfive,ht⟩⟩
  · exact ⟨C,hC,hm,horth,I,hI,Or.inr hx⟩

end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
