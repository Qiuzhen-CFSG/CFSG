module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneCore
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.TensorSection
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.ResidualAction
public import Theory.ElementaryAbelian.Quotient

/-!
# The two natural summands in the M24 cocode pair section

The native first-moment map on the trio pair space has the original affine
three-space as kernel. A perfect actor kills the symmetric-three affine
factor, so its action on that quotient is two copies of the literal natural
three-space. Transport through the original B and U markings gives an
explicit linear equivalence on B/U and identifies its residual kernel with
O₂(R). The plane action is contragredient in the native coordinates; the
proof compares kernels without identifying natural and dual representations.

The companion MathieuTrioMarking and NonFFSourceMathieuM24Section construct
the markings on the chosen pair. This is the cocode input to source 8.2.8(4);
the four-copy action on P/U and centralizer argument remain separate.
Source: Aschbacher--Smith H.15.6(3), 8.2.8, printed pp.401,718--719,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

private theorem perfect_trio_first {R : Type*} [Group R] [Group.IsPerfect R]
    (f : R →* trioStabilizer standardTrio) (r : R) :
    (standardAffineHom (f r)).1 = 1 := by
  let χ := (MonoidHom.fst _ _).comp (standardAffineHom.comp f)
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  have hp : r ∈ solvableResidual R := by rw [solvableResidual_eq_top]; trivial
  have hm := map_solvableResidual_le χ (mem_map_of_mem χ hp)
  rw [solvableResidual_eq_bot] at hm
  exact hm

private def pairCoordinates : standardPairSpace →ₗ[ZMod 2] (Vector × Vector) :=
  (BinaryPermutation.ThreeTensor.pairEquiv (V := Vector)).toLinearMap.comp pairMoment

private theorem pairCoordinates_surjective : Function.Surjective pairCoordinates :=
  (BinaryPermutation.ThreeTensor.pairEquiv (V := Vector)).surjective.comp pairMoment_surjective

private theorem pairCoordinates_zero (v : standardPairSpace) :
    pairCoordinates v = 0 ↔ v.val ∈ standardPlaneMap.range := by
  have hz : pairCoordinates v = 0 ↔ pairMoment v = 0 :=
    (BinaryPermutation.ThreeTensor.pairEquiv (V := Vector)).map_eq_zero_iff
  rw [hz,←LinearMap.mem_ker,pairMoment_ker_eq_standardPlanePairMap_range]
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨u,congrArg Subtype.val hu⟩
  · rintro ⟨u,hu⟩
    exact ⟨u,Subtype.ext hu⟩

private theorem pairCoordinates_action (g : trioStabilizer standardTrio)
    (hg : (standardAffineHom g).1 = 1) (v : standardPairSpace)
    (hv : cocodeRepresentation g.val v.val ∈ standardPairSpace) :
    pairCoordinates ⟨cocodeRepresentation g.val v.val,hv⟩ =
      (Matrix.SpecialLinearGroup.toLin' (standardAffineHom g).2 (pairCoordinates v).1,
       Matrix.SpecialLinearGroup.toLin' (standardAffineHom g).2 (pairCoordinates v).2) := by
  change BinaryPermutation.ThreeTensor.pairEquiv
    (cocodeMoment (cocodeRepresentation g.val v.val)) = _
  rw [cocodeMoment_equivariant g v.val v.property]
  have hq : standardAffineHom g = (1,(standardAffineHom g).2) := Prod.ext hg rfl
  change BinaryPermutation.ThreeTensor.pairEquiv
    (quotientTensorRepresentation (standardAffineHom g) (pairMoment v)) = _
  rw [hq]
  exact BinaryPermutation.ThreeTensor.pairEquiv_equivariant BinaryLinearThree.W
    (standardAffineHom g).2 (pairMoment v)

/-- On a perfect native trio actor, first moments give two copies of the
literal natural three-space, with the affine plane as their exact kernel. -/
theorem perfect_trio_pair_coordinates {R : Type*} [Group R] [Group.IsPerfect R]
    (f : R →* trioStabilizer standardTrio) :
    ∃ m : standardPairSpace →ₗ[ZMod 2] (Vector × Vector),
      Function.Surjective m ∧
      (∀ v, m v = 0 ↔ v.val ∈ standardPlaneMap.range) ∧
      ∀ (r : R) (v : standardPairSpace)
        (hv : cocodeRepresentation (f r).val v.val ∈ standardPairSpace),
        m ⟨cocodeRepresentation (f r).val v.val,hv⟩ =
          (Matrix.SpecialLinearGroup.toLin' (standardAffineHom (f r)).2 (m v).1,
           Matrix.SpecialLinearGroup.toLin' (standardAffineHom (f r)).2 (m v).2) :=
  ⟨pairCoordinates,pairCoordinates_surjective,pairCoordinates_zero,
    fun r v hv => pairCoordinates_action (f r) (perfect_trio_first f r) v hv⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
variable {G : Type*} [Group G]

/-- Native translations are exactly the perfect actor's plane fixers. -/
theorem perfect_trio_core_iff_plane {R : Type*} [Group R] [Group.IsPerfect R]
    (f : R →* trioStabilizer standardTrio) (r : R) :
    f r ∈ pCore 2 (trioStabilizer standardTrio) ↔
      ∀ v, cocodeRepresentation (f r).val (standardPlaneMap v) = standardPlaneMap v :=
  ⟨fun hr v => standardPlaneMap_fixed v (f r) hr,
    fun hr => plane_fixer_in_core (f r) (perfect_trio_first f r) hr⟩

/-- Transport the two natural summands through the actual B and U markings.
The kernel is the original U, and the action is literal conjugation. -/
theorem marked_pair_coordinates (W B U R : Subgroup G) [IsElementaryAbelian 2 W]
    [Group.IsPerfect R] (hBW : B ≤ W) (hRB : R ≤ normalizer (B : Set G))
    (hRW : R ≤ normalizer (W : Set G))
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (f : R →* trioStabilizer standardTrio)
    (hF : ∀ (r : R) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w)) =
        cocodeRepresentation (f r).val (F (Additive.ofMul w)))
    (hpair : ∀ w : W, (w : G) ∈ B ↔ F (Additive.ofMul w) ∈ standardPairSpace)
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    let := IsElementaryAbelian.of_le (p := 2) hBW
    ∃ m : Additive B →ₗ[ZMod 2] (Vector × Vector), Function.Surjective m ∧
      (∀ b : B, m (Additive.ofMul b) = 0 ↔ (b : G) ∈ U) ∧
      ∀ (r : R) (b : B),
        m (Additive.ofMul (B.normalizerMonoidHom ⟨r,hRB r.property⟩ b)) =
          (Matrix.SpecialLinearGroup.toLin' (standardAffineHom (f r)).2
              (m (Additive.ofMul b)).1,
           Matrix.SpecialLinearGroup.toLin' (standardAffineHom (f r)).2
              (m (Additive.ofMul b)).2) := by
  let := IsElementaryAbelian.of_le (p := 2) hBW
  let j : Additive B →ₗ[ZMod 2] standardPairSpace :=
    (F.toLinearMap.comp ((inclusion hBW).toAdditive.toZModLinearMap 2)).codRestrict _
      (fun b => (hpair _).mp b.toMul.property)
  have hj : Function.Surjective j := by
    intro v
    obtain ⟨w,hw⟩ := F.surjective v.val
    have hb : w.toMul.val ∈ B := (hpair w.toMul).mpr (hw ▸ v.property)
    exact ⟨Additive.ofMul ⟨w.toMul.val,hb⟩,Subtype.ext hw⟩
  refine ⟨pairCoordinates.comp j,pairCoordinates_surjective.comp hj,?_,?_⟩
  · intro b
    exact (pairCoordinates_zero (j (Additive.ofMul b))).trans (hplane _).symm
  · intro r b
    have hh : j (Additive.ofMul (B.normalizerMonoidHom ⟨r,hRB r.property⟩ b)) =
        ⟨cocodeRepresentation (f r).val (j (Additive.ofMul b)).val,by
          have hm := (j (Additive.ofMul (B.normalizerMonoidHom ⟨r,hRB r.property⟩ b))).property
          change F (Additive.ofMul (W.normalizerMonoidHom
            ⟨r,hRW r.property⟩ (inclusion hBW b))) ∈ _ at hm
          rwa [hF] at hm⟩ := by
      apply Subtype.ext
      exact hF r (inclusion hBW b)
    change pairCoordinates (j _) = _
    rw [hh]
    exact pairCoordinates_action (f r) (perfect_trio_first f r) _ _

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
variable {G : Type*} [Group G]

/-- The kernel of the residual on the literal B/U is its original two-core. -/
theorem marked_pair_section_kernel (W B U R : Subgroup G) [IsElementaryAbelian 2 W]
    [Group.IsPerfect R] (hBW : B ≤ W) (hUW : U ≤ W)
    (hRB : R ≤ normalizer (B : Set G)) (hRW : R ≤ normalizer (W : Set G))
    (hcore : R.pCoreIn 2 = R ⊓ centralizer (U : Set G))
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (f : R →* trioStabilizer standardTrio)
    (hF : ∀ (r : R) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w)) =
        cocodeRepresentation (f r).val (F (Additive.ofMul w)))
    (hpair : ∀ w : W, (w : G) ∈ B ↔ F (Additive.ofMul w) ∈ standardPairSpace)
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    ∀ r : R, (∀ b : B, ⁅(r : G),(b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R := by
  let := IsElementaryAbelian.of_le (p := 2) hBW
  obtain ⟨m,hm,hzero,hact⟩ := marked_pair_coordinates W B U R hBW hRB hRW F f hF hpair hplane
  have hc (r : R) : r ∈ pCore 2 R ↔ r.val ∈ centralizer (U : Set G) := by
    have he : r.val ∈ R.pCoreIn 2 ↔ r ∈ pCore 2 R := by
      constructor
      · rintro ⟨x,hx,he⟩
        exact (show x = r from Subtype.ext he) ▸ hx
      · exact mem_map_of_mem R.subtype
    rw [hcore] at he
    simpa only [mem_inf,r.property,true_and] using he.symm
  have hn (r : R) : f r ∈ pCore 2 (trioStabilizer standardTrio) ↔ r ∈ pCore 2 R := by
    rw [perfect_trio_core_iff_plane,hc]
    constructor
    · intro hf u hu
      let w : W := ⟨u,hUW hu⟩
      obtain ⟨v,hv⟩ := (hplane w).mp hu
      have he := hF r w
      rw [←hv,hf] at he
      have hw : W.normalizerMonoidHom ⟨r,hRW r.property⟩ w = w :=
        F.injective (he.trans hv)
      exact ((mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val hw)).symm
    · intro hr v
      obtain ⟨w,hw⟩ := F.surjective (standardPlaneMap v)
      have hu : w.toMul.val ∈ U := (hplane w.toMul).mpr (hw ▸ LinearMap.mem_range_self _ _)
      have hfix : W.normalizerMonoidHom ⟨r,hRW r.property⟩ w.toMul = w.toMul := by
        apply Subtype.ext
        exact (mul_inv_eq_iff_eq_mul).mpr (hr _ hu).symm
      rw [←hw]
      simpa only [ofMul_toMul] using (hF r w.toMul).symm.trans
        (congrArg F (congrArg Additive.ofMul hfix))
  have hd (r : R) (b : B) :
      ⁅r.val,b.val⁆ ∈ U ↔
        m (Additive.ofMul (B.normalizerMonoidHom ⟨r,hRB r.property⟩ b)) = m (Additive.ofMul b) := by
    let d : B := B.normalizerMonoidHom ⟨r,hRB r.property⟩ b / b
    have he : d.val = ⁅r.val,b.val⁆ := by
      change (r.val * b.val * r.val⁻¹) / b.val = _
      simp only [commutatorElement_def,div_eq_mul_inv]
    rw [←he,←hzero]
    change m (Additive.ofMul (B.normalizerMonoidHom ⟨r,hRB r.property⟩ b) - Additive.ofMul b) = 0 ↔ _
    rw [map_sub,sub_eq_zero]
  intro r
  rw [←hn]
  constructor
  · intro hr
    have hlin : Matrix.SpecialLinearGroup.toLin' (standardAffineHom (f r)).2 = 1 := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨b,hb⟩ := hm (v,0)
      have he := (hact r b.toMul).symm.trans ((hd r b.toMul).mp (hr b.toMul))
      simp only [ofMul_toMul,hb] at he
      exact congrArg Prod.fst he
    have hs : (standardAffineHom (f r)).2 = 1 :=
      Matrix.SpecialLinearGroup.toLin'_injective (hlin.trans (map_one _).symm)
    rw [←standardAffineHom_ker]
    exact Prod.ext (perfect_trio_first f r) hs
  · intro hr b
    apply (hd r b).mpr
    have hs : (standardAffineHom (f r)).2 = 1 :=
      congrArg Prod.snd (show standardAffineHom (f r) = 1 from
        (show f r ∈ standardAffineHom.ker from standardAffineHom_ker.symm ▸ hr))
    rw [hact,hs]
    rw [map_one]
    rfl

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
open Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G]

/-- The natural linear factor of the original trio residual is onto. -/
theorem residual_natural_surjective {R : Type*} [Group R]
    (f : R →* trioStabilizer standardTrio)
    (hf : f.range = solvableResidual (trioStabilizer standardTrio)) :
    Function.Surjective (Matrix.SpecialLinearGroup.toLin'.comp
      ((MonoidHom.snd _ _).comp (standardAffineHom.comp f))) := by
  let t := (MonoidHom.snd _ _).comp standardAffineHom
  have ht : Function.Surjective t := by
    intro a
    obtain ⟨g,hg⟩ := standardAffineHom_surjective (1,a)
    exact ⟨g,congrArg Prod.snd hg⟩
  let e := BinaryLinear.OuterCyclic.slEquivLinear 3
  let : Group.IsPerfect (BinaryLinear.GL Vector) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect SL(3,ZMod 2) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hm : (solvableResidual (trioStabilizer standardTrio)).map t = ⊤ := by
    rw [map_solvableResidual_eq t ht,solvableResidual_eq_top]
  intro a
  obtain ⟨A,hA⟩ := e.surjective a
  obtain ⟨g,hg,he⟩ := (show A ∈ (solvableResidual (trioStabilizer standardTrio)).map t by
    rw [hm]; trivial)
  rw [←hf] at hg
  obtain ⟨r,hr⟩ := hg
  refine ⟨r,?_⟩
  change Matrix.SpecialLinearGroup.toLin' (t (f r)) = a
  rw [hr,he,←hA]
  apply LinearEquiv.ext
  intro v
  exact (BinaryLinear.OuterCyclic.slEquivLinear_apply 3 A v).symm

/-- The literal quotient B/U is the sum of two natural three-spaces under
its actual residual action, with the original quotient representatives. -/
theorem marked_pair_section_natural (W B U R : Subgroup G) [IsElementaryAbelian 2 W]
    [Group.IsPerfect R] (hBW : B ≤ W) (hUW : U ≤ W)
    (hRB : R ≤ normalizer (B : Set G)) (hRW : R ≤ normalizer (W : Set G))
    (hRU : R ≤ normalizer (U : Set G))
    (hcore : R.pCoreIn 2 = R ⊓ centralizer (U : Set G))
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (f : R →* trioStabilizer standardTrio)
    (hf : f.range = solvableResidual (trioStabilizer standardTrio))
    (hF : ∀ (r : R) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w)) =
        cocodeRepresentation (f r).val (F (Additive.ofMul w)))
    (hpair : ∀ w : W, (w : G) ∈ B ↔ F (Additive.ofMul w) ∈ standardPairSpace)
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    let := IsElementaryAbelian.of_le (p := 2) hBW
    ∃ hUN : (U.subgroupOf B).Normal, letI := hUN
      ∃ (e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] (Vector × Vector))
        (π : R →* BinaryLinear.GL Vector),
        Function.Surjective π ∧
        (sectionAction R B U hRB hRU).ker = pCore 2 R ∧
        (∀ r v, π r v = Matrix.SpecialLinearGroup.toLin' (standardAffineHom (f r)).2 v) ∧
        ∀ (r : R) (z : B ⧸ U.subgroupOf B),
          e (Additive.ofMul (sectionAction R B U hRB hRU r z)) =
            (π r (e (Additive.ofMul z)).1,π r (e (Additive.ofMul z)).2) := by
  let := IsElementaryAbelian.of_le (p := 2) hBW
  let hUN : (U.subgroupOf B).Normal := inferInstance
  obtain ⟨m,hm,hzero,hact⟩ := marked_pair_coordinates W B U R hBW hRB hRW F f hF hpair hplane
  let g : B →* Multiplicative (Vector × Vector) :=
    { toFun := fun b => Multiplicative.ofAdd (m (Additive.ofMul b))
      map_one' := m.map_zero
      map_mul' := fun b c => m.map_add (Additive.ofMul b) (Additive.ofMul c) }
  have hg : Function.Surjective g := hm
  have hk : g.ker = U.subgroupOf B := by
    ext b
    exact hzero b
  let eg : (B ⧸ U.subgroupOf B) ≃* Multiplicative (Vector × Vector) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  let e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] (Vector × Vector) :=
    LinearEquiv.ofBijective (eg.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) eg.bijective
  let π : R →* BinaryLinear.GL Vector := Matrix.SpecialLinearGroup.toLin'.comp
    ((MonoidHom.snd _ _).comp (standardAffineHom.comp f))
  have hem (b : B) : e (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b)) =
      m (Additive.ofMul b) := rfl
  refine ⟨hUN,e,π,residual_natural_surjective f hf,?_,fun _ _ => rfl,?_⟩
  · ext r
    rw [mem_sectionAction_ker]
    exact marked_pair_section_kernel W B U R hBW hUW hRB hRW hcore F f hF hpair hplane r
  · intro r z
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) z
    rw [sectionAction_apply,hem,hem]
    exact hact r b

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
