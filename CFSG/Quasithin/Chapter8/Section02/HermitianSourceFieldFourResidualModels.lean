module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSieve
public import GorensteinWalter.SL2UniversalCover
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The actual residuals in the two remaining Hermitian source rows

The source sieve gives PSL₂(31) or PSL₃(2) after quotienting the normal
quasisimple residual by its full center. The prime-field covering theorem
makes the first covering kernel a two-group, which vanishes in a component
of the two-core-free ambient quotient. In the binary row the existing
odd-center covering theorem applies to the literal central quotient and the
original two-element field. Thus both full covering kernels are trivial.

Consequently J=O₂(H), and O²(H/O₂(H)) itself has one of the two concrete
models, retaining the maximal overlap and automizer or diagram markings.
This supplies the residuals used in the chief-section argument of
Aschbacher–Smith 8.2.9, printed pp.720–721, refs/quasithin.pdf
(1 March 2004 manuscript). Covering inputs: I.1.3, printed pp.407–408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

private theorem component_prime_image_injective
    (M K : Subgroup X) (hK : IsComponent X K) (hO : pCore 2 X=⊥)
    {F : Type*} [Field F] [Finite F] (hp : (Nat.card F).Prime) (hbig : 3<Nat.card F)
    (e : sourceImage M K ≃* PSL(2,F)) :
    Function.Injective ((QuotientGroup.mk' (sourceKernel M)).subgroupMap K) := by
  let : IsQuasisimple K := hK.2
  let : Fact (3<Nat.card F) := ⟨hbig⟩
  let q := QuotientGroup.mk' (sourceKernel M)
  let f := q.subgroupMap K
  let c : Covering K PSL(2,F) :=
    ⟨e.toMonoidHom.comp f,e.surjective.comp (q.subgroupMap_surjective K)⟩
  have h2 := GorensteinWalter.PSL2Cover.kernel_isPGroup_of_card_prime F c hp
  have hpK : pCore 2 K=⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1,hO]
    exact (K.subtype.ker_eq_bot_iff.mpr K.subtype_injective)
  have hker : c.toMonoidHom.ker=⊥ := bot_unique
    ((show c.toMonoidHom.ker ≤ pCore 2 K from le_sSup ⟨inferInstance,h2⟩).trans_eq hpK)
  have hi := c.toMonoidHom.ker_eq_bot_iff.mp hker
  exact fun x y he => hi (congrArg e he)

private theorem component_small_image_injective
    (M K : Subgroup X) (hK : IsComponent X K) (hO : pCore 2 X=⊥)
    (hJ : sourceKernel M = (center K).map K.subtype)
    (hm : ClassicalGroup.IsPSL (sourceImage M K) 2 31 ∨
      ClassicalGroup.IsPSL (sourceImage M K) 3 2) :
    Function.Injective ((QuotientGroup.mk' (sourceKernel M)).subgroupMap K) := by
  rcases hm with h31 | h2
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h31
    exact component_prime_image_injective M K hK hO (by rw [hcard]; decide)
      (by rw [hcard]; decide) e
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h2
    let : IsQuasisimple K := hK.2
    let q := QuotientGroup.mk' (sourceKernel M)
    let f := q.subgroupMap K
    have hk : f.ker = center K := by
      ext x
      change f x=1 ↔ x ∈ center K
      rw [Subtype.ext_iff]
      change q x=1 ↔ x ∈ center K
      constructor
      · intro hx
        have hxJ : (x : X) ∈ sourceKernel M := (QuotientGroup.eq_one_iff (x : X)).mp hx
        rw [hJ] at hxJ
        exact (mem_map_iff_mem K.subtype_injective).mp hxJ
      · intro hx
        apply (QuotientGroup.eq_one_iff (x : X)).mpr
        rw [hJ]
        exact mem_map_of_mem K.subtype hx
    let eZ : K ⧸ center K ≃* PSL(3,F) :=
      (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        ((QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective K)).trans e)
    have ho := GLS3.Chapter5.OddCentralCovers.component_center_odd hO K hK
    have hz := Matrix.PSL3.BinaryOddCenterCover.center_eq_bot_two hcard eZ ho
    exact f.ker_eq_bot_iff.mp (hk.trans hz)

/-- The full residual is PSL₂(31) or PSL₃(2), and the original maximal core equals O₂. -/
theorem parabolic_quotient_small_residual_models
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) = 2)
    (h3 : primeRank 3 X ≤ 1) (h5 : primeRank 5 X ≤ 1)
    (hrot : let q := QuotientGroup.mk' (pCore 2 X)
      ∀ (v r : X ⧸ pCore 2 X), v ∈ W.map q → v ≠ 1 → v*r*v⁻¹=r⁻¹ →
        ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a → orderOf r = p^a →
          orderOf r = 3 ∨ orderOf r = 5) :
    minimalParabolicCore S hP = pCore 2 X ∧
    let q := QuotientGroup.mk' (pCore 2 X)
    let M := (minimalParabolicMax S hP).map q
    let T := (S : Subgroup X).map q
    ∃ K : Subgroup (X ⧸ pCore 2 X), IsComponent (X ⧸ pCore 2 X) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (X ⧸ pCore 2 X) = K ∧
      center K = ⊥ ∧ K ⊔ T = ⊤ ∧ SingleClauses M K T ∧
      ((ClassicalGroup.IsPSL K 2 31 ∧ SingleOddLinearModel M K T) ∨
       ClassicalGroup.IsPSL K 3 2 ∧ DiagramModel M K T 1) := by
  obtain ⟨K,hcomp,hK,hn,hres,hcenter,hgen,hclauses,hmodels⟩ :=
    parabolic_quotient_small_rotation_models hX S hP hs W hWS hout hMW hcard h3 h5 hrot
  let := hn
  let N := pCore 2 X
  let q := QuotientGroup.mk' N
  let R := S.mapSurjective (QuotientGroup.mk'_surjective N)
  have hk : q.ker ≤ (S : Subgroup X) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  have hPq := minimalParabolic_surjective S hP q (QuotientGroup.mk'_surjective N) hk
  have hmax : minimalParabolicMax R hPq = (minimalParabolicMax S hP).map q :=
    (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective N)
      (by simpa only [q,QuotientGroup.ker_mk'] using minimalParabolicTwoCore_le_core S hP)).symm
  let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
  have hsq : ¬Group.IsSolvable (X ⧸ N) := fun hh =>
    hs ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,hh⟩)
  have hJ := Structure.core_eq_normal_component_center R hPq hsq
    (pCore_quotient_pCore_eq_bot 2) hcomp hgen
  have hmodels' := hmodels
  rw [←hmax] at hmodels'
  have hi := component_small_image_injective (minimalParabolicMax R hPq) K hcomp
    (pCore_quotient_pCore_eq_bot 2) hJ (hmodels'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  let j := QuotientGroup.mk' (sourceKernel (minimalParabolicMax R hPq))
  have hz : center K=⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply hi
    apply Subtype.ext
    change j x=1
    apply (QuotientGroup.eq_one_iff (x : X ⧸ N)).mpr
    change (x : X ⧸ N) ∈ minimalParabolicCore R hPq
    rw [hJ]
    exact mem_map_of_mem K.subtype hx
  have hcore : minimalParabolicCore S hP=pCore 2 X := by
    apply le_antisymm _ (minimalParabolicTwoCore_le_core S hP)
    have hm : (minimalParabolicCore S hP).map q=⊥ := by
      rw [hcenter,hz,Subgroup.map_bot]
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm
  let e : K ≃* sourceImage (minimalParabolicMax R hPq) K :=
    MulEquiv.ofBijective (j.subgroupMap K) ⟨hi,j.subgroupMap_surjective K⟩
  refine ⟨hcore,K,hcomp,hK,hn,hres,hz,hgen,hclauses,?_⟩
  rcases hmodels' with ⟨h31,hm⟩ | ⟨h2,hm⟩
  · obtain ⟨F,hF,hfin,hsize,⟨eF⟩⟩ := h31
    rw [hmax] at hm
    exact Or.inl ⟨⟨F,hF,hfin,hsize,⟨e.trans eF⟩⟩,hm⟩
  · obtain ⟨F,hF,hfin,hsize,⟨eF⟩⟩ := h2
    rw [hmax] at hm
    exact Or.inr ⟨⟨F,hF,hfin,hsize,⟨e.trans eF⟩⟩,hm⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
