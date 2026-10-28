module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourComponentAction
public import Theory.GroupTheory.SimpleSectionOrder
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.Representation.SpecialLinearRestriction
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Equality of the Hermitian residual and containing component in the quintic row

The same simple quotient of K is a section of every nontrivial image of K:
a proper normal kernel is central modulo O₂(K). Its action on the original
four-space has order dividing 20160; the actual determinant-one plane over
F₁₆ has order dividing 4080. Thus the simple quotient has order dividing
240. The original SL₂(4) quotient of R survives the solvable central-core
kernel, so its image has order at least 60. A perfect group has no proper
subgroup of index at most four, hence that image is the whole simple quotient.

The original Sylow makes O₂(K) normalize R. Lifting the radical supplement
through the quasisimple quotient now proves R=K, with no overgroup table or
assumed action faithfulness. Both full central and residual kernels remain.
The chosen-module application discharges every input on the actual quintic
branch; the cubic branch and final exclusion remain separate obligations.

Source: Aschbacher–Smith 8.2.8(1), printed p.719, final paragraph,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Normalizer.SmallOvergroups Normalizer.TensorRecognition
set_option backward.isDefEq.respectTransparency false

private def centralProjection (A : Type*) [Group A] :
    A →* (A ⧸ pCore 2 A) ⧸ center (A ⧸ pCore 2 A) :=
  (QuotientGroup.mk' (center (A ⧸ pCore 2 A))).comp (QuotientGroup.mk' (pCore 2 A))

private theorem centralProjection_surjective (A : Type*) [Group A] :
    Function.Surjective (centralProjection A) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

private theorem centralProjection_kernel_solvable (A : Type*) [Group A] [Finite A] :
    Group.IsSolvable (centralProjection A).ker := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let f : (centralProjection A).ker →* center (A ⧸ pCore 2 A) :=
    (q.comp (centralProjection A).ker.subtype).codRestrict _ (by
      intro x
      exact (QuotientGroup.eq_one_iff (q x.val)).mp x.property)
  have hk : IsPGroup 2 f.ker := by
    let j : f.ker →* pCore 2 A := {
      toFun x := ⟨x.val.val,by
        apply (QuotientGroup.eq_one_iff x.val.val).mp
        exact congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    exact pCore_isPGroup.of_injective j (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 A => (z : A)) h)))
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- Every nontrivial image sees the same simple central quotient. -/
private theorem centralProjection_card_dvd {A H : Type*} [Group A] [Finite A] [Group H]
    [Group.IsPerfect A] [IsQuasisimple (A ⧸ pCore 2 A)]
    (f : A →* H) (hf : f ≠ 1) :
    Nat.card ((A ⧸ pCore 2 A) ⧸ center (A ⧸ pCore 2 A)) ∣ Nat.card H := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hc : f.ker.map q ≤ center (A ⧸ pCore 2 A) := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [←map_top_of_surjective q (QuotientGroup.mk'_surjective _),←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact normal_kernel_commutator_le_twoCore f.ker
      (fun ht => hf (MonoidHom.ker_eq_top_iff.mp ht))
  have hker : f.ker ≤ (centralProjection A).ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff (q x)).mpr
    exact hc (mem_map_of_mem q hx)
  let π := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective
    ⟨centralProjection A,by simpa only [MonoidHom.ker_rangeRestrict] using hker⟩
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨a,rfl⟩ := centralProjection_surjective A s
    exact ⟨f.rangeRestrict a,by simp [π]⟩
  exact (card_dvd_of_surjective π hπ).trans f.range.card_subgroup_dvd_card

private def planeSpecialLinear {A F W : Type*} [Group A] [Field F]
    [AddCommGroup W] [Module F W] [Group.IsPerfect A]
    (β : A →* (W ≃ₗ[F] W)) (b : Module.Basis (Fin 2) F W) : A →* SL(2,F) := by
  let ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp β
  exact {
    toFun a := ⟨LinearMap.toMatrix b b (ρ a),by
      rw [LinearMap.det_toMatrix,Representation.det_eq_one_of_perfect]⟩
    map_one' := by apply Subtype.ext; simp only [map_one,LinearMap.toMatrix_one]; rfl
    map_mul' a b' := by apply Subtype.ext; simp only [map_mul,LinearMap.toMatrix_mul]; rfl }

private theorem planeSpecialLinear_ne_one {A F W : Type*} [Group A] [Field F]
    [AddCommGroup W] [Module F W] [Group.IsPerfect A]
    (β : A →* (W ≃ₗ[F] W)) (b : Module.Basis (Fin 2) F W) (hn : β ≠ 1) :
    planeSpecialLinear β b ≠ 1 := by
  intro hh
  apply hn
  ext a v
  have he := congrArg Subtype.val (DFunLike.congr_fun hh a)
  have hm : (β a).toLinearMap = 1 := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_one]
    exact he
  exact LinearMap.congr_fun hm v

variable {G : Type*} [Group G] [Finite G]

/-- The simultaneous source actions bound the common simple quotient by 240. -/
theorem quintic_component_central_order {R K I U : Subgroup G}
    [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)] [IsElementaryAbelian 2 U]
    (ht : QuinticComponentAction R K I U) (hu : Nat.card U = 16)
    (hne : pCore 2 R ≠ ⊤)
    (hnon : ¬ R ≤ centralizer (U : Set G)) :
    Nat.card ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ∣ 240 := by
  obtain ⟨hUP,hP,eI,σ,hf,hKP,hKU,hIC,hRK,β,hd,hβ,_,_,hker,_⟩ := ht
  let := hUP
  let := hP
  let := InvertedFiveTensor.Sixteen.moduleSixteen σ hf
  have hβne : β ≠ 1 := by
    intro he
    have ht : (β.comp (inclusion hRK)).ker = ⊤ := by simp [he]
    exact hne (hker.symm.trans ht)
  let b := Module.finBasisOfFinrankEq Sixteen (CoreSection I U) hd
  have hdP := centralProjection_card_dvd (planeSpecialLinear β b)
    (planeSpecialLinear_ne_one β b hβne)
  have hcardP : Nat.card SL(2,Sixteen) = 4080 := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
      InvertedFiveTensor.Sixteen.card_field]
    norm_num
  let f := U.normalizerMonoidHom.comp (inclusion hKU)
  have hfn : f ≠ 1 := by
    intro he
    apply hnon
    intro r hr
    have hh : inclusion hKU (⟨r,hRK hr⟩ : K) ∈ U.normalizerMonoidHom.ker :=
      by
        change f ⟨r,hRK hr⟩ = 1
        exact DFunLike.congr_fun he ⟨r,hRK hr⟩
    rwa [normalizerMonoidHom_ker] at hh
  have hdU := centralProjection_card_dvd f hfn
  have hcardU : Nat.card (MulAut U) = 20160 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow U 4 hu]
    norm_num [Fin.prod_univ_succ]
  rw [hcardP] at hdP
  rw [hcardU] at hdU
  exact Nat.dvd_gcd hdU hdP

/-- In the quintic row the original residual already fills the containing component. -/
theorem quintic_component_eq {R K I U : Subgroup G}
    [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)] [IsElementaryAbelian 2 U]
    (ht : QuinticComponentAction R K I U) (hu : Nat.card U = 16)
    (hR : (R ⧸ pCore 2 R) ≃* SL(2,E 1))
    (hnon : ¬ R ≤ centralizer (U : Set G))
    (hQR : K.pCoreIn 2 ≤ normalizer (R : Set G)) : R = K := by
  have htcopy := ht
  obtain ⟨hUP,hP,eI,σ,hf,hKP,hKU,hIC,hRK,β,hd,hβ,hdet,hkernel,hker,hx⟩ := htcopy
  have hcardR : Nat.card (R ⧸ pCore 2 R) = 60 := by
    rw [Nat.card_congr hR.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,card_E]
    norm_num
  have hne : pCore 2 R ≠ ⊤ := by intro he; rw [he] at hcardR; simp at hcardR
  let S := (K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)
  let π := centralProjection K
  have hS : Nat.card S ≤ 240 := Nat.le_of_dvd (by decide)
    (quintic_component_central_order ht hu hne hnon)
  let r := π.comp (inclusion hRK)
  let := centralProjection_kernel_solvable K
  let j : r.ker →* π.ker := {
    toFun x := ⟨inclusion hRK x.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective
    (f := j) (fun x y he => Subtype.ext ((inclusion_injective hRK) (congrArg Subtype.val he)))
  let : Group.IsSolvable r.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
  let : IsSimpleGroup PSL(2,E 1) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    (by rw [card_E]; norm_num)
  let : IsSimpleGroup SL(2,E 1) := (Theory.PSL2.sl2QuotientEquiv (E 1)).isSimpleGroup
  let : IsSimpleGroup (R ⧸ pCore 2 R) := hR.isSimpleGroup
  let : Group.IsPerfect SL(2,E 1) :=
    ⟨OrthogonalFourMinus.HermitianEquiv.sl2_commutator_eq_top 1⟩
  let : Group.IsPerfect (R ⧸ pCore 2 R) :=
    Group.IsPerfect.ofSurjective (f := hR.symm.toMonoidHom) hR.symm.surjective
  have hr : 60 ∣ Nat.card r.range := by
    rw [←hcardR]
    exact SimpleSection.card_dvd_of_solvable_representation
      (Group.IsPerfect.not_isSolvable _) (QuotientGroup.mk' (pCore 2 R))
      (QuotientGroup.mk'_surjective _) r.rangeRestrict
  have hrlo : 60 ≤ Nat.card r.range := Nat.le_of_dvd Nat.card_pos hr
  have heq := r.range.index_mul_card
  have hi : r.range.index ≤ 4 := by nlinarith
  let : Group.IsPerfect (⊤ : Subgroup S) := inferInstance
  have htop : r.range = ⊤ := top_unique
    (le_of_isPerfect_of_index_le_four ⊤ r.range hi)
  have hgen : R.subgroupOf K ⊔ π.ker = ⊤ := by
    have he := congrArg (Subgroup.comap π) htop
    have hincl : (inclusion hRK).range = R.subgroupOf K := inclusion_range hRK
    simpa only [r,MonoidHom.range_comp,hincl,comap_map_eq,comap_top] using he
  have hrad : solvableRadical K ⊔ R.subgroupOf K = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le le_sup_right
      ((le_solvableRadical π.ker inferInstance inferInstance).trans le_sup_left)
  have hQ : pCore 2 K ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [←subgroupOf_normalizer_eq hRK]
    intro k hk
    exact hQR (mem_map_of_mem K.subtype hk)
  have hRtop := eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 K) (R.subgroupOf K) hQ hrad
  exact le_antisymm hRK (fun k hk => show k ∈ R from
    (show (⟨k,hk⟩ : K) ∈ R.subgroupOf K from hRtop ▸ mem_top _))
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
