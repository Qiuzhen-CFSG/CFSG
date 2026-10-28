module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.Kernel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.NormalizedSupCard
public import Stellmacher.SectionOne.SL2FamilySylowCoordinates

/-!
# Native factors of a solvable minimal-parabolic quotient

The original characteristic-subgroup obstruction and unique maximal
subgroup hypothesis provide the native SL₂(2) factor family on the canonical
Section Two module. Its derived product is the image of the original
two-residual. The kernel reduction identifies the literal residual kernel
with the actual core commutator.

The indexed factors, module supports, Sylow image and elementary Thompson
image remain those supplied by Stellmacher (2.2) and (2.4), journal p.20,
`refs/latex/stellmacher-n-group.tex`. This prepares the local solvable
outside-block argument in Aschbacher–Smith C.1.29, printed pp.132–134.
-/

public section
namespace CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
open Subgroup Stellmacher
open scoped commutatorElement
universe u
variable {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
  [MulDistribMulAction G V]

private theorem twoPerfect_of_threeGroup {A : Type*} [Group A] (hA : IsPGroup 3 A) :
    IsPPerfect 2 A := by
  apply (pResidual_eq_top_iff 2 A).mp
  apply top_unique
  intro a _
  exact mem_pResidual_of_orderOf_coprime
    (hA.orderOf_coprime (by decide : Nat.Coprime 3 2) a).symm

/-- The residual of a normal native S₃ product with a Sylow supplement is
its literal derived subgroup. -/
theorem residual_eq_derived_of_native_product
    (S : Sylow 2 G) (E : Subgroup G) [E.Normal]
    (hES : E ⊔ (S : Subgroup G) = ⊤)
    {n : ℕ} (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D)
    (hD : ∀ i, SectionOne.IsOneSevenFactor (V := V) (D i)) :
    pResidual 2 G = (commutator E).map E.subtype := by
  let F := (commutator E).map E.subtype
  let : F.Normal := inferInstance
  let : IsElementaryAbelian 3 F :=
    SectionOne.internalOneSevenProduct_derived_isElementaryAbelian E D hprod hD
  have hFp : IsPPerfect 2 F := twoPerfect_of_threeGroup (IsElementaryAbelian.isPGroup 3 F)
  obtain ⟨_, hSi⟩ := SectionOne.sl2_family_sylow_coordinates S E inferInstance D hprod
    (fun i => (hD i).1)
  have hEF : E ≤ F ⊔ (S : Subgroup G) := by
    rw [hprod.1]
    apply iSup_le
    intro i
    let A := (commutator (D i)).map (D i).subtype
    let T := (S : Subgroup G) ⊓ D i
    have hAn : D i ≤ normalizer (A : Set G) :=
      (D i).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (D i) (commutator (D i)))
    have hAnT : T ≤ normalizer (A : Set G) := inf_le_right.trans hAn
    have hAc : Nat.card A = 3 := (hD i).2.1.2.1
    have hTc : Nat.card T = 2 := hSi i
    have hd : Disjoint A T := disjoint_of_coprime_natCard (by rw [hAc, hTc]; decide)
    have hcard : Nat.card (A ⊔ T : Subgroup G) = Nat.card (D i) := by
      rw [card_sup_eq_mul_of_normalizes_of_disjoint A T hAnT hd, hAc, hTc,
        SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (hD i).1]
    have heq : A ⊔ T = D i := eq_of_le_of_card_ge
      (sup_le (map_subtype_le _) inf_le_right) hcard.ge
    have hAF : A ≤ F := by
      rw [show F = (commutator E).map E.subtype from rfl, hprod.derived.1]
      exact le_iSup (fun j : Fin n => (commutator (D j)).map (D j).subtype) i
    rw [← heq]
    exact sup_le (hAF.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hFS : F ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← hES]
    exact sup_le hEF le_sup_right
  exact pResidual_eq_of_isPPerfect F hFp
    (isPGroup_quotient_of_sup_eq_top F (S : Subgroup G) S.isPGroup' hFS)

/-- The native elementary-three quotient kills the residual's remaining
central two-kernel after dividing by the actual core commutator. -/
theorem residual_inf_core_eq
    (h : SectionTwo.Hypotheses G) (S : Sylow 2 G)
    {B : Type u} [Group B] (q : G →* B)
    (hker : q.ker = SectionTwo.cSubgroup S)
    (hW : ⁅pCore 2 G, pResidual 2 G⁆ ≤ SectionTwo.vSubgroup S)
    (hQC : pCore 2 G ≤ centralizer (SectionTwo.vSubgroup S : Set G))
    (himage : IsElementaryAbelian 3 ((pResidual 2 G).map q)) :
    pResidual 2 G ⊓ pCore 2 G = ⁅pCore 2 G, pResidual 2 G⁆ := by
  let R := pResidual 2 G
  let W := ⁅pCore 2 G, R⁆
  let Z := W.subgroupOf R
  let : Z.Normal := inferInstance
  let : IsElementaryAbelian 3 (R.map q) := himage
  let f : R →* R.map q := q.subgroupMap R
  have hN := residual_inf_centralizer_eq h S hW hQC
  have hkQ : f.ker ≤ (pCore 2 G).subgroupOf R := by
    intro x hx
    have hc : (x : G) ∈ SectionTwo.cSubgroup S := by
      rw [← hker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact (hN.le ⟨x.property, hc⟩).2
  have hZ : Z ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change q x = 1
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact hQC ((SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h S).1 (hW hx))
  have hcomm : ⁅f.ker, (⊤ : Subgroup R)⁆ ≤ Z := by
    rw [commutator_le]
    intro x hx y _
    change ⁅(x : G), (y : G)⁆ ∈ W
    exact commutator_mem_commutator (hkQ hx) y.property
  have heq := ker_eq_of_twoPerfect_of_elementary_three (isPPerfect_pResidual 2) f Z hZ
    (pCore_isPGroup.comap_subtype.to_le hkQ) hcomm
  apply le_antisymm
  · intro x hx
    have hf : (⟨x, hx.1⟩ : R) ∈ f.ker := by
      apply Subtype.ext
      change q x = 1
      apply MonoidHom.mem_ker.mp
      rw [hker]
      exact hQC hx.2
    rw [heq] at hf
    exact hf
  · exact le_inf (commutator_le_right _ _) (commutator_le_left _ _)

end CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic

namespace CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
open Subgroup Stellmacher
universe u
variable {G B : Type u} [Group G] [Finite G] [Group B] [Finite B]
variable (S : Sylow 2 G) (q : G →* B) (hq : Function.Surjective q)

/-- The same native factor family, quotient map and original support action. -/
structure NativeData [MulDistribMulAction B (SectionTwo.vSubgroup S)] where
  E : Subgroup B
  E_normal : E.Normal
  E_baumann : E = normalClosure
    (((S : Subgroup G) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)).map q : Set B)
  n : ℕ
  D : Fin n → Subgroup B
  product : IsInternalDirectProductFamily E D
  independent : iSupIndep D
  injective : Function.Injective D
  factors : ∀ i, SectionOne.IsOneSevenFactor (V := SectionTwo.vSubgroup S) (D i)
  module_product : IsInternalDirectProductFamily (⊤ : Subgroup (SectionTwo.vSubgroup S))
    (fun i : Option (Fin n) => match i with
      | none => FixedPoints.subgroup E (SectionTwo.vSubgroup S)
      | some i => commutatorAction (D i) (SectionTwo.vSubgroup S))
  thompson : (elementaryAbelianMaxJ (S : Subgroup G)).map q =
    (S.mapSurjective hq : Subgroup B) ⊓ E
  residual_image : (pResidual 2 G).map q = (commutator E).map E.subtype
  commutator_le : ⁅pCore 2 G, pResidual 2 G⁆ ≤ SectionTwo.vSubgroup S
  core_centralizes : pCore 2 G ≤ centralizer (SectionTwo.vSubgroup S : Set G)
  residual_kernel : pResidual 2 G ⊓ q.ker = ⁅pCore 2 G, pResidual 2 G⁆

/-- Construct the native factors and remove the actual residual's two-kernel. -/
theorem exists_nativeData (h : SectionTwo.Hypotheses G)
    (hker : q.ker = SectionTwo.cSubgroup S)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hu : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    letI := SectionTwo.quotientConjugationAction S q hq hker
    Nonempty (NativeData S q hq) := by
  classical
  let : IsElementaryAbelian 2 (SectionTwo.vSubgroup S) :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let := SectionTwo.quotientConjugationAction S q hq hker
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let B₀ := (S : Subgroup G) ⊓ centralizer (omegaOneCenterAmbient J : Set G)
  let L := normalClosure (B₀ : Set G)
  let Jbar := J.map q
  let E := ⁅SectionOne.oddCore B, Jbar⁆ ⊔ Jbar
  obtain ⟨hcore, hnot, _⟩ := SectionTwo.two_four_initial_reduction h S hP hu
  have hQC : pCore 2 G ≤ centralizer (SectionTwo.vSubgroup S : Set G) := by
    rw [hcore]
    exact inf_le_right
  have hJne : Jbar ≠ ⊥ := by
    intro he
    have hc : J ≤ centralizer (SectionTwo.vSubgroup S : Set G) := by
      change J ≤ SectionTwo.cSubgroup S
      rw [← hker]
      exact (map_eq_bot_iff J).mp he
    exact hnot (le_centralizer_iff.mp hc)
  have h22 := SectionTwo.lemma_two_two h S q hq hker ((S : Subgroup G).map q)
    Jbar (B₀.map q) rfl B₀ rfl rfl rfl hJne
  let : E.Normal := h22.part_a
  have hclosureJ : normalClosure (Jbar : Set B) = E := by
    apply le_antisymm
    · exact normalClosure_le_normal (show Jbar ≤ E from le_sup_right)
    · exact sup_le
        ((commutator_mono le_rfl le_normalClosure).trans (commutator_le_right _ _))
        le_normalClosure
  have hclosureB : normalClosure (B₀.map q : Set B) = E := by
    rw [← h22.part_b]
    exact hclosureJ
  have hLmap : L.map q = E := by
    rw [show L = normalClosure (B₀ : Set G) from rfl, map_normalClosure _ q hq]
    exact hclosureB
  obtain ⟨K, _, _, hKL, _, _, hKS⟩ :=
    SectionTwo.two_four_exists_local_sl2Frattini_factor h S hcore hnot hu
  have hLS : L ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← hKS]
    exact sup_le_sup_right hKL _
  have hES : E ⊔ (S.mapSurjective hq : Subgroup B) = ⊤ := by
    have hm := congrArg (Subgroup.map q) hLS
    simpa only [Subgroup.map_sup, hLmap, Subgroup.map_top_of_surjective q hq, Sylow.coe_mapSurjective] using hm
  obtain ⟨hJB, n, D, _, hprod, hinj, hD, _, hmodule⟩ :=
    SectionTwo.nativeBaumann_action_factors h S q hq hker B₀ rfl hJne
  rw [hclosureB] at hprod hmodule
  have hres := residual_eq_derived_of_native_product (S.mapSurjective hq) E hES D hprod hD
  have himage : (pResidual 2 G).map q = (commutator E).map E.subtype := by
    rw [map_pResidual_of_surjective 2 q hq, hres]
  have hthree : IsElementaryAbelian 3 ((pResidual 2 G).map q) := by
    rw [himage]
    exact SectionOne.internalOneSevenProduct_derived_isElementaryAbelian E D hprod hD
  have hW : ⁅pCore 2 G, pResidual 2 G⁆ ≤ SectionTwo.vSubgroup S := by
    rw [← twoResidualAmbient_top_eq_pResidual]
    exact SectionTwo.lemma_two_four h S hP hu
  have hkernel : pResidual 2 G ⊓ q.ker = ⁅pCore 2 G, pResidual 2 G⁆ := by
    rw [hker]
    exact (residual_inf_centralizer_eq h S hW hQC).trans
      (residual_inf_core_eq h S q hker hW hQC hthree)
  have hJleT : Jbar ≤ (S.mapSurjective hq : Subgroup B) := by
    apply map_mono
    exact sSup_le fun _ hA => hA.1
  have hJinf : Jbar = (S.mapSurjective hq : Subgroup B) ⊓ E := by
    simpa only [E, SectionOne.oddCore] using
      SectionOne.oddCore_commutator_join_sylow_inf (S.mapSurjective hq) Jbar hJleT
  have hind : iSupIndep D := Subgroup.iSupIndep_of_centerless_of_pairwise_commute D
    (fun i => SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two (hD i).1)
    (fun i j hij x y hx hy => hprod.2.2 i j hij x hx y hy)
  exact ⟨⟨E, inferInstance, hclosureB.symm, n, D, hprod, hind, hinj, hD,
    hmodule, hJinf, himage, hW, hQC, hkernel⟩⟩

end CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic
