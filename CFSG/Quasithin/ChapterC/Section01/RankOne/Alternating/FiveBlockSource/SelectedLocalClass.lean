module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicLocalGroup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicSeed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.BaumannMap
/-!
# The selected cubic local class on the original Baumann group

For the actual marked S₅ action, the cubic selected inside L moves an
omega-center vector. Its commutator generation transfers this movement to
J(P). The index-three theorem then constructs the local class, and the
intermediate-subgroup identities identify its Baumann group with the
original one. The final embedding preserves the literal ambient inclusion
and applies the single preselected characteristic pair.
Source: Aschbacher–Smith C.1.21(4), C.1.23(1), printed pp.129–130.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open scoped IsMulCommutative
open ChapterB Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
universe u
variable {H : Type u} [Group H] [Finite H]

private theorem maxJ_eq_intermediate (R P : Subgroup H)
    (hBP : baumann R ≤ P) (hPR : P ≤ R) :
    elementaryAbelianMaxJ P = elementaryAbelianMaxJ R := by
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq P R hPR
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R P
    ((elementaryAbelianMaxJ_le_baumann R).trans hBP)
  have ho := le_antisymm hsmall.1 hlarge.1
  exact le_antisymm (hsmall.2 ho) (hlarge.2 ho.symm)

theorem selected_cubic_omega_movement
    (q : H →* Sym) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (L : Subgroup H) [L.Normal] (hL : L.map q = alternatingGroup (Fin 5))
    (S : Sylow 2 (cubicLocalGroup q))
    (hS : (S : Subgroup (cubicLocalGroup q)).map (cubicLocalGroup q).subtype = cubicLocalTwoGroup q)
    (hJ : (elementaryAbelianMaxJ (cubicLocalTwoGroup q)).map q = OuterFourGeometry.four)
    (hseed : ⁅omegaOneCenterAmbient (cubicLocalTwoGroup q),selectedResidual q L⁆ ≠ ⊥) :
    ¬ elementaryAbelianMaxJ (S : Subgroup (cubicLocalGroup q)) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup (cubicLocalGroup q)) : Set (cubicLocalGroup q)) : Set (cubicLocalGroup q)) := by
  let N := cubicLocalGroup q
  let V := normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N)
  let J := elementaryAbelianMaxJ (S : Subgroup N)
  have hJM : J.map N.subtype = elementaryAbelianMaxJ (cubicLocalTwoGroup q) := by
    rw [← elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,hS]
  have hY := cubicLocalGroup_residual q hq L hL hk
  have hc : pResidual 2 N = ⁅pResidual 2 N,J⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,hY,hJM]
    exact selectedResidual_eq_commutator q L _ hL hJ hk
  intro hfix
  have hres : pResidual 2 N ≤ centralizer (V : Set N) := by
    rw [hc]
    exact (commutator_mono le_rfl hfix).trans (commutator_le_right _ _)
  have hv : ⁅V,pResidual 2 N⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hres)
  have hz : ⁅omegaOneCenterAmbient (S : Subgroup N),pResidual 2 N⁆ = ⊥ :=
    bot_unique ((commutator_mono (fun _ hx => subset_normalClosure hx) le_rfl).trans hv.le)
  apply hseed
  have hh := congrArg (map N.subtype) hz
  rwa [map_commutator,←omegaOneCenterAmbient_map_injective N.subtype N.subtype_injective,
    hS,hY,Subgroup.map_bot] at hh

theorem selected_cubic_localClass_of_seed
    (q : H →* Sym) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hfit : generalizedFitting H = pCore 2 H) (hQ : pCore 2 H ≤ q.ker)
    (L : Subgroup H) [L.Normal] (hL : L.map q = alternatingGroup (Fin 5))
    (R : Subgroup H) (hR : R.map q = OuterFourGeometry.eight) (hkR : q.ker ≤ R)
    (hB : (baumann R).map q = OuterFourGeometry.four)
    (hJ : (elementaryAbelianMaxJ R).map q = OuterFourGeometry.four)
    (hseed : ⁅omegaOneCenterAmbient (cubicLocalTwoGroup q),selectedResidual q L⁆ ≠ ⊥) :
    ∃ S : Sylow 2 (cubicLocalGroup q),
      (S : Subgroup (cubicLocalGroup q)).map (cubicLocalGroup q).subtype = cubicLocalTwoGroup q ∧
      (baumann (S : Subgroup (cubicLocalGroup q))).map (cubicLocalGroup q).subtype = baumann R ∧
      GlaubermanNiles.InLocalClass (inclusion
        (show baumann (S : Subgroup (cubicLocalGroup q)) ≤
          pResidual 2 (cubicLocalGroup q) ⊔ baumann (S : Subgroup (cubicLocalGroup q)) from le_sup_right)) := by
  obtain ⟨S,hS⟩ := cubicLocalTwoGroup_sylow q hq hk
  have hPN : cubicLocalTwoGroup q ≤ cubicLocalGroup q :=
    comap_mono OuterFourGeometry.four_le_local
  have hSM : (S : Subgroup (cubicLocalGroup q)).map (cubicLocalGroup q).subtype = cubicLocalTwoGroup q := by
    rw [hS,map_subgroupOf_eq_of_le hPN]
  obtain ⟨hBP,hPR⟩ := cubicLocalTwoGroup_bounds q R (baumann R) hR hkR hB
  have hJP : (elementaryAbelianMaxJ (cubicLocalTwoGroup q)).map q = OuterFourGeometry.four := by
    rw [maxJ_eq_intermediate R _ hBP hPR,hJ]
  have hm := selected_cubic_omega_movement q hq hk L hL S hSM hJP hseed
  refine ⟨S,hSM,?_,cubic_omega_inLocalClass S (hS ▸ cubicLocalTwoGroup_index q hq)
    (cubicLocalGroup_characteristic q hfit hQ) hm⟩
  calc
    _ = baumann ((S : Subgroup (cubicLocalGroup q)).map (cubicLocalGroup q).subtype) :=
      baumann_map_injective _ (cubicLocalGroup q).subtype_injective _
    _ = baumann (cubicLocalTwoGroup q) := congrArg baumann hSM
    _ = baumann R := (lemma_B_2_3_4 R (cubicLocalTwoGroup q) hBP hPR).symm



theorem selected_cubic_localClass
    (q : H →* Sym) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hfit : generalizedFitting H = pCore 2 H) (hQ : pCore 2 H ≤ q.ker)
    (L : Subgroup H) [L.Normal] (hL : L.map q = alternatingGroup (Fin 5))
    (R : Subgroup H) (hR : R.map q = OuterFourGeometry.eight) (hkR : q.ker ≤ R)
    (hB : (baumann R).map q = OuterFourGeometry.four)
    (hJ : (elementaryAbelianMaxJ R).map q = OuterFourGeometry.four)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hker : q.ker = centralizer (U : Set H)) (hUP : U ≤ cubicLocalTwoGroup q)
    (e : Additive U ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ g v, e (NormalElementaryQuotient.representation U q hq hker g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (e v)) :
    ∃ S : Sylow 2 (cubicLocalGroup q),
      (S : Subgroup (cubicLocalGroup q)).map (cubicLocalGroup q).subtype = cubicLocalTwoGroup q ∧
      (baumann (S : Subgroup (cubicLocalGroup q))).map (cubicLocalGroup q).subtype = baumann R ∧
      GlaubermanNiles.InLocalClass (inclusion
        (show baumann (S : Subgroup (cubicLocalGroup q)) ≤
          pResidual 2 (cubicLocalGroup q) ⊔ baumann (S : Subgroup (cubicLocalGroup q)) from le_sup_right)) := by
  exact selected_cubic_localClass_of_seed q hq hk hfit hQ L hL R hR hkR hB hJ
    (selected_omega_seed U q hq hker L _ hL
      (map_comap_eq_self_of_surjective hq _) hUP e he)

/-- The original Baumann group is the domain of the actual selected local
embedding.  Both its ambient map and the selected target are identified. -/
theorem selected_cubic_original_pair_of_seed
    (q : H →* Sym) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hfit : generalizedFitting H = pCore 2 H) (hQ : pCore 2 H ≤ q.ker)
    (L : Subgroup H) [L.Normal] (hL : L.map q = alternatingGroup (Fin 5))
    (R : Subgroup H) (hR : R.map q = OuterFourGeometry.eight) (hkR : q.ker ≤ R)
    (hB : (baumann R).map q = OuterFourGeometry.four)
    (hJ : (elementaryAbelianMaxJ R).map q = OuterFourGeometry.four)
    (hseed : ⁅omegaOneCenterAmbient (cubicLocalTwoGroup q),selectedResidual q L⁆ ≠ ⊥)
    (D : GlaubermanNiles.CharacteristicPair (baumann R)) (hD : D.Universal.{u,u}) :
    ∃ (A : Subgroup (cubicLocalGroup q)) (j : baumann R →* A),
      A.map (cubicLocalGroup q).subtype = selectedResidual q L ⊔ baumann R ∧
      ((cubicLocalGroup q).subtype.comp A.subtype).comp j = (baumann R).subtype ∧
      GlaubermanNiles.InLocalClass j ∧ GlaubermanNiles.Alternatives D.first D.second j := by
  obtain ⟨S,hS,hBS,hi⟩ := selected_cubic_localClass_of_seed q hq hk hfit hQ L hL R hR hkR hB hJ hseed
  let N := cubicLocalGroup q
  let B := baumann (S : Subgroup N)
  let A := pResidual 2 N ⊔ B
  let a : B ≃* baumann R := (B.equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr hBS)
  let j : baumann R →* A := (inclusion (show B ≤ A from le_sup_right)).comp a.symm.toMonoidHom
  have hj : GlaubermanNiles.InLocalClass j := hi.precomp_equiv a.symm
  refine ⟨A,j,?_,?_,hj,hD _ _ hj⟩
  · exact (Subgroup.map_sup _ _ _).trans (congrArg₂ (· ⊔ ·)
      (cubicLocalGroup_residual q hq L hL hk) hBS)
  · ext b
    change ((a.symm b : B) : H) = (b : H)
    exact congrArg (fun x : baumann R => (x : H)) (a.apply_symm_apply b)

theorem selected_cubic_original_pair
    (q : H →* Sym) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hfit : generalizedFitting H = pCore 2 H) (hQ : pCore 2 H ≤ q.ker)
    (L : Subgroup H) [L.Normal] (hL : L.map q = alternatingGroup (Fin 5))
    (R : Subgroup H) (hR : R.map q = OuterFourGeometry.eight) (hkR : q.ker ≤ R)
    (hB : (baumann R).map q = OuterFourGeometry.four)
    (hJ : (elementaryAbelianMaxJ R).map q = OuterFourGeometry.four)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hker : q.ker = centralizer (U : Set H)) (hUP : U ≤ cubicLocalTwoGroup q)
    (e : Additive U ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ g v, e (NormalElementaryQuotient.representation U q hq hker g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (e v))
    (D : GlaubermanNiles.CharacteristicPair (baumann R)) (hD : D.Universal.{u,u}) :
    ∃ (A : Subgroup (cubicLocalGroup q)) (j : baumann R →* A),
      A.map (cubicLocalGroup q).subtype = selectedResidual q L ⊔ baumann R ∧
      ((cubicLocalGroup q).subtype.comp A.subtype).comp j = (baumann R).subtype ∧
      GlaubermanNiles.InLocalClass j ∧ GlaubermanNiles.Alternatives D.first D.second j := by
  exact selected_cubic_original_pair_of_seed q hq hk hfit hQ L hL R hR hkR hB hJ
    (selected_omega_seed U q hq hker L _ hL
      (map_comap_eq_self_of_surjective hq _) hUP e he) D hD

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
