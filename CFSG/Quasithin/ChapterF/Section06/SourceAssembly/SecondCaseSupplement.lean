module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.NoncyclicExtension
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The normal supplement in F.6.18(2)

In the marked elementary model, projection onto the first cubic coordinate
has a normal kernel supplementing the first parabolic. The Heisenberg model
uses its b-coordinate in the same way. Both kernels miss the marked cubic
residual. Pulling this kernel through the original quotient retains these
properties. The literal unmarked source row supplies the existing marked
models: its order excludes collapse and a cyclic overlap, while its normal
three-subgroup forces a noncyclic three-core.

Source: Aschbacher–Smith, F.6.16 and F.6.18(2), printed pp.308–310;
the normal-supplement application in 14.6.10(5), printed p.1028.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open MarkedCubicRecognition
theorem second_case_models_solvable {A : Type*} [Group A] [Finite A]
    {A₁ A₂ : Subgroup A} (h : IsGoldschmidtTriple A₁ A₂)
    (hm : Nonempty ((A ⧸ pPrimeCore 3 A) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      Nonempty ((A ⧸ pPrimeCore 3 A) ≃* HeisenbergExtension)) : Group.IsSolvable A := by
  let : Group.IsSolvable (pPrimeCore 3 A) := h.primeToThreeCore_solvable
  apply (Group.isSolvable_iff_subgroup_quotient (pPrimeCore 3 A)).mpr
  refine ⟨inferInstance,?_⟩
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨e⟩ := hm
    obtain ⟨f,hf,_,_,hcard,_,⟨eq⟩⟩ := heisenberg_extension_data e
    let : Group.IsNilpotent f.ker := (IsPGroup.of_card (p := 3) (n := 3)
      (by simpa using hcard)).isNilpotent
    let : Group.IsSolvable ((A ⧸ pPrimeCore 3 A) ⧸ f.ker) :=
      Group.isSolvable_of_isSolvable_injective (f := eq.toMonoidHom) eq.injective
    exact (Group.isSolvable_iff_subgroup_quotient f.ker).mpr ⟨inferInstance,inferInstance⟩

end CFSG.Quasithin.ChapterF.SourceAssembly

open Subgroup
open MarkedCubicRecognition
namespace CFSG.Quasithin.ChapterF.Noncyclic.MarkedRecognition

private def bCoordinate : HeisenbergPrime 3 →* C3 where
  toFun z := Multiplicative.ofAdd z.b
  map_one' := rfl
  map_mul' z w := by rfl

private def heisenbergProjection : HeisenbergExtension →* NineExtension :=
  SemidirectProduct.map ((MonoidHom.inl C3 C3).comp bCoordinate) (MonoidHom.id Four)
    (by intro t; apply MonoidHom.ext; intro z; revert z t; decide +kernel)

private def nineProjection : NineExtension →* NineExtension :=
  SemidirectProduct.map ((MonoidHom.inl C3 C3).comp (MonoidHom.fst C3 C3))
    (MonoidHom.id Four) (by intro t; apply MonoidHom.ext; intro z; revert z t; decide +kernel)

private theorem marked_normal_supplement
    {G M D : Type*} [Group G] [Finite G] [Group M] [Group D]
    {A B : Subgroup G} {ρ : Four →* MulAut M} {U V : Subgroup M}
    (m : MarkedModel A B M ρ U V)
    (f : (M ⋊[ρ] Four) →* D)
    (hlift : ∀ x : M ⋊[ρ] Four, ∃ y ∈ U, ∃ t : Four,
      f (SemidirectProduct.inl y * SemidirectProduct.inr t) = f x)
    (hne : ∃ y ∈ U, f (SemidirectProduct.inl y) ≠ 1) :
    ∃ P : Subgroup G, P.Normal ∧ P ⊔ A = ⊤ ∧
      ¬ (pResidual 2 A).map A.subtype ≤ P := by
  let q := f.comp m.ambientEquiv.symm.toMonoidHom
  have hU (y : M) (hy : y ∈ U) :
      m.ambientEquiv (SemidirectProduct.inl y) ∈ (pResidual 2 A).map A.subtype := by
    have hh : m.residualEquiv y ∈ residualLine A := by
      rw [←m.left_line]
      exact mem_map_of_mem m.residualEquiv.toMonoidHom hy
    rw [m.residual_apply]
    exact hh
  refine ⟨q.ker,inferInstance,?_,?_⟩
  · apply top_unique
    intro g _
    obtain ⟨y,hy,t,ht⟩ := hlift (m.ambientEquiv.symm g)
    let a := m.ambientEquiv (SemidirectProduct.inl y * SemidirectProduct.inr t)
    have ha : a ∈ A := by
      dsimp [a]
      rw [map_mul,m.complement_apply]
      exact A.mul_mem ((map_subtype_le _) (hU y hy)) (m.complementEquiv t).property.1
    have hqa : q a = q g := by simpa only [q,a,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using ht
    have hk : g * a⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hqa,mul_inv_cancel]
    have hh := (q.ker ⊔ A).mul_mem
      ((le_sup_left : q.ker ≤ q.ker ⊔ A) hk)
      ((le_sup_right : A ≤ q.ker ⊔ A) ha)
    simpa only [inv_mul_cancel_right] using hh
  · intro hh
    obtain ⟨y,hy,hne⟩ := hne
    have hk := MonoidHom.mem_ker.mp (hh (hU y hy))
    apply hne
    simpa only [q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hk

/-- Each marked solvable model has a normal supplement missing the first cubic residual. -/
theorem marked_second_cases_normal_supplement
    {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hm : Nonempty (MarkedModel A B Nine nineAction
        (MonoidHom.inl C3 C3).range (MonoidHom.inr C3 C3).range) ∨
      Nonempty (MarkedModel A B (HeisenbergPrime 3) heisenbergAction
        leftAxis.range rightAxis.range)) :
    ∃ P : Subgroup G, P.Normal ∧ P ⊔ A = ⊤ ∧
      ¬ (pResidual 2 A).map A.subtype ≤ P := by
  rcases hm with hm | hm
  · obtain ⟨m⟩ := hm
    apply marked_normal_supplement m nineProjection
    · intro x
      refine ⟨(x.left.1,1),⟨x.left.1,rfl⟩,x.right,?_⟩
      ext <;> simp [nineProjection,SemidirectProduct.map]
    · refine ⟨(Multiplicative.ofAdd 1,1),⟨_,rfl⟩,?_⟩
      decide +kernel
  · obtain ⟨m⟩ := hm
    apply marked_normal_supplement m heisenbergProjection
    · intro x
      refine ⟨leftAxis (Multiplicative.ofAdd x.left.b),⟨_,rfl⟩,x.right,?_⟩
      ext <;> simp [heisenbergProjection,SemidirectProduct.map,bCoordinate,leftAxis]
    · refine ⟨leftAxis (Multiplicative.ofAdd 1),⟨_,rfl⟩,?_⟩
      decide +kernel
end CFSG.Quasithin.ChapterF.Noncyclic.MarkedRecognition

namespace CFSG.Quasithin.ChapterF.Noncyclic.MarkedRecognition
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

omit [Finite D] in
/-- Pull the actual normal supplement through the quotient map. -/
theorem normal_supplement_preimage (q : G →* D) (hq : Function.Surjective q)
    (A : Subgroup G) (P : Subgroup D) [P.Normal]
    (hgen : P ⊔ A.map q = ⊤)
    (hmiss : ¬ (pResidual 2 (A.map q)).map (A.map q).subtype ≤ P) :
    (P.comap q).Normal ∧ P.comap q ⊔ A = ⊤ ∧
      ¬ (pResidual 2 A).map A.subtype ≤ P.comap q := by
  refine ⟨inferInstance,?_,?_⟩
  · have hm : (P.comap q ⊔ A).map q = ⊤ := by
      rw [Subgroup.map_sup,map_comap_eq,MonoidHom.range_eq_top.mpr hq,top_inf_eq,hgen]
    have hh := congrArg (Subgroup.comap q) hm
    rw [comap_map_eq,comap_top,sup_eq_left.mpr
      ((ker_le_comap q P).trans le_sup_left)] at hh
    exact hh
  · intro hh
    apply hmiss
    rw [←map_embedded_pResidual 2 A q]
    exact (map_le_iff_le_comap).mpr hh
end CFSG.Quasithin.ChapterF.Noncyclic.MarkedRecognition


namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Subgroup Theory.GroupTheory MarkedCubicRecognition
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
theorem second_case_order_noncyclic
    (hm : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup D, ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty ((D ⧸ N) ≃* Four)) :
    (Nat.card D = 36 ∨ Nat.card D = 108) ∧ ¬ IsCyclic (pCore 3 D) := by
  rcases hm with hm | ⟨N,hN,hex,hcard,_,⟨e⟩⟩
  · obtain ⟨e⟩ := hm
    have hc : Nat.card D = 36 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    refine ⟨Or.inl hc,?_⟩
    intro hcy
    let : IsCyclic (pCore 3 D) := hcy
    let A := alternatingGroup (Fin 3)
    have hAc : Nat.card A = 3 := by
      rw [Nat.card_eq_fintype_card]; decide +kernel
    have hp : IsPGroup 3 (A.prod A : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
      apply IsPGroup.of_card (n := 2)
      rw [Nat.card_congr (prodEquiv A A).toEquiv,Nat.card_prod,hAc]
      norm_num
    let X := (A.prod A).map e.symm.toMonoidHom
    let : X.Normal := Normal.map inferInstance _ e.symm.surjective
    have hX : X ≤ pCore 3 D := le_sSup ⟨inferInstance,hp.map _⟩
    let : IsCyclic X := isCyclic_of_injective (inclusion hX) (inclusion_injective _)
    let : IsCyclic (A.prod A : Subgroup _) :=
      isCyclic_of_injective (equivMapOfInjective (A.prod A) e.symm.toMonoidHom
        e.symm.injective).toMonoidHom
        (equivMapOfInjective (A.prod A) e.symm.toMonoidHom e.symm.injective).injective
    let : IsCyclic (A × A) := isCyclic_of_surjective (prodEquiv A A).toMonoidHom
      (prodEquiv A A).surjective
    have hh := coprime_card_of_isCyclic_prod A A
    rw [hAc] at hh
    norm_num at hh
  · let : N.Normal := hN
    let : IsExtraspecial 3 N := hex
    have hc : Nat.card D = 108 := by
      rw [←N.card_mul_index,index_eq_card,Nat.card_congr e.toEquiv,hcard]
      norm_num [Four,C2,Nat.card_prod]
    refine ⟨Or.inr hc,?_⟩
    intro hcy
    let : IsCyclic (pCore 3 D) := hcy
    have hNcore : N ≤ pCore 3 D := le_sSup ⟨inferInstance,IsExtraspecial.isPGroup 3 N⟩
    let : IsCyclic N := isCyclic_of_injective (inclusion hNcore) (inclusion_injective _)
    have he : center N = ⊤ := center_eq_top
    have hh := IsExtraspecial.center_order_p 3 N
    rw [he,Nat.card_congr Subgroup.topEquiv.toEquiv,hcard] at hh
    omega

/-- The literal unmarked row (2) supplies its existing marked source models. -/
theorem marked_second_case_of_unmarked
    {A : Type*} [Group A] [Finite A] {K : GroupClass}
    (hsq : IsSQTK K A) {A₁ A₂ : Subgroup A} (h : IsGoldschmidtTriple A₁ A₂)
    (hm : Nonempty ((A ⧸ pPrimeCore 3 A) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup (A ⧸ pPrimeCore 3 A), ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty (((A ⧸ pPrimeCore 3 A) ⧸ N) ≃* Four)) :
    let q := QuotientGroup.mk' (pPrimeCore 3 A)
    Nonempty (Noncyclic.MarkedRecognition.MarkedModel (A₁.map q) (A₂.map q) Nine nineAction
      (MonoidHom.inl C3 C3).range (MonoidHom.inr C3 C3).range) ∨
    Nonempty (Noncyclic.MarkedRecognition.MarkedModel (A₁.map q) (A₂.map q)
      (HeisenbergPrime 3) heisenbergAction leftAxis.range rightAxis.range) := by
  have hc := second_case_order_noncyclic hm
  have hqt : IsGoldschmidtTriple
      (A₁.map (QuotientGroup.mk' (pPrimeCore 3 A)))
      (A₂.map (QuotientGroup.mk' (pPrimeCore 3 A))) := by
    rcases h.primeToThreeCore_dichotomy with hg | hb
    · exact hg.2.1
    · obtain ⟨e⟩ := hb.2.2.1
      have hcard : Nat.card (A ⧸ pPrimeCore 3 A) = 6 := by
        rw [Nat.card_congr e.toEquiv]
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
      rcases hc.1 with hh | hh <;> omega
  apply source_marked_models hsq (MulEquiv.refl _) hqt hc.2
  rintro ⟨e⟩
  obtain ⟨S,hS⟩ := hqt.intersection_sylow
  have hcard : Nat.card S = 2 := by
    rw [←hS,Nat.card_congr e.toEquiv]
    simp
  have hh := (S : Subgroup (A ⧸ pPrimeCore 3 A)).card_mul_index
  rw [hcard] at hh
  have hn := S.not_dvd_index
  rcases hc.1 with he | he <;> rw [he] at hh
  · have hi : (S : Subgroup (A ⧸ pPrimeCore 3 A)).index = 18 := by omega
    exact hn (hi ▸ (by decide))
  · have hi : (S : Subgroup (A ⧸ pPrimeCore 3 A)).index = 54 := by omega
    exact hn (hi ▸ (by decide))
end CFSG.Quasithin.ChapterF.SourceAssembly
