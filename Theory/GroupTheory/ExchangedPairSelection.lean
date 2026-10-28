module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
/-!
# An index-two selection on an exchanged pair

For a split actor A₁ × A₂, combine a first-factor selection R₁,L₁ with the
whole passive actor A₂. The relative index and commutator identity survive the
product. An ambient factor exchange extends first-factor Sylow generation to
the whole group. The construction retains the literal paired embedding.

Source: the paired natural-action step of Aschbacher–Smith 3.1.9(5), 15.1.12(4).
-/
public section
open Subgroup
namespace Subgroup
variable {D E G : Type*} [Group D] [Group E] [Group G]
private theorem product_relIndex (A R : Subgroup D) (B : Subgroup E) (hRA : R ≤ A) :
    (R.prod B).relIndex (A.prod B) = R.relIndex A := by
  have he : R.prod B = (R.comap (MonoidHom.fst D E)) ⊓ A.prod B := by
    ext x
    exact ⟨fun h => ⟨h.1,hRA h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
  rw [he,inf_relIndex_right,relIndex_comap]
  congr 1
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy.1
  · intro hx
    exact ⟨(x,1),⟨hx,B.one_mem⟩,rfl⟩

private theorem product_normalizes (A R : Subgroup D) (B C : Subgroup E)
    (hAR : A ≤ normalizer (R : Set D)) (hBC : B ≤ normalizer (C : Set E)) :
    A.prod B ≤ normalizer (R.prod C : Set (D × E)) := by
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  exact and_congr (mem_normalizer_iff.mp (hAR hg.1) x.1)
    (mem_normalizer_iff.mp (hBC hg.2) x.2)

/-- Retain the passive coordinate of a split actor and the active coordinate's cubic.
An ambient element exchanging the factors turns the first-factor generation into
whole-group generation, while preserving the original actor and its index two. -/
theorem exchanged_pair_selection
    (j : D × D →* G) (hj : Function.Injective j)
    (S : Subgroup G) (A₁ A₂ R₁ L₁ P₁ : Subgroup D)
    (hRA : R₁ ≤ A₁)
    (hAS : (A₁.prod A₂).map j ≤ S)
    (hPS : (P₁.prod (⊥ : Subgroup D)).map j ≤ S)
    (hAR : A₁ ≤ normalizer (R₁ : Set D))
    (hLR : L₁ ≤ normalizer (R₁ : Set D))
    (hAL : A₁ ≤ normalizer (L₁ : Set D))
    (hidx : R₁.relIndex A₁ = 2)
    (hcomm : L₁ = ⁅L₁,A₁⁆)
    (hgen : L₁ ⊔ P₁ = ⊤)
    (hbase : j.range ⊔ S = ⊤)
    (hex : ∃ t ∈ S,
      (((⊤ : Subgroup D).prod (⊥ : Subgroup D)).map j).map
        (MulAut.conj t).toMonoidHom = ((⊥ : Subgroup D).prod (⊤ : Subgroup D)).map j) :
    ∃ R L : Subgroup G,
      R ≤ S ∧ (A₁.prod A₂).map j ≤ normalizer (R : Set G) ∧
      L ≤ normalizer (R : Set G) ∧
      (A₁.prod A₂).map j ≤ normalizer (L : Set G) ∧
      R.relIndex ((A₁.prod A₂).map j) = 2 ∧
      L = ⁅L,(A₁.prod A₂).map j⁆ ∧ L ⊔ S = ⊤ := by
  let R := (R₁.prod A₂).map j
  let L := (L₁.prod (⊥ : Subgroup D)).map j
  refine ⟨R,L,(map_mono (prod_mono hRA le_rfl)).trans hAS,?_,?_,?_,?_,?_,?_⟩
  · exact (map_mono (product_normalizes A₁ R₁ A₂ A₂ hAR A₂.le_normalizer)).trans
      ((R₁.prod A₂).le_normalizer_map j)
  · exact (map_mono (product_normalizes L₁ R₁ ⊥ A₂ hLR bot_le)).trans
      ((R₁.prod A₂).le_normalizer_map j)
  · exact (map_mono (product_normalizes A₁ L₁ A₂ ⊥ hAL le_normalizer_of_normal)).trans
      ((L₁.prod (⊥ : Subgroup D)).le_normalizer_map j)
  · exact (relIndex_map_map_of_injective _ _ hj).trans
      ((product_relIndex A₁ R₁ A₂ hRA).trans hidx)
  · change (L₁.prod (⊥ : Subgroup D)).map j =
      ⁅(L₁.prod (⊥ : Subgroup D)).map j,(A₁.prod A₂).map j⁆
    rw [←map_commutator,commutator_prod_prod,commutator_bot_left,←hcomm]
  · let J := L ⊔ S
    let i := j.comp (MonoidHom.inl D D)
    have hL : L₁.map i ≤ J := by
      rintro _ ⟨g,hg,rfl⟩
      exact (show L ≤ J from le_sup_left) ⟨(g,1),⟨hg,one_mem _⟩,rfl⟩
    have hP : P₁.map i ≤ J := by
      rintro _ ⟨g,hg,rfl⟩
      exact (show S ≤ J from le_sup_right) (hPS ⟨(g,1),⟨hg,one_mem _⟩,rfl⟩)
    have hI : (⊤ : Subgroup D).map i ≤ J := by
      rw [←hgen,map_sup]
      exact sup_le hL hP
    have hfirst : ((⊤ : Subgroup D).prod (⊥ : Subgroup D)).map j ≤ J := by
      rintro _ ⟨⟨a,b⟩,⟨_,hb⟩,rfl⟩
      change b = 1 at hb
      subst b
      exact hI ⟨a,mem_top _,rfl⟩
    obtain ⟨t,ht,hex⟩ := hex
    have hsecond : ((⊥ : Subgroup D).prod (⊤ : Subgroup D)).map j ≤ J := by
      rw [←hex]
      rintro _ ⟨g,hg,rfl⟩
      exact J.mul_mem (J.mul_mem ((show S ≤ J from le_sup_right) ht) (hfirst hg)) (J.inv_mem ((show S ≤ J from le_sup_right) ht))
    have hY : j.range ≤ J := by
      rintro _ ⟨⟨a,b⟩,rfl⟩
      have he : j (a,b) = j (a,1) * j (1,b) := by rw [←map_mul]; simp
      rw [he]
      exact J.mul_mem (hfirst ⟨(a,1),⟨mem_top _,one_mem _⟩,rfl⟩)
        (hsecond ⟨(1,b),⟨one_mem _,mem_top _⟩,rfl⟩)
    exact top_unique (hbase ▸ sup_le hY le_sup_right)
end Subgroup
