module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Sylow
public import Theory.GroupTheory.DisjointCommutingProduct
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.Janko1.Model.Certification

/-!
# The two conjugate components and their quotient product

An index-two component normalizer makes the orbit exactly the join of a
component and any moving conjugate. A.3.7 makes their images modulo the orbit's
two-core commute. The initial model list and quasisimplicity make the first
image simple and centerless, so the two images are disjoint. Multiplication
then constructs the direct product, retaining its values on both inclusions.
Conjugation identifies the second intrinsic quotient with the first.

The universal A.3.7 implication is explicit. The source assembly supplies the
index and initial model list using the universal A.3.8 implication; no orbit,
product or factor identity is assumed here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Proposition
1.2.1(2)–(3), printed pp.503–504, and Proposition 1.3.4, pp.509–510.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedFactorsProof
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p : ℕ} {T X P H L : Subgroup G}

private theorem simple_of_linear_model {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) {q : ℕ} (hm : ClassicalGroup.IsPSL Q 2 q) :
    IsSimpleGroup Q := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  let _ := hq
  let _ : Group.IsPerfect PSL(2, F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hs : IsSimpleGroup PSL(2, F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  exact e.isSimpleGroup_congr.mpr hs

omit [Finite G] in
/-- The initial nonnormal models have simple intrinsic component quotients.
For the linear cases perfectness supplies the Iwasawa simplicity criterion,
so no exceptional small-field case is silently discarded. -/
theorem quotient_simple (h : SwappedInput 𝒦 p T X P H L)
    (hm : Section02.NonnormalCComponentModel (XiQuotient L)) :
    IsSimpleGroup (XiQuotient L) := by
  cases hm with
  | linear_even n hn iso => exact simple_of_linear_model h.quasisimple iso
  | linear_prime q hq ho iso => exact simple_of_linear_model h.quasisimple iso
  | suzuki m hm iso =>
    exact iso.some.isSimpleGroup_congr.mpr
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  | janko iso => exact iso.some.isSimpleGroup

omit [Finite G] in
/-- Index two identifies the entire orbit with the chosen two conjugates. -/
theorem orbit_eq_sup (h : SwappedInput 𝒦 p T X P H L)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2)
    {t : G} (ht : t ∈ T) (hm : t ∉ normalizer L) :
    componentOrbit L T = L ⊔ L.conjBy t := by
  have hTH : T ≤ H := le_sup_right.trans h.overgroup
  let tH : H := ⟨t, hTH ht⟩
  have htH : tH ∉ normalizer (L.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component.1]
    exact hm
  have hconj (s : T) : L.conjBy (s : G) = L ∨ L.conjBy (s : G) = L.conjBy t := by
    by_cases hs : (s : G) ∈ normalizer L
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hs)
    · have hsH : (⟨s, hTH s.property⟩ : H) ∉ normalizer (L.subgroupOf H : Set H) := by
        rw [← subgroupOf_normalizer_eq h.component.1]
        exact hs
      have he : tH⁻¹ * (⟨s, hTH s.property⟩ : H) ∈ normalizer (L.subgroupOf H : Set H) :=
        (mul_mem_iff_of_index_two hi).mpr (by simp [htH, hsH])
      rw [← subgroupOf_normalizer_eq h.component.1] at he
      have heq : L.conjBy (t⁻¹ * (s : G)) = L := mem_normalizer_iff_map_conj_eq.mp he
      have hh := congrArg (fun B : Subgroup G => B.conjBy t) heq
      rw [conjBy_mul, conjBy_inv'] at hh
      exact Or.inr hh
  apply le_antisymm
  · apply iSup_le
    intro s
    change L.conjBy (s : G) ≤ L ⊔ L.conjBy t
    rcases hconj s with he | he <;> rw [he]
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_componentOrbit L T) (le_iSup (fun s : T => L.conjBy s) ⟨t, ht⟩)

omit [Finite G] in
/-- Relative component membership is preserved by conjugation inside H. -/
theorem conjugate_component (hL : L ∈ cComponentsIn H) {t : G} (ht : t ∈ H) :
    L.conjBy t ∈ cComponentsIn H := by
  have hle : L.conjBy t ≤ H := by
    rintro x ⟨l, hl, rfl⟩
    exact H.mul_mem (H.mul_mem ht (hL.1 hl)) (H.inv_mem ht)
  refine ⟨hle, ?_⟩
  have hc := hL.2.map_equiv (MulAut.conj (⟨t, ht⟩ : H))
  have he : (L.subgroupOf H).map (MulAut.conj (⟨t, ht⟩ : H)).toMonoidHom =
      (L.conjBy t).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hle, map_map]
    change (L.subgroupOf H).map ((MulAut.conj t).toMonoidHom.comp H.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hL.1]
    rfl
  rwa [he] at hc

/-- The intrinsic quotient is identified with its actual image in the orbit quotient. -/
noncomputable def componentImageEquiv (h : SwappedInput 𝒦 p T X P H L)
    {B : Subgroup G} (hB : B ∈ cComponentsIn H) (hBK : B ≤ componentOrbit L T) :
    XiQuotient B ≃* SwappedSylow.imageInOrbit L T B :=
  (QuotientGroup.congr (pCore 2 B) (pCore 2 (B.subgroupOf (componentOrbit L T)))
    (subgroupOfEquivOfLe hBK).symm (pCore_map_iso 2 _)).trans
    (cComponentTwoCoreQuotientEquiv
      (hB.2.subgroupOf_of_le hBK (SwappedSylow.orbit_le_overgroup h)))

private theorem center_bot_of_perfect_simple {D : Type*} [Group D]
    [Group.IsPerfect D] [IsSimpleGroup D] : center D = ⊥ := by
  rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hz | hz
  · exact hz
  · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp hz)).elim

/-- The two quotient factors are disjoint because they commute and the first is centerless. -/
theorem quotient_factors_disjoint (h : SwappedInput 𝒦 p T X P H L)
    (hs : IsSimpleGroup (XiQuotient L)) {B : Subgroup G}
    (hc : ⁅SwappedSylow.imageInOrbit L T L, SwappedSylow.imageInOrbit L T B⁆ = ⊥) :
    Disjoint (SwappedSylow.imageInOrbit L T L) (SwappedSylow.imageInOrbit L T B) := by
  let e := componentImageEquiv h h.component (le_componentOrbit L T)
  let _ := hs
  let _ := h.quasisimple
  let _ : IsSimpleGroup (SwappedSylow.imageInOrbit L T L) := e.symm.isSimpleGroup
  let _ : Group.IsPerfect (SwappedSylow.imageInOrbit L T L) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hz := center_bot_of_perfect_simple (D := SwappedSylow.imageInOrbit L T L)
  apply disjoint_def.mpr
  intro x hx hy
  have hcenter : (⟨x, hx⟩ : SwappedSylow.imageInOrbit L T L) ∈
      center (SwappedSylow.imageInOrbit L T L) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp hc y.property x hy).symm
  rw [hz] at hcenter
  exact congrArg Subtype.val (mem_bot.mp hcenter)

/-- A.3.7 applies to the two distinct actual components in the orbit quotient. -/
theorem quotient_factors_commute
    (hA37 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B C : Subgroup D, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (h : SwappedInput 𝒦 p T X P H L) {t : G}
    (ht : t ∈ T) (hm : t ∉ normalizer L) :
    ⁅SwappedSylow.imageInOrbit L T L, SwappedSylow.imageInOrbit L T (L.conjBy t)⁆ = ⊥ := by
  let K := componentOrbit L T
  let A := L.subgroupOf K
  let B := (L.conjBy t).subgroupOf K
  have hLK : L ≤ K := le_componentOrbit L T
  have htH : t ∈ H := (le_sup_right.trans h.overgroup) ht
  have hBK : L.conjBy t ≤ K := le_iSup (fun s : T => L.conjBy s) ⟨t, ht⟩
  have hA : A.IsCComponent :=
    h.component.2.subgroupOf_of_le hLK (SwappedSylow.orbit_le_overgroup h)
  have hB : B.IsCComponent :=
    (conjugate_component h.component htH).2.subgroupOf_of_le hBK
      (SwappedSylow.orbit_le_overgroup h)
  let _ := pCore_isNilpotent (p := 2) (G := K)
  apply hA37 _ (SwappedSylow.orbit_quotient_sqtk h) (pCore_quotient_pCore_eq_bot 2)
    _ _ (hA.map_quotient _) (hB.map_quotient _)
  intro he
  have heq := hA.eq_of_map_quotient_eq hB (pCore 2 K) he
  have hh := congrArg (fun C : Subgroup K => C.map K.subtype) heq
  rw [map_subgroupOf_eq_of_le hLK, map_subgroupOf_eq_of_le hBK] at hh
  exact hm (mem_normalizer_iff_map_conj_eq.mpr hh.symm)

/-- Multiplication of the actual conjugate quotient factors gives coordinates
on K/O₂(K). The evaluation formula remembers both factor inclusions. -/
theorem quotient_product_coordinates
    (hA37 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B C : Subgroup D, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (h : SwappedInput 𝒦 p T X P H L)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2)
    (hs : IsSimpleGroup (XiQuotient L)) {t : G}
    (ht : t ∈ T) (hm : t ∉ normalizer L) :
    ∃ e : SwappedSylow.imageInOrbit L T L ×
        SwappedSylow.imageInOrbit L T (L.conjBy t) ≃* XiQuotient (componentOrbit L T),
      ∀ a b, e (a, b) = (a : XiQuotient (componentOrbit L T)) * b := by
  have hc := quotient_factors_commute hA37 h ht hm
  have hd := quotient_factors_disjoint h hs hc
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hgen : SwappedSylow.imageInOrbit L T L ⊔
      SwappedSylow.imageInOrbit L T (L.conjBy t) = ⊤ := by
    unfold SwappedSylow.imageInOrbit
    rw [← Subgroup.map_sup]
    have hBK : L.conjBy t ≤ componentOrbit L T := le_iSup (fun s : T => L.conjBy s) ⟨t, ht⟩
    rw [← subgroupOf_sup (le_componentOrbit L T) hBK, ← orbit_eq_sup h hi ht hm,
      subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  exact ⟨e.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv), he⟩

/-- The orbit quotient is the product of two copies of the intrinsic component
quotient, via the two actual component inclusions and conjugation by t. -/
theorem quotient_product
    (hA37 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B C : Subgroup D, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (h : SwappedInput 𝒦 p T X P H L)
    (hi : (normalizer (L.subgroupOf H : Set H)).index = 2)
    (hs : IsSimpleGroup (XiQuotient L)) :
    Nonempty (XiQuotient (componentOrbit L T) ≃* XiQuotient L × XiQuotient L) := by
  obtain ⟨t, ht, hm⟩ := h.exists_swap
  obtain ⟨e, _⟩ := quotient_product_coordinates hA37 h hi hs ht.1 hm
  let a := componentImageEquiv h h.component (le_componentOrbit L T)
  let c : L ≃* L.conjBy t := equivMapOfInjective L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let cq : XiQuotient L ≃* XiQuotient (L.conjBy t) :=
    QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let b := cq.trans (componentImageEquiv h
    (conjugate_component h.component ((le_sup_right.trans h.overgroup) ht.1))
    (le_iSup (fun s : T => L.conjBy s) ⟨t, ht.1⟩))
  exact ⟨e.symm.trans (MulEquiv.prodCongr a.symm b.symm)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedFactorsProof
