module
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Separation
public import Theory.GroupTheory.ConjugatePairSeed.Center
public import Theory.GroupTheory.ElementaryEightPairQuaternionRecognition
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# The intrinsic quaternion pair in F.9.5(6.i)

The two original seeds generate a group whose center is exactly V₁.
Their central commutators give mutual normalization. When |V|=16 and
the seed has index two, both seeds are elementary eights; the proved
recognition theorem therefore constructs two actual quaternion factors.
Source: Aschbacher–Smith F.9.5(6.i), printed p.319.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

omit h [Finite G] in
theorem pair_seed_conjugate_le_closure (g : G) (hg : g ∈ D.H) :
    D.Vplus.map (MulAut.conj g).toMonoidHom ≤ D.UH := by
  rintro _ ⟨a,ha,rfl⟩
  exact subset_closure ⟨g,hg,a,ha,rfl⟩

/-- The source bound transfers to the second original module and seed. -/
theorem pair_conjugate_centralizer_bound
    (hc : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (g : G) (hg : g ∈ D.H) :
    ⁅D.V.map (MulAut.conj g).toMonoidHom,
      D.H ⊓ centralizer (D.Vplus.map (MulAut.conj g).toMonoidHom : Set G)⁆ ≤ D.V₁ := by
  let f := (MulAut.conj g).toMonoidHom
  have hz : D.V₁.map f = D.V₁ := mem_normalizer_iff_map_conj_eq.mp
    ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hg)
  apply commutator_le.mpr
  rintro _ ⟨a,ha,rfl⟩ x hx
  let y := (MulAut.conj g⁻¹) x
  have hyH : y ∈ D.H := by
    simpa only [y,MulAut.conj_apply,inv_inv] using
      D.H.mul_mem (D.H.mul_mem (D.H.inv_mem hg) hx.1) hg
  have hxy : f y = x := by simp [f,y,MulAut.conj_apply,mul_assoc]
  have hyC : y ∈ centralizer (D.Vplus : Set G) := by
    intro w hw
    apply (MulAut.conj g).injective
    change f (w*y) = f (y*w)
    rw [map_mul,map_mul,hxy]
    exact hx.2 _ (mem_map_of_mem f hw)
  have hm := hz.le (mem_map_of_mem f (hc (commutator_mem_commutator ha ⟨hyH,hyC⟩)))
  rw [map_commutatorElement,hxy] at hm
  exact hm

/-- The actual seed join has center precisely the original order-two point. -/
theorem pair_seed_center
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hc : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    (center (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G)).map
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom).subtype = D.V₁ := by
  let := h.elementary
  let f := (MulAut.conj g).toMonoidHom
  have hBH : D.V.map f ≤ D.H := by
    rintro _ ⟨a,ha,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.V_le_H ha)) (D.H.inv_mem hg)
  have hnE : D.Vplus.map f ≤ normalizer (D.Vplus : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono (le_conjugateSpanBy _ _)
      ((pair_seed_conjugate_le_closure (D := D) g hg).trans h.UH_le_QH)).trans
      h.commutator_UH_QH_le_point).trans h.point_lt.le
  exact center_seed_sup_eq D.H D.V (D.V.map f) D.Vplus (D.Vplus.map f) D.V₁
    h.plus_le (map_mono h.plus_le) h.V_le_H hBH h.point_lt.le
    inferInstance hnE h.H_centralizes
    (h.pair_seed_fixed_eq_point hp g hg hn)
    (h.pair_conjugate_seed_fixed_eq_point hp g hg hn) hc
    (h.pair_conjugate_centralizer_bound hc g hg)

/-- F.9.5(6.i) constructs quaternion factors in the literal pair seed group. -/
theorem pair_seed_quaternion
    (hi : D.Vplus.relIndex D.V = 2) (hcard : Nat.card D.V = 16)
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hc : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Nonempty (QuaternionCentralProductData
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G)) := by
  let := h.elementary
  let f := (MulAut.conj g).toMonoidHom
  let P := D.Vplus ⊔ D.Vplus.map f
  let C := D.Vplus.subgroupOf P
  let E := (D.Vplus.map f).subgroupOf P
  have hCP : D.Vplus ≤ P := le_sup_left
  have hEP : D.Vplus.map f ≤ P := le_sup_right
  have hseed : Nat.card D.Vplus = 8 := by
    have hh := (D.Vplus.subgroupOf D.V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe h.plus_le).toEquiv] at hh
    change Nat.card D.Vplus * D.Vplus.relIndex D.V = Nat.card D.V at hh
    rw [hi,hcard] at hh
    omega
  let : IsElementaryAbelian 2 D.Vplus := IsElementaryAbelian.of_le h.plus_le
  let : IsElementaryAbelian 2 (D.Vplus.map f) := IsElementaryAbelian.map f
  have hC : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hCP
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hEP
  have hCc : Nat.card C = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv).trans hseed
  have hEc : Nat.card E = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv,
      card_map_of_injective (MulAut.conj g).injective,hseed]
  have hgen : C ⊔ E = ⊤ := by
    rw [←subgroupOf_sup hCP hEP]
    exact subgroupOf_self P
  have hnC : C ≤ normalizer (E : Set P) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply commutator_le.mpr
    intro c hc' e he'
    have hh : ⁅(c:G),(e:G)⁆ ∈ D.V₁ := h.commutator_UH_QH_le_point
      (commutator_mem_commutator
        (le_conjugateSpanBy D.Vplus D.H hc')
        (h.UH_le_QH (pair_seed_conjugate_le_closure (D := D) g hg he')))
    have hz : D.V₁.map f = D.V₁ := mem_normalizer_iff_map_conj_eq.mp
      ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hg)
    exact (hz.symm.le.trans (map_mono h.point_lt.le)) hh
  have hcenter : Nat.card (center P) = 2 := by
    rw [←card_map_of_injective P.subtype_injective,
      h.pair_seed_center hp hc g hg hn,h.point_card]
  obtain ⟨A,B,hA,hB,hgen,hint,hcomm⟩ := exists_quaternion_factors_of_elementary_eights
    C E hC hE hCc hEc hgen hnC hcenter
  exact ⟨⟨A,B,hA,hB,hint,hcomm,hgen⟩⟩
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
