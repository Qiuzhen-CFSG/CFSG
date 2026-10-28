module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup
public import Theory.Representation.BinaryPermutation.FiveCentralizerSpan

/-!
# The actual three-point intersection in Vᵥ

An A₅ marking transports the coordinate hyperplane to the literal span of
z under O²(C_L(v)). The residual cubic supplies all three generators;
the whole stabilizer of v preserves the hyperplane, which gives the reverse
containment. Earlier 13.2.6(2), expressed as fusion control on actual group
elements, identifies its three displayed points with zᴳ ∩ Vᵥ. Their product
is v, so every normalizer of Vᵥ centralizes v.

No flag-compatible marking is assumed to exist here; its construction belongs
to the configuration. The fusion input is an earlier source theorem, not an
assumption about the desired three-point intersection or its normalizer.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.926,
928, and 13.2.6(2) on p.879.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace A5Module
open BinaryPermutation.FiveCentralizerGeometry Subgroup
open scoped IsMulCommutative BigOperators
variable {G : Type*} [Group G] {L V : Subgroup G} (s : Marking L V)

theorem map_mem (x : Multiplicative Space) : s.map x ∈ V :=
  s.range_eq.le ⟨x, rfl⟩

include s in
theorem module_abelian : IsMulCommutative V := by
  rw [← s.range_eq]
  infer_instance

theorem stabilizer_fixes_v (c : ↥(L ⊓ Gv (markedV s))) :
    act (s.action (inclusion inf_le_left c)) v = v := by
  apply Multiplicative.ofAdd.injective
  apply s.injective
  rw [← s.equivariant]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property.2)

theorem residual_normalizes_plane :
    Lv L (markedV s) ≤ normalizer ((SpanGeometry.plane.map s.map : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  rintro c ⟨d, hd, rfl⟩ x ⟨y, hy, rfl⟩
  refine ⟨Multiplicative.ofAdd
    (act (s.action (inclusion inf_le_left d)) y.toAdd),
    SpanGeometry.plane_invariant _ (stabilizer_fixes_v s d) y hy, ?_⟩
  exact (s.equivariant (inclusion inf_le_left d) y.toAdd).symm

theorem Vv_le_plane : Vv L (markedZ s) (markedV s) ≤ SpanGeometry.plane.map s.map := by
  apply conjugateSpanBy_le _ (residual_normalizes_plane s)
  exact zpowers_le.mpr ⟨Multiplicative.ofAdd z, SpanGeometry.points_mem 0, rfl⟩

theorem Vv_le_module : Vv L (markedZ s) (markedV s) ≤ V := by
  apply (Vv_le_plane s).trans
  rintro x ⟨y, _, rfl⟩
  exact map_mem s y

theorem span_abelian : IsMulCommutative (Vv L (markedZ s) (markedV s)) := by
  let := module_abelian s
  exact .of_setLike_mul_comm fun _ hx _ hy =>
    setLike_mul_comm (Vv_le_module s hx) (Vv_le_module s hy)

variable [Finite G]

theorem point_mem_Vv (i : Fin 3) :
    s.map (Multiplicative.ofAdd (SpanGeometry.point i)) ∈ Vv L (markedZ s) (markedV s) := by
  obtain ⟨c, hc, he⟩ := exists_residual_cubic s
  have hconj (d : ↥(L ⊓ Gv (markedV s))) (hd : d ∈ pResidual 2 ↥(L ⊓ Gv (markedV s))) :
      s.map (Multiplicative.ofAdd (act (s.action (inclusion inf_le_left d)) z)) ∈
        Vv L (markedZ s) (markedV s) := by
    rw [← s.equivariant]
    exact subset_closure ⟨d, ⟨d, hd, rfl⟩, markedZ s, mem_zpowers _, rfl⟩
  fin_cases i
  · exact z_mem_Vv L (markedZ s) (markedV s)
  · change s.map (Multiplicative.ofAdd (act cubic z)) ∈ _
    simpa only [he] using hconj c hc
  · change s.map (Multiplicative.ofAdd (act (cubic ^ 2) z)) ∈ _
    have hpow := (pResidual 2 ↥(L ⊓ Gv (markedV s))).pow_mem hc 2
    simpa only [map_pow, he] using hconj (c ^ 2) hpow

/-- The ambient conjugate span is the marked eight-element hyperplane. -/
theorem Vv_eq_plane : Vv L (markedZ s) (markedV s) = SpanGeometry.plane.map s.map := by
  apply le_antisymm (Vv_le_plane s)
  rintro x ⟨y, hy, rfl⟩
  have hp := point_mem_Vv s
  rcases SpanGeometry.plane_cases y.toAdd hy with h | h | h | h | h | h | h | h
  · have he : y = 1 := h
    rw [he, map_one]
    exact one_mem _
  · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
    rw [h]
    exact hp 0
  · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
    rw [h]
    exact hp 1
  · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
    rw [h]
    exact hp 2
  · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
    rw [h, ofAdd_add, map_mul]
    exact mul_mem (hp 0) (hp 1)
  · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
    rw [h, ofAdd_add, map_mul]
    exact mul_mem (hp 0) (hp 2)
  · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
    rw [h, ofAdd_add, map_mul]
    exact mul_mem (hp 1) (hp 2)
  · change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
    rw [h]
    exact markedV_mem_Vv s

/-- The actual span has order eight, with no kernel lost in transport. -/
theorem Vv_card : Nat.card (Vv L (markedZ s) (markedV s)) = 8 := by
  rw [Vv_eq_plane s, Subgroup.card_map_of_injective s.injective]
  exact SpanGeometry.plane_card

def singularPoint (i : Fin 3) : Vv L (markedZ s) (markedV s) :=
  ⟨s.map (Multiplicative.ofAdd (SpanGeometry.point i)), point_mem_Vv s i⟩

theorem singularPoint_injective : Function.Injective (singularPoint s) := by
  intro i j h
  apply SpanGeometry.point_injective
  exact s.injective (congrArg Subtype.val h)

def singularPoints : Finset (Vv L (markedZ s) (markedV s)) :=
  Finset.univ.map ⟨singularPoint s, singularPoint_injective s⟩

theorem singularPoints_card : (singularPoints s).card = 3 := by
  rw [singularPoints, Finset.card_map, Finset.card_univ]
  rfl

/-- The exact earlier 13.2.6(2) input, specialized to the involution z.
The entire conjugacy statement concerns actual elements of G and L. -/
def ControlsFusionOfZ : Prop :=
  ∀ x ∈ V, (∃ c : G, MulAut.conj c (markedZ s) = x) →
    ∃ l : L, MulAut.conj (l : G) (markedZ s) = x

theorem singularPoint_conjugate (i : Fin 3) :
    ∃ c : G, MulAut.conj c (markedZ s) = (singularPoint s i : G) := by
  obtain ⟨d, hd⟩ := s.onto (cubic ^ i.val)
  refine ⟨d, ?_⟩
  change MulAut.conj (d : G) (s.map (Multiplicative.ofAdd z)) = _
  rw [s.equivariant, hd]
  fin_cases i <;> rfl

/-- The three displayed points are exactly zᴳ ∩ Vᵥ, using earlier fusion control. -/
theorem mem_singularPoints_iff (hfusion : ControlsFusionOfZ s)
    (x : Vv L (markedZ s) (markedV s)) :
    x ∈ singularPoints s ↔ ∃ c : G, MulAut.conj c (markedZ s) = (x : G) := by
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact singularPoint_conjugate s i
  · intro hx
    obtain ⟨l, hl⟩ := hfusion x (Vv_le_module s x.property) hx
    have hm := (Vv_le_plane s) x.property
    obtain ⟨y, hy, hxy⟩ := hm
    have he : act (s.action l) z = y.toAdd := by
      apply Multiplicative.ofAdd.injective
      apply s.injective
      exact (s.equivariant l z).symm.trans (hl.trans hxy.symm)
    obtain ⟨i, hi⟩ := SpanGeometry.orbit_in_plane (s.action l) (he.symm ▸ hy)
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_univ _, Subtype.ext ?_⟩
    change s.map (Multiplicative.ofAdd (SpanGeometry.point i)) = (x : G)
    rw [← hi]
    exact (s.equivariant l z).symm.trans hl

/-- The product in the actual ambient group is v. -/
theorem singularPoints_product :
    let := span_abelian s
    ((∏ x ∈ singularPoints s, x : Vv L (markedZ s) (markedV s)) : G) = markedV s := by
  dsimp only
  let := span_abelian s
  rw [singularPoints, Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk, Fin.prod_univ_three]
  change s.map (Multiplicative.ofAdd (SpanGeometry.point 0)) *
    s.map (Multiplicative.ofAdd (SpanGeometry.point 1)) *
      s.map (Multiplicative.ofAdd (SpanGeometry.point 2)) = _
  rw [← map_mul, ← map_mul]
  exact congrArg (fun x : Space => s.map (Multiplicative.ofAdd x)) SpanGeometry.points_sum

/-- The normalizer reduction preceding 13.6.8, with the intersection and
its product constructed from the actual module and earlier fusion theorem. -/
theorem normalizer_Vv_le_Gv_of_fusion (hfusion : ControlsFusionOfZ s) :
    normalizer (Vv L (markedZ s) (markedV s) : Set G) ≤ Gv (markedV s) := by
  let := span_abelian s
  exact normalizer_Vv_le_Gv L (markedZ s) (markedV s) (singularPoints s)
    (mem_singularPoints_iff s hfusion) (singularPoints_product s)
end A5Module
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
