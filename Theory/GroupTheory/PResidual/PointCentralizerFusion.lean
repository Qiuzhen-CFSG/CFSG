module
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.SubgroupAutomorphismImages
/-!
# Fusion and centralizers of point-centralizer residuals

An element centralizing Oᵖ(C_G(f)) contains that p-perfect subgroup in
Oᵖ(C_G(x)). If x is conjugate to f, equal finite orders force equality.
When C_{C_G(f)}(Oᵖ(C_G(f))) is abelian, the same containment and cardinality
argument identifies its analogue at x. Returning conjugators therefore
normalize the whole residual centralizer whenever all its nonidentity
elements are conjugate to f.

Source application: Aschbacher–Smith F.5.5, printed p.302.
-/
@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
def pointCentralizerResidual (p : ℕ) (x : G) : Subgroup G :=
  (pResidual p (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype

def pointResidualCentralizer (p : ℕ) (x : G) : Subgroup G :=
  centralizer ({x} : Set G) ⊓ centralizer (pointCentralizerResidual p x : Set G)

omit [Finite G] in
private theorem centralizer_map_equiv (e : G ≃* G) (s : Set G) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using hx (e y) ⟨y,hy,rfl⟩

theorem pointCentralizerResidual_map (p : ℕ) (x : G) (e : G ≃* G) :
    (pointCentralizerResidual p x).map e.toMonoidHom = pointCentralizerResidual p (e x) := by
  rw [pointCentralizerResidual,map_embedded_pResidual,centralizer_map_equiv,Set.image_singleton]
  rfl

theorem pointResidualCentralizer_map (p : ℕ) (x : G) (e : G ≃* G) :
    (pointResidualCentralizer p x).map e.toMonoidHom = pointResidualCentralizer p (e x) := by
  rw [pointResidualCentralizer,map_inf _ _ e.toMonoidHom e.injective,
    centralizer_map_equiv,Set.image_singleton,centralizer_map_equiv]
  change _ ⊓ centralizer (((pointCentralizerResidual p x).map e.toMonoidHom) : Set G) = _
  rw [pointCentralizerResidual_map]
  rfl

theorem pointCentralizerResidual_eq_of_conjugate_mem (p : ℕ) (f x : G)
    (hx : x ∈ pointResidualCentralizer p f) (hc : IsConj f x) :
    pointCentralizerResidual p x = pointCentralizerResidual p f := by
  have hle : pointCentralizerResidual p f ≤ centralizer ({x} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hx.2 a ha)
  have hperf : IsPPerfect p (pointCentralizerResidual p f) :=
    isPPerfect_embedded_pResidual p (centralizer ({f} : Set G))
  have hres := embedded_pResidual_mono p hle
  rw [(pResidual_eq_top_iff p _).mpr hperf,
    ←MonoidHom.range_eq_map,range_subtype] at hres
  apply (eq_of_le_of_card_ge hres ?_).symm
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have he := pointCentralizerResidual_map p f (MulAut.conj g)
  change (pointCentralizerResidual p f).map (MulAut.conj g).toMonoidHom =
    pointCentralizerResidual p (g*f*g⁻¹) at he
  rw [hg] at he
  change Nat.card (pointCentralizerResidual p x) ≤ Nat.card (pointCentralizerResidual p f)
  rw [←he,card_map_of_injective (MulAut.conj g).injective]

theorem pointResidualCentralizer_eq_of_conjugate_mem (p : ℕ) (f x : G)
    [IsMulCommutative (pointResidualCentralizer p f)]
    (hx : x ∈ pointResidualCentralizer p f) (hc : IsConj f x) :
    pointResidualCentralizer p x = pointResidualCentralizer p f := by
  have hres := pointCentralizerResidual_eq_of_conjugate_mem p f x hx hc
  have hle : pointResidualCentralizer p f ≤ pointResidualCentralizer p x := by
    intro a ha
    refine ⟨?_,?_⟩
    · exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨a,ha⟩ : pointResidualCentralizer p f) ⟨x,hx⟩))
    · rw [hres]
      exact ha.2
  apply (eq_of_le_of_card_ge hle ?_).symm
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have he := pointResidualCentralizer_map p f (MulAut.conj g)
  change (pointResidualCentralizer p f).map (MulAut.conj g).toMonoidHom =
    pointResidualCentralizer p (g*f*g⁻¹) at he
  rw [hg] at he
  rw [←he,card_map_of_injective (MulAut.conj g).injective]

theorem pointResidualCentralizer_conjugator_mem_normalizer (p : ℕ) (f : G)
    [IsMulCommutative (pointResidualCentralizer p f)]
    (hf : ∀x∈pointResidualCentralizer p f, x≠1 → IsConj f x)
    (g x : G) (hx : x∈pointResidualCentralizer p f) (hx1 : x≠1)
    (hgx : g*x*g⁻¹∈pointResidualCentralizer p f) :
    g ∈ normalizer (pointResidualCentralizer p f : Set G) := by
  have hy1 : g*x*g⁻¹≠1 := by
    intro he
    apply hx1
    exact (MulAut.conj g).injective (he.trans (map_one _).symm)
  have hxC := pointResidualCentralizer_eq_of_conjugate_mem p f x hx (hf x hx hx1)
  have hyC := pointResidualCentralizer_eq_of_conjugate_mem p f (g*x*g⁻¹) hgx (hf _ hgx hy1)
  have hmap := pointResidualCentralizer_map p x (MulAut.conj g)
  change (pointResidualCentralizer p x).map (MulAut.conj g).toMonoidHom =
    pointResidualCentralizer p (g*x*g⁻¹) at hmap
  rw [hxC,hyC] at hmap
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact hmap ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom ha
  · intro ha
    rw [←hmap] at ha
    obtain ⟨b,hb,he⟩ := ha
    exact (MulAut.conj g).injective he ▸ hb
end Subgroup
