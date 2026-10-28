module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerGraphCentralizer
public import Theory.GroupAction.SymmetricFiveSixteenOrbits

/-!
# The point normalizer inside the graph centralizer

The faithful S₅ action on A₁ has five roots and ten other nonidentity
vectors. The graph involution belongs to the ten-orbit, so its stabilizer
in N_G(A₁) has order 192. The original E₁ has index two in this stabilizer;
the Sylow overgroup R therefore normalizes E₁.

Source: Aschbacher--Smith F.5.4(3--4), printed p.301.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)
include hf

/-- The point normalizer in C_G(f) has order 192. -/
theorem normalizer_point_graph_centralizer_card (hs : Source.Hypotheses c i z)
    (ht : ∀ x ∈ A c i false, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i false : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G) = 384) :
    Nat.card (normalizer (A c i false : Set G) ⊓ C c i : Subgroup G) = 192 := by
  let N := normalizer (A c i false : Set G)
  let q := QuotientGroup.mk' ((A c i false).subgroupOf N)
  let ρ := normalizerCoreAction c i z t hf false
  obtain ⟨e⟩ := normalizer_point_quotient_of_transitive c i z t hf hs ht hl
  let a := ρ.comp e.symm.toMonoidHom
  let S : Set (A c i false) := {x | IsConj (rootElement c i z) x.val}
  let f : A c i false := ⟨Source.graphElement c i,graph_mem_A c i z t hf false⟩
  let := hf.A_elementary false
  let := conjMulDistribMulActionOfLeNormalizer N (A c i false) le_rfl
  have h1 : (1 : A c i false) ∉ S := by
    intro hh
    change IsConj (rootElement c i z) 1 at hh
    have hz : rootElement c i z = 1 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hh
      apply (MulAut.conj g).injective
      exact hg.trans (map_one _).symm
    have ho := source_root_order c i z hs
    rw [hz,orderOf_one] at ho
    omega
  have hinv (g : Equiv.Perm (Fin 5)) (x : A c i false) (hx : x ∈ S) : a g x ∈ S := by
    obtain ⟨n,hnq⟩ := QuotientGroup.mk'_surjective ((A c i false).subgroupOf N) (e.symm g)
    change IsConj (rootElement c i z) (ρ (e.symm g) x).val
    rw [←hnq]
    exact hx.trans (isConj_iff.mpr ⟨n.val,rfl⟩)
  have hf1 : f ≠ 1 := by
    intro he
    have hh : Source.graphElement c i = 1 := congrArg Subtype.val he
    obtain ⟨g,hg⟩ := isConj_iff.mp hf.graph_fuses_t
    rw [hh,mul_one,mul_inv_cancel] at hg
    have ho := hf.t_order
    rw [←hg,orderOf_one] at ho
    omega
  have hfS : f ∉ S := fun hh => Source.graph_not_conjugate_root c i z hs hh.symm
  have hc := Theory.GroupAction.symmetric_five_sixteen_complement_orbit
    (hf.A_card false) a
    ((normalizerCoreAction_injective c i z t hf false).comp e.symm.injective)
    S hf.root_class_A_point h1 hinv f hf1 hfS
  have hr : Set.range (fun g => a g f) = MulAction.orbit N f := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      obtain ⟨n,hnq⟩ := QuotientGroup.mk'_surjective ((A c i false).subgroupOf N) (e.symm g)
      refine ⟨n,?_⟩
      change ρ (q n) f = ρ (e.symm g) f
      rw [hnq]
    · rintro ⟨n,rfl⟩
      refine ⟨e (q n),?_⟩
      change ρ (e.symm (e (q n))) f = ρ (q n) f
      rw [e.symm_apply_apply]
  have hstab : MulAction.stabilizer N f = (N ⊓ C c i).subgroupOf N := by
    ext n
    change n • f = f ↔ n.val ∈ N ⊓ C c i
    constructor
    · intro he
      refine ⟨n.property,mem_centralizer_singleton_iff.mpr ?_⟩
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
    · intro he
      apply Subtype.ext
      change n.val * Source.graphElement c i * n.val⁻¹ = Source.graphElement c i
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp he.2)
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N f)
  rw [Nat.card_prod,←hr,hstab,
    Nat.card_congr (subgroupOfEquivOfLe (show N ⊓ C c i ≤ N from inf_le_left)).toEquiv] at hh
  change (Set.range (fun g => a g f)).ncard * Nat.card (N ⊓ C c i : Subgroup G) = Nat.card N at hh
  rw [hc,normalizer_card_eq_sixteen_mul c i z t hf false,
    normalizer_point_quotient_card_of_transitive c i z t hf ht hl] at hh
  change 10 * Nat.card (normalizer (A c i false : Set G) ⊓ C c i : Subgroup G) = 16 * 120 at hh
  omega

/-- F.5.4(3), point endpoint: R normalizes the original E₁. -/
theorem normalizer_R_normalizes_E_point (hs : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (ht : ∀ x ∈ A c i false, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i false : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G) = 384) :
    Rimage c i R ≤ normalizer (E c i false : Set G) := by
  let L := normalizer (A c i false : Set G) ⊓ C c i
  have hE : E c i false ≤ L := le_inf (E_le_normalizer_A c i false) inf_le_right
  have hcard := normalizer_point_graph_centralizer_card c i z t hf hs ht hl
  have hnormal : ((E c i false).subgroupOf L).Normal := normal_of_index_eq_two (by
    have hh := ((E c i false).subgroupOf L).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv,
      normalizer_E_card c i z t hf,hcard] at hh
    omega)
  exact (le_inf (normalizer_R_normalizes_A c i z t hf R hR false) (Rimage_le_C c i R)).trans
    ((normal_subgroupOf_iff_le_normalizer hE).mp hnormal)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
