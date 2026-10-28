module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPlaneAction
public import Theory.GroupTheory.OddSubsetTranslation

/-!
# The plane normalizer inside the graph centralizer

Root transitivity prevents either normalizer from fixing the graph
involution: multiplication by that involution would preserve an odd root
class. For the plane normalizer, the endpoint centralizer of order 96 and
its Sylow overgroup of order 64 force their common containing graph
centralizer to have order 192. The endpoint therefore has index two,
which proves that R normalizes E₂.

Source: Aschbacher--Smith F.5.4(3), printed p.301.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)
include hf

/-- An odd transitive root class prevents the whole normalizer from fixing f. -/
theorem normalizer_not_le_graph_centralizer (b : Bool)
    (ht : ∀ x ∈ A c i b, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z) = x) :
    ¬ normalizer (A c i b : Set G) ≤ C c i := by
  intro hNC
  let := hf.A_elementary b
  let S : Set (A c i b) := {x | IsConj (rootElement c i z) x.val}
  let f : A c i b := ⟨Source.graphElement c i,graph_mem_A c i z t hf b⟩
  have hodd : Odd (Nat.card S) := by
    change Odd (Nat.card (classIntersection (rootElement c i z) (A c i b)))
    cases b <;> simp only [hf.root_class_A_point,hf.root_class_A_plane] <;> decide
  have hS : ∀ x ∈ S, f*x ∈ S := by
    intro x hx
    obtain ⟨n,hN,he⟩ := ht x.val x.property hx
    have hnf : MulAut.conj n (Source.graphElement c i) = Source.graphElement c i := by
      change n * Source.graphElement c i * n⁻¹ = Source.graphElement c i
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hNC hN))
    change IsConj (rootElement c i z) (Source.graphElement c i * x.val)
    have hc := hf.root_fuses_graph_root.trans
      (isConj_iff.mpr ⟨n,rfl⟩ : IsConj
        (Source.graphElement c i * rootElement c i z)
        (MulAut.conj n (Source.graphElement c i * rootElement c i z)))
    simpa only [map_mul,hnf,he] using hc
  have hf1 := eq_one_of_involution_preserves_odd_subset S f
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (A c i b)) f) hodd hS
  have hfo : Source.graphElement c i = 1 := congrArg Subtype.val hf1
  obtain ⟨g,hg⟩ := isConj_iff.mp hf.graph_fuses_t
  rw [hfo,mul_one,mul_inv_cancel] at hg
  have ho := hf.t_order
  rw [←hg,orderOf_one] at ho
  omega

omit [Finite G] in
/-- The order of a literal normalizer is sixteen times its quotient order. -/
theorem normalizer_card_eq_sixteen_mul (b : Bool) :
    Nat.card (normalizer (A c i b : Set G)) =
      16 * Nat.card (normalizerQuotient c i b) := by
  have hh := ((A c i b).subgroupOf (normalizer (A c i b : Set G))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (A c i b).le_normalizer).toEquiv,hf.A_card] at hh
  exact hh.symm

/-- The plane normalizer in C_G(f) has order 192. -/
theorem normalizer_plane_graph_centralizer_card (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (ht : ∀ x ∈ A c i true, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i true : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t) :
    Nat.card (normalizer (A c i true : Set G) ⊓ C c i : Subgroup G) = 192 := by
  let N := normalizer (A c i true : Set G)
  let L := N ⊓ C c i
  have hE : E c i true ≤ L := le_inf (E_le_normalizer_A c i true) inf_le_right
  have hRL : Rimage c i R ≤ L := le_inf
    (normalizer_R_normalizes_A c i z t hf R hR true) (Rimage_le_C c i R)
  have h96 := card_dvd_of_le hE
  have h64 := card_dvd_of_le hRL
  rw [normalizer_E_card c i z t hf] at h96
  rw [normalizer_R_card c i z t hf] at h64
  have h192 : 192 ∣ Nat.card L := by
    have hh := Nat.lcm_dvd h96 h64
    norm_num at hh
    exact hh
  have hN : Nat.card N = 576 := by
    rw [normalizer_card_eq_sixteen_mul c i z t hf true,
      normalizer_plane_quotient_card_of_transitive c i z t hf ht hl]
  have hd : Nat.card L ∣ 576 := hN ▸ card_dvd_of_le (show L ≤ N from inf_le_left)
  obtain ⟨k,hk⟩ := h192
  have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 192)
    (by simpa only [hk] using hd)
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with hk1 | hk3
  · change Nat.card L = 192
    simpa only [hk1,mul_one] using hk
  · have he : L = N := eq_of_le_of_card_ge inf_le_left (by rw [hN,hk,hk3])
    exact (normalizer_not_le_graph_centralizer c i z t hf true ht
      (show N ≤ C c i by rw [←he]; exact inf_le_right)).elim

/-- F.5.4(3), plane endpoint: R normalizes the original E₂. -/
theorem normalizer_R_normalizes_E_plane (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (ht : ∀ x ∈ A c i true, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i true : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t) :
    Rimage c i R ≤ normalizer (E c i true : Set G) := by
  let L := normalizer (A c i true : Set G) ⊓ C c i
  have hE : E c i true ≤ L := le_inf (E_le_normalizer_A c i true) inf_le_right
  have hcard := normalizer_plane_graph_centralizer_card c i z t hf R hR ht hl
  have hnormal : ((E c i true).subgroupOf L).Normal := normal_of_index_eq_two (by
    have hh := ((E c i true).subgroupOf L).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv,
      normalizer_E_card c i z t hf,hcard] at hh
    omega)
  exact (le_inf (normalizer_R_normalizes_A c i z t hf R hR true) (Rimage_le_C c i R)).trans
    ((normal_subgroupOf_iff_le_normalizer hE).mp hnormal)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
