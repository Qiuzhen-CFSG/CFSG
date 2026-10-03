module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Sylow

/-!
# The intrinsic Sylow hypothesis in Lyons's characterization

Theorem 2 of Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), p. 372, assumes a Sylow subgroup of order 64 whose center, derived
subgroup, Frattini subgroup, first omega subgroup, and square-generated
subgroup coincide and are elementary abelian of order four.  The interface
below uses the actual subgroup operations, including the square-generated
subgroup.  It imposes no hypothesis on local odd cores or local solvability.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- Exactly the intrinsic Sylow assumptions of Lyons's Theorem 2. -/
public structure SylowStructure {G : Type*} [Group G] (S : Sylow 2 G) : Prop where
  card : Nat.card S = 64
  center_eq_commutator : Subgroup.center S = commutator S
  center_eq_frattini : Subgroup.center S = frattini S
  center_eq_omega : Subgroup.center S = omega₁ S (p := 2)
  center_eq_squares : Subgroup.center S =
    Subgroup.closure (Set.range fun s : S => s ^ 2)
  center_card : Nat.card (Subgroup.center S) = 4
  center_elementary : IsElementaryAbelian 2 (Subgroup.center S)

/-- The center of the supplied Sylow subgroup, mapped into the ambient group. -/
@[expose] public def centerImage {G : Type*} [Group G] (S : Sylow 2 G) : Subgroup G :=
  (Subgroup.center S).map (S : Subgroup G).subtype

public theorem centerImage_le {G : Type*} [Group G] (S : Sylow 2 G) :
    centerImage S ≤ (S : Subgroup G) := Subgroup.map_subtype_le _

public theorem centerImage_card {G : Type*} [Group G] (S : Sylow 2 G)
    (h : SylowStructure S) : Nat.card (centerImage S) = 4 := by
  rw [centerImage, Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective]
  exact h.center_card

public theorem centerImage_elementary {G : Type*} [Group G] (S : Sylow 2 G)
    (h : SylowStructure S) : IsElementaryAbelian 2 (centerImage S) := by
  let _ := h.center_elementary
  exact IsElementaryAbelian.map (p := 2) (S : Subgroup G).subtype

public theorem involution_mem_centerImage {G : Type*} [Group G] (S : Sylow 2 G)
    (h : SylowStructure S) {x : G} (hx : x ∈ (S : Subgroup G)) (hx2 : x ^ 2 = 1) :
    x ∈ centerImage S := by
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [h.center_eq_omega]
  apply Subgroup.subset_closure
  change (⟨x, hx⟩ : S) ^ (2 ^ 1) = 1
  apply Subtype.ext
  simpa using hx2

public theorem sylow_le_centralizer_centerImage {G : Type*} [Group G] (S : Sylow 2 G) :
    (S : Subgroup G) ≤ Subgroup.centralizer (centerImage S : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  rintro z ⟨t, ht, rfl⟩
  exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp ht) ⟨s, hs⟩)).symm

public theorem centerImage_ne_bot {G : Type*} [Group G] (S : Sylow 2 G)
    (h : SylowStructure S) : centerImage S ≠ ⊥ := by
  intro heq
  have hc := centerImage_card S h
  rw [heq, Subgroup.card_bot] at hc
  omega

public theorem normalizer_centerImage_ne_top {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (S : Sylow 2 G) (h : SylowStructure S) :
    Subgroup.normalizer (centerImage S : Set G) ≠ ⊤ := by
  intro htop
  have hnormal : (centerImage S).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (centerImage S) hnormal with hbot | htop
  · exact centerImage_ne_bot S h hbot
  · have hcardG : Nat.card G = 4 := by
      simpa [htop] using centerImage_card S h
    have hle := Nat.card_le_card_of_injective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
    rw [h.card, hcardG] at hle
    omega

/-- All elements of square one in the center normalizer already lie in the center.
Conjugate their cyclic two-subgroups into the supplied Sylow inside that normalizer. -/
public theorem square_one_mem_centerImage_of_mem_normalizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (h : SylowStructure S)
    {x : G} (hx : x ∈ Subgroup.normalizer (centerImage S : Set G)) (hx2 : x ^ 2 = 1) :
    x ∈ centerImage S := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := centerImage S
  let N := Subgroup.normalizer (Z : Set G)
  have hSN : (S : Subgroup G) ≤ N :=
    (sylow_le_centralizer_centerImage S).trans (Subgroup.centralizer_le_normalizer _)
  let xN : N := ⟨x, hx⟩
  have hxN2 : xN ^ 2 = 1 := Subtype.ext hx2
  have hxp : IsPGroup 2 (Subgroup.zpowers xN) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hxN2)
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N P (S.subtype hSN)
  have hxP : xN ∈ (P : Subgroup N) := hP (Subgroup.mem_zpowers _)
  have hconjS : (n : G) * x * (n : G)⁻¹ ∈ (S : Subgroup G) := by
    have ht : n * xN * n⁻¹ ∈ (S.subtype hSN : Subgroup N) := by
      rw [← hn]
      exact Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hxP
    exact ht
  have hconjZ : (n : G) * x * (n : G)⁻¹ ∈ Z :=
    involution_mem_centerImage S h hconjS (by
      simpa only [map_pow, map_one, MulAut.conj_apply] using congrArg (MulAut.conj (n : G)) hx2)
  exact ((Subgroup.mem_normalizer_iff.mp n.property) x).mpr hconjZ

/-- Normalizing the Sylow subgroup preserves its ambient center. -/
public theorem normalizer_sylow_le_normalizer_centerImage
    {G : Type*} [Group G] (S : Sylow 2 G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (centerImage S : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨s, hs, rfl⟩ := hx
  let a := Subgroup.normalizerMonoidHom (S : Subgroup G) ⟨g, hg⟩
  have hfix := (inferInstance : (Subgroup.center S).Characteristic).fixed a
  have ha : a s ∈ Subgroup.center S := by
    change s ∈ (Subgroup.center S).comap a.toMonoidHom
    rw [hfix]
    exact hs
  exact ⟨a s, ha, rfl⟩

end Stellmacher.Recognition.LyonsU3Four
