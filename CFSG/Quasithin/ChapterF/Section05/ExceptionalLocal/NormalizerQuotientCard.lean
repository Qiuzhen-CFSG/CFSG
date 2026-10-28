module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerFusion
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPointAction
public import Theory.GroupTheory.NormalizerClassOrbitCard

/-!
# Orders of the two original normalizer quotients

The proved root-transitivity theorem and the endpoint stabilizers give
orders 120 and 36 for N_G(A₁)/A₁ and N_G(A₂)/A₂. The existing faithful
five-root permutation action then identifies the first literal quotient
with S₅. Only the finite endpoint stabilizer calculations remain explicit.

Source: Aschbacher--Smith F.5.4(4), printed p.301.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)

omit [Finite G] in
include hf in
/-- Orbit-stabilizer for the original normalizer quotient, with literal
intersection in the first endpoint. -/
theorem normalizer_quotient_card_of_root_transitive (b : Bool)
    (ht : ∀ x ∈ A c i b, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z) = x) :
    16 * Nat.card (normalizerQuotient c i b) =
      Nat.card (classIntersection (rootElement c i z) (A c i b)) *
        Nat.card (M c i false ⊓ normalizer (A c i b : Set G) : Subgroup G) := by
  have ho := card_normalizer_of_class_transitive (A c i b) (rootElement c i z)
    (hf.root_mem_A b) ht
  rw [hf.root_centralizer,inf_comm] at ho
  have hc := ((A c i b).subgroupOf (normalizer (A c i b : Set G))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (A c i b).le_normalizer).toEquiv,hf.A_card] at hc
  exact hc.trans ho.symm

omit [Finite G] in
include hf in
/-- The point quotient has order 120 once its original root stabilizer has
the source order 384. -/
theorem normalizer_point_quotient_card_of_transitive
    (ht : ∀ x ∈ A c i false, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i false : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G) = 384) :
    Nat.card (normalizerQuotient c i false) = 120 := by
  have hh := normalizer_quotient_card_of_root_transitive c i z t hf false ht
  rw [hf.root_class_A_point,hl] at hh
  omega

include hf in
/-- The faithful five-root action is onto S₅ at the computed order. -/
theorem normalizer_point_quotient_of_transitive (hs : Source.Hypotheses c i z)
    (ht : ∀ x ∈ A c i false, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i false : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G) = 384) :
    Nonempty (normalizerQuotient c i false ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨f,hf'⟩ := exists_pointNormalizer_embedding c i z t hf hs
  have hc : Nat.card (normalizerQuotient c i false) = Nat.card (Equiv.Perm (Fin 5)) := by
    rw [normalizer_point_quotient_card_of_transitive c i z t hf ht hl]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf',hc⟩)⟩

omit [Finite G] in
include hf in
/-- The plane quotient has order 36 from the literal local-plane normalizer. -/
theorem normalizer_plane_quotient_card_of_transitive
    (ht : ∀ x ∈ A c i true, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i true : Set G), MulAut.conj n (rootElement c i z) = x)
    (hl : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t) :
    Nat.card (normalizerQuotient c i true) = 36 := by
  have hh := normalizer_quotient_card_of_root_transitive c i z t hf true ht
  obtain ⟨e⟩ := hf.t_centralizer_iso
  rw [hf.root_class_A_plane,hl,Nat.card_congr e.toEquiv] at hh
  norm_num [Nat.card_prod,DihedralGroup.card,DihedralGroup.nat_card] at hh
  omega

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
