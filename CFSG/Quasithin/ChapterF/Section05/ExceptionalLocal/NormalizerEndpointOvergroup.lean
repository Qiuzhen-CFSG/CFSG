module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPointGraphCentralizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Both original endpoint centralizers inside their normalizers

The point and plane graph-centralizer calculations prove that R normalizes
both Eᵢ. Their joins have order 192 and are exactly N_G(Aᵢ)∩C_G(f).
The stated inputs are the earlier root-transitivity and local endpoint
normalizer computations, which have independent source producers.

Source: Aschbacher--Smith F.5.4(3), printed p.301.
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

theorem normalizer_R_normalizes_E (hs : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (ht : ∀ b, ∀ x ∈ A c i b, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z) = x)
    (hp : Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G) = 384)
    (hl : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t)
    (b : Bool) : Rimage c i R ≤ normalizer (E c i b : Set G) := by
  cases b
  · exact normalizer_R_normalizes_E_point c i z t hf hs R hR (ht false) hp
  · exact normalizer_R_normalizes_E_plane c i z t hf R hR (ht true) hl

/-- The literal endpoint join has the required order. -/
theorem normalizer_ER_card_of_normalizes
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i))) (b : Bool)
    (hE : Rimage c i R ≤ normalizer (E c i b : Set G)) :
    Nat.card (E c i b ⊔ Rimage c i R : Subgroup G) = 192 := by
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (E c i b) (Rimage c i R) hE
  rw [normalizer_E_card c i z t hf,normalizer_R_card c i z t hf,
    inf_comm,normalizer_R_inf_E c i z t hf R hR b,
    normalizer_TfImage_card c i z t hf] at hh
  omega

/-- The original join is the full graph centralizer inside each normalizer. -/
theorem normalizer_ER_eq_graph_centralizer (hs : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (ht : ∀ b, ∀ x ∈ A c i b, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z) = x)
    (hp : Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G) = 384)
    (hl : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t)
    (b : Bool) : E c i b ⊔ Rimage c i R = normalizer (A c i b : Set G) ⊓ C c i := by
  have hE := normalizer_R_normalizes_E c i z t hf hs R hR ht hp hl b
  have hc := normalizer_ER_card_of_normalizes c i z t hf R hR b hE
  apply eq_of_le_of_card_ge
    (sup_le (le_inf (E_le_normalizer_A c i b) inf_le_right)
      (le_inf (normalizer_R_normalizes_A c i z t hf R hR b) (Rimage_le_C c i R)))
  rw [hc]
  cases b
  · exact (normalizer_point_graph_centralizer_card c i z t hf hs (ht false) hp).le
  · exact (normalizer_plane_graph_centralizer_card c i z t hf R hR (ht true) hl).le

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
