module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerEndpointOvergroup
public import Theory.GroupTheory.SpecificGroups.ElementaryFourSymmetricFourExtension.Recognition

/-!
# The endpoint joins in the original F.5 normalizer calculation

Each literal EᵢR has order 192, normal Eᵢ ≃ E₄ × S₄, and Sylow two-group
R ≃ D₈ × D₈. The structural extension theorem therefore identifies it
with D₈ × S₄. Its proof uses the centralizer of the normal A₄ and corrects
the S₄ complement's central twist; it does not identify groups by order.

Source: Aschbacher--Smith F.5.4(3), printed p.301. This discharges the
ER_iso field of NormalizerFacts from the earlier normalization calculation.
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

/-- The original endpoint join is D₈ × S₄ once the source normalization is known. -/
theorem normalizer_ER_iso_of_normalizes
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i))) (b : Bool)
    (hE : Rimage c i R ≤ normalizer (E c i b : Set G)) :
    Nonempty ((E c i b ⊔ Rimage c i R : Subgroup G) ≃*
      DihedralGroup 4 × Equiv.Perm (Fin 4)) := by
  let L := E c i b ⊔ Rimage c i R
  let E₀ := (E c i b).subgroupOf L
  let R₀ := (Rimage c i R).subgroupOf L
  have hEL : E c i b ≤ L := le_sup_left
  have hRL : Rimage c i R ≤ L := le_sup_right
  let : E₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le (E c i b).le_normalizer hE)
  obtain ⟨ee⟩ := hf.E_iso b
  let eE := (subgroupOfEquivOfLe hEL).trans ee
  obtain ⟨er⟩ := normalizer_R_iso c i z t hf R
  let eR := (subgroupOfEquivOfLe hRL).trans er
  have hLc : Nat.card L = 192 := normalizer_ER_card_of_normalizes c i z t hf R hR b hE
  have hRc : Nat.card R₀ = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv]
    exact normalizer_R_card c i z t hf R
  let S₀ : Sylow 2 L := Sylow.ofCard R₀ (by
    rw [hRc,hLc]
    rw [show 192=2^6*3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization])
  exact ElementaryFourSymmetricFourExtension.exists_dihedral_product E₀ eE hLc S₀ eR

/-- The F.5.4 endpoint structure under the actual earlier source inputs. -/
theorem normalizer_ER_iso (hs : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (ht : ∀ b, ∀ x ∈ A c i b, IsConj (rootElement c i z) x →
      ∃ n ∈ normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z) = x)
    (hp : Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G) = 384)
    (hl : M c i false ⊓ normalizer (A c i true : Set G) = Tcentralizer c i t)
    (b : Bool) :
    Nonempty ((E c i b ⊔ Rimage c i R : Subgroup G) ≃*
      DihedralGroup 4 × Equiv.Perm (Fin 4)) :=
  normalizer_ER_iso_of_normalizes c i z t hf R hR b
    (normalizer_R_normalizes_E c i z t hf hs R hR ht hp hl b)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
