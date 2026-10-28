module

public import Theory.ElementaryAbelian.AbelianNormalClosure
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Core
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Action


/-!
# Apply the rank-ten bound to the larger component action

Source: Aschbacher–Smith, Lemma 8.2.7, printed p.718 (PDF p.735).

For a literal section E/D, an irreducible J-action kills O₂(X). Inversion
modulo O₂(H) consequently gives exact inversion in this action image.
Its odd subgroup remains nontrivial and acts fully, so the image of the
element of V is an involution. The L₃(4) and M₂₂ table entries give
|V:U|≤64 and |V:B|=2, hence the required five-dimensional bound modulo U.
Applying SectionBound now proves the bound ten, without assuming any bound
on E/D and without assuming B≤X.

The source proof of inversion modulo O₂(H) remains an explicit input.
The construction of E/D for J=K_U T is in the sibling Section module.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
variable {G : Type*} [Group G] [Finite G]

/-- Apply SectionBound to the actual larger conjugation action. The table
bound and the involution hypothesis are derived, rather than supplied. -/
theorem section_rank_from_source_rows (X H I U V T J E D Y : Subgroup G)
    [(D.subgroupOf E).Normal] [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (E ⧸ D.subgroupOf E)] [Nontrivial (E ⧸ D.subgroupOf E)]
    (ρ : J →* MulAut (E ⧸ D.subgroupOf E))
    (hX : X = (pResidual 2 H).map H.subtype)
    (hIH : I ≤ H) (hVI : V ≤ I) (hTH : T ≤ H)
    (hXJ : X ≤ J) (hJX : J ≤ normalizer (X : Set G))
    (hQT : X.pCoreIn 2 ≤ T) (hTV : T ≤ normalizer (V : Set G))
    (hVT : V ≤ T) (hUT : U ≤ T)
    (hUB : U ≤ V ⊓ I.pCoreIn 2) (hk : (V ⊓ I.pCoreIn 2).relIndex V = 2)
    (hUcard : Nat.card U = 16) (hVcard : Nat.card V = 512 ∨ Nat.card V = 1024)
    (hER : E ≤ X.pCoreIn 2 ⊔ U) (hUD : U ≤ D)
    (hJE : J ≤ normalizer (E : Set G))
    (hact : ∀ j : J, ∀ e : E,
      ρ j (QuotientGroup.mk' (D.subgroupOf E) e) =
        QuotientGroup.mk' (D.subgroupOf E)
          ⟨(j : G) * (e : G) * (j : G)⁻¹,
            (mem_normalizer_iff.mp (hJE j.property) e).mp e.property⟩)
    (hirr : ∀ A : Subgroup (E ⧸ D.subgroupOf E),
      (∀ j : J, ∀ w, w ∈ A → ρ j w ∈ A) → A = ⊥ ∨ A = ⊤)
    (hYX : Y ≤ X) (hodd : Odd (Nat.card Y))
    (hactive : ¬ Y.subgroupOf J ≤ ρ.ker)
    (hfull : commutatorAction ((Y.subgroupOf J).map ρ) (E ⧸ D.subgroupOf E) = ⊤)
    (v : J) (hv : (v : G) ∈ V)
    (hinv : ∀ y ∈ Y, (v : G) * y * (v : G)⁻¹ * y ∈ H.pCoreIn 2) :
    Module.finrank (ZMod 2) (Additive (E ⧸ D.subgroupOf E)) ≤ 10 := by
  have hXH : X ≤ H := hX ▸ map_subtype_le _
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hX]
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hYJ := hYX.trans hXJ
  have hinverts := image_inversion X H J Y ρ hXH hJX hYX
    (core_killed J X ρ hJX hirr) v hinv
  have hsq : v ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (v : G) hv)
  have ht := inverting_image_isInvolution J Y ρ hYJ hodd hactive v hsq hinverts
  have himgodd : Odd (Nat.card ((Y.subgroupOf J).map ρ)) := by
    apply Odd.of_dvd_nat ?_ (card_map_dvd (Y.subgroupOf J) ρ)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hYJ).toEquiv]
  let _ : IsElementaryAbelian 2 (V ⊓ X.pCoreIn 2 : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hrow := residual_core_table_rank X H I V U hXH hHX hIH hVI hUB hk
    (table_relative_index V U (hUB.trans inf_le_left) hUcard hVcard)
  have hUC : U ≤ centralizer (V : Set G) := by
    intro u hu
    apply mem_centralizer_iff.mpr
    intro w hw
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : V) ⟨u, (hUB hu).1⟩)
  let _ : MulDistribMulAction J (E ⧸ D.subgroupOf E) :=
    MulDistribMulAction.compHom (E ⧸ D.subgroupOf E) ρ
  have hα : MulDistribMulAction.toMulAut J (E ⧸ D.subgroupOf E) = ρ := by
    ext j w
    rfl
  apply section_finrank_le_ten X U V T J E D (hTH.trans hHX) hQT hTV hVT hUT hUC
    hER hUD hJE hact ((Y.subgroupOf J).map ρ) himgodd v
    (by rw [hα]; exact ht) hv ?_ hfull hrow
  rwa [hα]

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
