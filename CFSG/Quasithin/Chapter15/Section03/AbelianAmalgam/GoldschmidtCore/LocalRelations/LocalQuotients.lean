module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.CoreObstruction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SubgroupProductCard

/-!
# The second local quotient and the terminal intersection

A normal subgroup with intrinsic two-core quotient of order three meets
any containing Sylow two-subgroup in its own two-core. The subgroup it
supplements therefore has Sylow index three. Applied to `X_E`, the
commutator identity `X_E=[X_E,J(R)]` prevents `T_E` from being normal;
the faithful three-coset action identifies the intrinsic quotient of
`G₂=X_E T_E` with `S₃`.

For the intersection, the original `S₃ × S₃` quotient gives
`[G_E:T_E]=9`. The two normal cubic residuals give index three
for `Y_E T_E` and `X_E T_E`. Their literal product is `G_E`, so
the product-order formula gives intersection `T_E`. Since `G₁≤M`,
this also proves `G₁ ∩ G₂=T_E`.

Only genuine conclusions of 15.3.66–67 are inputs. No equality or
containment between the two local cores and `R=C_T(V)` is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
construction preceding Lemma 15.3.68, printed p.1154, PDF p.1171.
-/

public section

open scoped Pointwise
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem cubic_core_intersection (A D : Subgroup G) (hD : IsPGroup 2 D)
    (hQ : A.pCoreIn 2 ≤ D) (hq : Nat.card (A ⧸ pCore 2 A) = 3) :
    A ⊓ D = A.pCoreIn 2 := by
  have hind : ¬ 2 ∣ (pCore 2 A).index := by
    rw [index_eq_card, hq]
    decide
  let P : Sylow 2 A := pCore_isPGroup.toSylow hind
  have hle : D.subgroupOf A ≤ pCore 2 A := by
    have hh := (hD.comap_subtype : IsPGroup 2 (D.subgroupOf A)).inf_normalizer_sylow P
    change D.subgroupOf A ⊓ normalizer (pCore 2 A : Set A) =
      D.subgroupOf A ⊓ pCore 2 A at hh
    rw [(pCore 2 A).normalizer_eq_top, inf_top_eq] at hh
    exact inf_eq_left.mp hh.symm
  apply le_antisymm
  · intro x hx
    exact mem_map.mpr ⟨⟨x,hx.1⟩, hle hx.2, rfl⟩
  · exact le_inf (pCoreIn_le 2 A) hQ

private theorem cubic_sup_index (A D : Subgroup G) (hD : IsPGroup 2 D)
    (hn : D ≤ normalizer (A : Set G)) (hQ : A.pCoreIn 2 ≤ D)
    (hq : Nat.card (A ⧸ pCore 2 A) = 3) : D.relIndex (A ⊔ D) = 3 := by
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A D hn
  rw [cubic_core_intersection A D hD hQ hq,
    pCoreIn, card_map_of_injective A.subtype_injective] at hprod
  have hA := (pCore 2 A).card_mul_index
  rw [index_eq_card, hq] at hA
  have hDcard := relIndex_mul_relIndex (⊥ : Subgroup G) D (A ⊔ D) bot_le le_sup_right
  simp only [relIndex_bot_left] at hDcard
  have hQpos : 0 < Nat.card (pCore 2 A) := Nat.card_pos
  have hDpos : 0 < Nat.card D := Nat.card_pos
  rw [← hA, ← hDcard, mul_assoc] at hprod
  have hh := Nat.eq_of_mul_eq_mul_left hQpos hprod
  rw [mul_comm 3] at hh
  exact (Nat.eq_of_mul_eq_mul_left hDpos hh).symm

/-- The second local group has its intrinsic symmetric-three quotient. -/
theorem secondAmalgam_quotient (T V E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hEV : E ≤ V)
    (hquot : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)))
    (hcomm : lineX E = ⁅lineX E, elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))⁆) :
    Nonempty ((secondAmalgamGroup T E ⧸ pCore 2 (secondAmalgamGroup T E)) ≃*
      Equiv.Perm (Fin 3)) := by
  let D := lineT T E
  let B := secondAmalgamGroup T E
  have hD : IsPGroup 2 D :=
    (U.isPGroup'.map (lineNormalizer E).subtype).of_equiv (MulEquiv.subgroupCongr hU)
  have hQD : (lineX E).pCoreIn 2 ≤ D := by
    have hQ := pCoreIn_mono_of_normalizes
      ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))
      (lineNormalizer_le_normalizer_lineX E) (p := 2)
    exact hQ.trans (by
      change (pCore 2 (lineNormalizer E)).map (lineNormalizer E).subtype ≤ lineT T E
      rw [← hU]
      exact map_mono (pCore_isPGroup.le_sylow_of_normal U))
  have hq : Nat.card (lineX E ⧸ pCore 2 (lineX E)) = 3 := by
    obtain ⟨e⟩ := hquot
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hi : (D.subgroupOf B).index = 3 :=
    cubic_sup_index (lineX E) D hD
      (inf_le_right.trans (lineNormalizer_le_normalizer_lineX E)) hQD hq
  let P : Sylow 2 B := (hD.comap_subtype : IsPGroup 2 (D.subgroupOf B)).toSylow
    (by change ¬ 2 ∣ (D.subgroupOf B).index; rw [hi]; decide)
  have hproper : pCore 2 B < (P : Subgroup B) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    have hDB : D = twoCoreAmbient B := by
      have hh := congrArg (fun Q : Subgroup B => Q.map B.subtype) he
      rw [show (P : Subgroup B) = D.subgroupOf B from rfl,
        map_subgroupOf_eq_of_le (show D ≤ B from le_sup_right)] at hh
      exact hh.symm
    have hRD : T ⊓ centralizer (V : Set G) ≤ D := le_inf inf_le_left
      (inf_le_right.trans ((centralizer_le hEV).trans (centralizer_le_normalizer (E : Set G))))
    exact centralizer_not_le_secondCore T V E hquot hcomm (hRD.trans hDB.le)
  exact sylow_index_three_core_quotient P hi hproper

private theorem index_nine_of_core_quotient (H : Type*) [Group H] [Finite H]
    (U : Sylow 2 H) (hq : Nat.card (H ⧸ pCore 2 H) = 36) :
    (U : Subgroup H).index = 9 := by
  let P : Sylow 2 (H ⧸ pCore 2 H) := U.mapSurjective (QuotientGroup.mk'_surjective _)
  have hc : Nat.card (P : Subgroup (H ⧸ pCore 2 H)) = 4 := by
    rw [P.card_eq_multiplicity, hq]
    decide +kernel
  have hi : (P : Subgroup (H ⧸ pCore 2 H)).index = (U : Subgroup H).index :=
    (U : Subgroup H).index_map_eq (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal U)
  have hh := (P : Subgroup (H ⧸ pCore 2 H)).card_mul_index
  rw [hc, hi, hq] at hh
  omega

/-- The two terminal local groups meet in exactly the fixed line Sylow subgroup.
The count uses the original S₃ × S₃ quotient and the two normal cubic residuals. -/
theorem amalgam_intersection (M Y T E F : Subgroup G)
    (hYM : Y ≤ M) (hTM : T ≤ M)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hYN : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal)
    (hYq : Nonempty ((lineY Y E ⧸ pCore 2 (lineY Y E)) ≃* Multiplicative (ZMod 3)))
    (hXq : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)))
    (hHq : Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hME : lineM M E = lineY Y E ⊔ lineT T E)
    (hprod : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT T E : Set G)) :
    firstAmalgamGroup Y T E F ⊓ secondAmalgamGroup T E = lineT T E := by
  let D := lineT T E
  let A := lineY Y E ⊔ D
  let B := secondAmalgamGroup T E
  let H := lineNormalizer E
  have hD : IsPGroup 2 D :=
    (U.isPGroup'.map H.subtype).of_equiv (MulEquiv.subgroupCongr hU)
  have hDH : D ≤ H := inf_le_right
  have hAD : D ≤ A := le_sup_right
  have hBD : D ≤ B := le_sup_right
  have hAH : A ≤ H := sup_le ((lineY_le Y E).trans inf_le_right) inf_le_right
  have hBH : B ≤ H := sup_le
    ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G))) inf_le_right
  have hcore : H.pCoreIn 2 ≤ D := by
    change (pCore 2 H).map H.subtype ≤ lineT T E
    rw [← hU]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal U)
  have hindex (L : Subgroup G) (hLH : L ≤ H) (hn : H ≤ normalizer (L : Set G))
      (hq : Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3))) :
      D.relIndex (L ⊔ D) = 3 := by
    apply cubic_sup_index L D hD (hDH.trans hn)
      ((pCoreIn_mono_of_normalizes hLH hn).trans hcore)
    obtain ⟨e⟩ := hq
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hiA : D.relIndex A = 3 := hindex (lineY Y E) ((lineY_le Y E).trans inf_le_right)
    ((normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans inf_le_right)).mp hYN) hYq
  have hiB : D.relIndex B = 3 := hindex (lineX E)
    ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))
    (lineNormalizer_le_normalizer_lineX E) hXq
  have hiH : D.relIndex H = 9 := by
    have he : D.subgroupOf H = (U : Subgroup H) := by
      rw [show D = lineT T E from rfl, ← hU]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    change (D.subgroupOf H).index = 9
    rw [he]
    apply index_nine_of_core_quotient H U
    obtain ⟨e⟩ := hHq
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_perm]
  have hAB : (A : Set G) * (B : Set G) = (H : Set G) := by
    apply Set.Subset.antisymm
    · rintro g ⟨a, ha, b, hb, rfl⟩
      exact H.mul_mem (hAH ha) (hBH hb)
    · intro g hg
      rw [show (H : Set G) = (lineNormalizer E : Set G) from rfl, hprod] at hg
      obtain ⟨w, ⟨y, hy, x, hx, rfl⟩, t, ht, rfl⟩ := hg
      exact ⟨y, mem_sup_left hy, x * t, B.mul_mem (mem_sup_left hx) (mem_sup_right ht),
        (mul_assoc y x t).symm⟩
  have hcard (K : Subgroup G) (hDK : D ≤ K) : Nat.card D * D.relIndex K = Nat.card K := by
    simpa only [relIndex_bot_left] using relIndex_mul_relIndex (⊥ : Subgroup G) D K bot_le hDK
  have hcA := hcard A hAD
  have hcB := hcard B hBD
  have hcH := hcard H hDH
  rw [hiA] at hcA
  rw [hiB] at hcB
  rw [hiH] at hcH
  have hcAB := card_set_mul_mul_card_inf A B
  rw [hAB] at hcAB
  change Nat.card H * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B at hcAB
  rw [← hcA, ← hcB, ← hcH] at hcAB
  have he : A ⊓ B = D := by
    symm
    apply eq_of_le_of_card_ge (le_inf hAD hBD)
    have hpos : 0 < Nat.card D := Nat.card_pos
    have hh : Nat.card D * (9 * Nat.card (A ⊓ B : Subgroup G)) =
        Nat.card D * (9 * Nat.card D) := by
      calc
        _ = (Nat.card D * 9) * Nat.card (A ⊓ B : Subgroup G) := by ring
        _ = (Nat.card D * 3) * (Nat.card D * 3) := hcAB
        _ = _ := by ring
    have heq := Nat.eq_of_mul_eq_mul_left hpos hh
    omega
  apply le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  have hfirst : firstAmalgamGroup Y T E F ≤ M :=
    sup_le ((lineY_le Y F).trans inf_le_left |>.trans hYM) (inf_le_left.trans hTM)
  intro x hx
  have ha : x ∈ A := by
    change x ∈ lineY Y E ⊔ lineT T E
    rw [← hME]
    exact ⟨hfirst hx.1, hBH hx.2⟩
  exact he.le ⟨ha, hx.2⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
