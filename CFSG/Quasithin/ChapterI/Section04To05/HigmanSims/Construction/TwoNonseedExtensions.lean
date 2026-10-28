module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CanonicalEightCentralizer
public import Theory.GroupTheory.ElementaryEightCentralizer

/-!
# Exactly two elementary-sixteen extensions of an original nonseed eight

The original plane lifts and central cyclic four generate the full centralizer
of the constructed nonseed eight. Its two reflection joins are literal
subgroups of the original group. Every elementary sixteen containing the
eight centralizes it, so the intrinsic classification is also exhaustive in
the original group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Original HS data construct a nonseed eight whose full centralizer has
that eight as its center, and exactly two elementary-sixteen extensions in
the original group. One displayed extension contains the original seed-class
involution supplied by the canonical plane lift. -/
theorem TypeAt.exists_two_nonseed_eight_extensions (h : TypeAt z V) :
    ∃ (u c b : G) (E : pointCoreEights u),
      u ∈ V ∧ u ≠ 1 ∧ TypeAt u V ∧ E.val ∉ pointCoreSeedOrbit u V ∧
      Nat.card (centralizer (E.val : Set G)) = 32 ∧
      Nat.card (involutionCentralizer u ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 ∧
      orderOf c = 4 ∧ c ^ 2 = u ∧
      c ∈ (center ((involutionCentralizer u).pCoreIn 2)).map
        ((involutionCentralizer u).pCoreIn 2).subtype ∧
      b ^ 2 = 1 ∧ IsConj b z ∧ ¬ Commute b c ∧ b * c * b⁻¹ = c⁻¹ ∧
      (center (centralizer (E.val : Set G))).map
        (centralizer (E.val : Set G)).subtype = E.val ∧
      let A := E.val ⊔ zpowers b
      let B := E.val ⊔ zpowers (c * b)
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ A ≠ B ∧ A ⊓ B = E.val ∧
      (∀ F : Subgroup G,
        (E.val ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  obtain ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768,
    hc4, hc2, hcZ, hcK, hbK, hb2, hbz, hnc, hbc⟩ :=
    h.exists_nonabelian_eight_centralizer
  let K := centralizer (E.val : Set G)
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  have hEK : E.val ≤ K := le_centralizer_iff_isMulCommutative.mpr inferInstance
  let EK := E.val.subgroupOf K
  let : IsElementaryAbelian 2 EK := IsElementaryAbelian.subgroupOf hEK
  have hE8 : Nat.card EK = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv).trans E.property.2.2.2
  have hEZ : EK ≤ center K := by
    intro e he
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (k.property e he).symm
  let ck : K := ⟨c, hcK⟩
  let bk : K := ⟨b, hbK⟩
  have hck4 : orderOf ck = 4 := by rw [← orderOf_coe]; exact hc4
  have hckE : ck ^ 2 ∈ EK := by change c ^ 2 ∈ E.val; rw [hc2]; exact E.property.2.1
  have hbk2 : bk ^ 2 = 1 := Subtype.ext hb2
  have hncK : ¬ Commute bk ck := fun hh => hnc (congrArg Subtype.val hh.eq)
  have hbcK : bk * ck * bk⁻¹ = ck⁻¹ := Subtype.ext hbc
  obtain ⟨_, hZ, hAE, hA16, hBE, hB16, hne, hi, hall⟩ :=
    elementaryEight_centralizer_extensions hK32 EK hE8 hEZ ck bk hck4 hckE hbk2 hncK hbcK
  let AK := EK ⊔ zpowers bk
  let BK := EK ⊔ zpowers (ck * bk)
  let A := E.val ⊔ zpowers b
  let B := E.val ⊔ zpowers (c * b)
  have hEmap : EK.map K.subtype = E.val := map_subgroupOf_eq_of_le hEK
  have hAmap : AK.map K.subtype = A := by
    rw [Subgroup.map_sup, hEmap, MonoidHom.map_zpowers]
    rfl
  have hBmap : BK.map K.subtype = B := by
    rw [Subgroup.map_sup, hEmap, MonoidHom.map_zpowers]
    rfl
  let : IsElementaryAbelian 2 AK := hAE
  let : IsElementaryAbelian 2 BK := hBE
  have hAelem : IsElementaryAbelian 2 A := hAmap ▸ IsElementaryAbelian.map K.subtype
  have hBelem : IsElementaryAbelian 2 B := hBmap ▸ IsElementaryAbelian.map K.subtype
  have hAc : Nat.card A = 16 := by
    rw [← hAmap, card_map_of_injective K.subtype_injective]
    exact hA16
  have hBc : Nat.card B = 16 := by
    rw [← hBmap, card_map_of_injective K.subtype_injective]
    exact hB16
  refine ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768, hc4, hc2, hcZ, hb2, hbz, hnc, hbc,
    ?_, hAelem, hAc, hBelem, hBc, ?_, ?_, ?_⟩
  · rw [hZ, hEmap]
  · intro he
    exact hne (map_injective K.subtype_injective (hAmap.trans (he.trans hBmap.symm)))
  · change A ⊓ B = E.val
    rw [← hAmap, ← hBmap, ← map_inf _ _ _ K.subtype_injective, hi, hEmap]
  · intro F
    constructor
    · rintro ⟨hEF, hFe, hF16⟩
      let : IsElementaryAbelian 2 F := hFe
      have hFK : F ≤ K := by
        intro x hx y hy
        exact setLike_mul_comm (hEF hy) hx
      let FK := F.subgroupOf K
      let : IsElementaryAbelian 2 FK := IsElementaryAbelian.subgroupOf hFK
      have hEFK : EK ≤ FK := fun x hx => hEF hx
      have hFc : Nat.card FK = 16 :=
        (Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv).trans hF16
      have hFmap : FK.map K.subtype = F := map_subgroupOf_eq_of_le hFK
      rcases (hall FK).mp ⟨hEFK, inferInstance, hFc⟩ with he | he
      · exact Or.inl (hFmap.symm.trans ((congrArg (fun S : Subgroup K => S.map K.subtype) he).trans hAmap))
      · exact Or.inr (hFmap.symm.trans ((congrArg (fun S : Subgroup K => S.map K.subtype) he).trans hBmap))
    · rintro (rfl | rfl)
      · exact ⟨le_sup_left, hAelem, hAc⟩
      · exact ⟨le_sup_left, hBelem, hBc⟩

end CFSG.Quasithin.HigmanSims
