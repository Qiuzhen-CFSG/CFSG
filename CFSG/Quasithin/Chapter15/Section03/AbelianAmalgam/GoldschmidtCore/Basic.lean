module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Basic
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.PPrimeCore

/-!
# Conjugation and core transfers for the terminal amalgam

Right conjugation constructs the second singular line. The index-two
normalizer intersection is unchanged, and the line residual conjugates
with the line. Consequently the first local group inherits its symmetric
quotient from 15.3.66; both local joins are the source's setwise products.

The normalization and commutator arguments place the module in the
ambient two-core. Once the Sylow and local-core calculations are supplied,
it lies in the center of that core. An adapter constructs the actual
Chapter F Goldschmidt triple inside the generated subgroup, transporting
both quotient types through the subgroup inclusions. Finally, a two-group
centralizer eliminates the odd core in the argument on printed p.1155.

These are conditional steps, not the complete Lemma 15.3.68. The local
geometry, maximal-local Sylow assertion and Thompson argument must still
be assembled by the owning module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1154–1155, PDF pp.1171–1172.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
variable {G : Type*} [Group G]

/-- An index-two line stabilizer is unchanged when the line is conjugated
by an element of `T`. -/
theorem lineT_otherLine (T E : Subgroup G) (s : G) (hs : s ∈ T)
    (hi : (lineT T E).relIndex T = 2) :
    lineT T (otherLine E s) = lineT T E := by
  have hn : T ≤ normalizer (lineT T E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp (normal_of_index_eq_two hi)
  have hT : T.map (MulAut.conj s⁻¹).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer (T.inv_mem hs))
  have hTE := mem_normalizer_iff_map_conj_eq.mp (hn (T.inv_mem hs))
  calc
    lineT T (otherLine E s) = (lineT T E).map (MulAut.conj s⁻¹).toMonoidHom := by
      rw [lineT, lineT, lineNormalizer, map_inf _ _ _ (MulAut.conj s⁻¹).injective, hT,
        map_equiv_normalizer_eq]
      rfl
    _ = lineT T E := hTE

/-- An element outside the line stabilizer gives a distinct line. -/
theorem otherLine_ne (T E : Subgroup G) (s : G) (hs : s ∈ T)
    (hsE : s ∉ lineT T E) : otherLine E s ≠ E := by
  intro h
  have hi : s⁻¹ ∈ lineNormalizer E := mem_normalizer_iff_map_conj_eq.mpr h
  exact hsE ⟨hs, by simpa using (lineNormalizer E).inv_mem hi⟩

variable [Finite G]

/-- The two-residual commutes with right conjugation. -/
theorem lineY_otherLine (Y E : Subgroup G) (s : G)
    (hs : s ∈ normalizer (Y : Set G)) :
    lineY Y (otherLine E s) = otherLine (lineY Y E) s := by
  have hY : Y.map (MulAut.conj s⁻¹).toMonoidHom = Y :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hs)
  unfold lineY otherLine lineNormalizer
  rw [map_twoResidualAmbient_of_subgroup_image _ _ _ rfl,
    map_inf _ _ _ (MulAut.conj s⁻¹).injective, hY, map_equiv_normalizer_eq]

/-- The normalization calculation identifies the first join with `Y_F T_E`. -/
theorem firstAmalgam_product (Y T E F : Subgroup G)
    (hTY : T ≤ normalizer (Y : Set G)) (hTF : lineT T F = lineT T E) :
    (firstAmalgamGroup Y T E F : Set G) = (lineY Y F : Set G) * (lineT T E : Set G) := by
  apply coe_mul_of_right_le_normalizer_left
  rw [← hTF]
  exact lineT_le_normalizer_lineY Y T F hTY

/-- The second join is `X_E T_E`, since `G_E` normalizes `X_E`. -/
theorem secondAmalgam_product (T E : Subgroup G) :
    (secondAmalgamGroup T E : Set G) = (lineX E : Set G) * (lineT T E : Set G) :=
  coe_mul_of_right_le_normalizer_left _ _
    (inf_le_right.trans (lineNormalizer_le_normalizer_lineX E))

/-- The first local group is the conjugate of the local group in 15.3.66(5). -/
theorem firstAmalgam_eq_conjugate (Y T E : Subgroup G) (s : G)
    (hs : s ∈ T) (hTY : T ≤ normalizer (Y : Set G))
    (hi : (lineT T E).relIndex T = 2) :
    firstAmalgamGroup Y T E (otherLine E s) = otherLine (lineY Y E ⊔ lineT T E) s := by
  have hn : T ≤ normalizer (lineT T E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp (normal_of_index_eq_two hi)
  have hTE : (lineT T E).map (MulAut.conj s⁻¹).toMonoidHom = lineT T E :=
    mem_normalizer_iff_map_conj_eq.mp (hn (T.inv_mem hs))
  rw [firstAmalgamGroup, lineY_otherLine Y E s (hTY hs)]
  simp only [otherLine, Subgroup.map_sup, hTE]

/-- Transport the actual symmetric-group quotient from 15.3.66(5). -/
theorem firstAmalgam_quotient (Y T E : Subgroup G) (s : G)
    (hs : s ∈ T) (hTY : T ≤ normalizer (Y : Set G))
    (hi : (lineT T E).relIndex T = 2)
    (hquot : Nonempty (((lineY Y E ⊔ lineT T E : Subgroup G) ⧸
      pCore 2 (lineY Y E ⊔ lineT T E : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Nonempty ((firstAmalgamGroup Y T E (otherLine E s) ⧸
      pCore 2 (firstAmalgamGroup Y T E (otherLine E s))) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨q⟩ := hquot
  let e := ((MulAut.conj s⁻¹).subgroupMap (lineY Y E ⊔ lineT T E)).trans
    (MulEquiv.subgroupCongr (firstAmalgam_eq_conjugate Y T E s hs hTY hi).symm)
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans q⟩

omit [Finite G] in
/-- Both generators normalize `Y_E`, proving the first assertion of 15.3.68
from its two earlier normalization inputs. -/
theorem amalgam_normalizes_lineY (Y T E F : Subgroup G)
    (hY : Y ⊔ lineT T E ≤ normalizer (lineY Y E : Set G))
    (hE : lineNormalizer E ≤ normalizer (lineY Y E : Set G)) :
    amalgamGroup Y T E F ≤ normalizer (lineY Y E : Set G) := by
  have hFY : lineY Y F ≤ Y :=
    (map_subtype_le (Stellmacher.twoResidualSubgroup _)).trans inf_le_left
  have hXE : lineX E ≤ lineNormalizer E :=
    (map_subtype_le (Stellmacher.twoResidualSubgroup _)).trans
      (centralizer_le_normalizer (E : Set G))
  exact sup_le (sup_le (hFY.trans (le_sup_left.trans hY)) (le_sup_right.trans hY))
    (sup_le (hXE.trans hE) (inf_le_right.trans hE))

/-- Build the Chapter F triple inside the generated subgroup. The quotient
equivalences use the intrinsic cores of the embedded local subgroups. -/
theorem goldschmidtTriple_of_local_quotients (A B T : Subgroup G)
    (hA : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)))
    (hB : Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)))
    (hAB : A ⊓ B = T) (hT : Stellmacher.IsSylowSubgroupIn T (A ⊔ B)) :
    ChapterF.IsGoldschmidtTriple (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)) := by
  obtain ⟨eA⟩ := hA
  obtain ⟨eB⟩ := hB
  obtain ⟨S, hS⟩ := hT
  let fA := subgroupOfEquivOfLe (show A ≤ A ⊔ B from le_sup_left)
  let fB := subgroupOfEquivOfLe (show B ≤ A ⊔ B from le_sup_right)
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ fA (pCore_map_iso 2 fA)).trans eA⟩,
    ⟨(QuotientGroup.congr _ _ fB (pCore_map_iso 2 fB)).trans eB⟩, S, ?_⟩
  · rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  · apply map_injective (A ⊔ B).subtype_injective
    rw [map_inf _ _ _ (A ⊔ B).subtype_injective,
      map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le le_sup_right, hAB, hS]

omit [Finite G] in
private theorem core_inter_normalizer (H K : Subgroup G)
    (hKH : K ≤ normalizer (H : Set G)) :
    K ⊓ Stellmacher.twoCoreAmbient H ≤ Stellmacher.twoCoreAmbient K := by
  have hn : K ≤ normalizer (Stellmacher.twoCoreAmbient H : Set G) :=
    hKH.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hc : (Stellmacher.twoCoreAmbient H).subgroupOf K ≤ pCore 2 K :=
    le_sSup ⟨normal_subgroupOf_of_le_normalizer hn,
      (pCore_isPGroup.map H.subtype).comap_subtype⟩
  intro x hx
  exact mem_map.mpr ⟨⟨x, hx.1⟩, hc hx.2, rfl⟩

omit [Finite G] in
private theorem commutator_eq_le_core (V H : Subgroup G) (hV : IsPGroup 2 V)
    (hVH : V ≤ normalizer (H : Set G)) (hHV : H ≤ normalizer (V : Set G))
    (hc : ⁅V, H⁆ = V) : V ≤ Stellmacher.twoCoreAmbient H := by
  have hle : V ≤ H := hc ▸ le_normalizer_iff_commutator_le_right.mp hVH
  have hv : V.subgroupOf H ≤ pCore 2 H := le_sSup
    ⟨(normal_subgroupOf_iff_le_normalizer hle).mpr hHV, hV.comap_subtype⟩
  intro x hx
  exact mem_map.mpr ⟨⟨x, hle hx⟩, hv hx, rfl⟩

omit [Finite G] in
/-- The commutator identity from 15.3.66 places `V` in `O₂(Y_E)`;
normalization then puts it in `O₂(G₀)`. -/
theorem amalgam_module_le_core (Y T V E F : Subgroup G) (hV : IsPGroup 2 V)
    (hVT : V ≤ lineT T E) (hYV : Y ≤ normalizer (V : Set G))
    (hY : Y ⊔ lineT T E ≤ normalizer (lineY Y E : Set G))
    (hE : lineNormalizer E ≤ normalizer (lineY Y E : Set G))
    (hc : ⁅V, lineY Y E⁆ = V) :
    V ≤ Stellmacher.twoCoreAmbient (amalgamGroup Y T E F) := by
  have hYE : lineY Y E ≤ Y :=
    (map_subtype_le (Stellmacher.twoResidualSubgroup _)).trans inf_le_left
  have hVc := commutator_eq_le_core V (lineY Y E) hV
    (hVT.trans (le_sup_right.trans hY)) (hYE.trans hYV) hc
  exact (le_inf (hVT.trans (le_sup_right.trans le_sup_left)) hVc).trans
    (core_inter_normalizer _ _ (amalgam_normalizes_lineY Y T E F hY hE))

omit [Finite G] in
private theorem core_le_local_core (H K : Subgroup G) (hKH : K ≤ H)
    (hQK : Stellmacher.twoCoreAmbient H ≤ K) :
    Stellmacher.twoCoreAmbient H ≤ Stellmacher.twoCoreAmbient K := by
  exact (le_inf hQK le_rfl).trans (core_inter_normalizer H K (hKH.trans H.le_normalizer))

omit [Finite G] in
/-- Once `T_E` is Sylow in `G₀`, its normal two-core lies in both local
cores. Their centralizer bound makes `V` central in that core. -/
theorem amalgam_module_le_center (Y T V E F : Subgroup G)
    (hVQ : V ≤ Stellmacher.twoCoreAmbient (amalgamGroup Y T E F))
    (hT : Stellmacher.IsSylowSubgroupIn (lineT T E) (amalgamGroup Y T E F))
    (hcommon : Stellmacher.twoCoreAmbient (firstAmalgamGroup Y T E F) ⊓
      Stellmacher.twoCoreAmbient (secondAmalgamGroup T E) ≤ centralizer (V : Set G)) :
    V ≤ (center (Stellmacher.twoCoreAmbient (amalgamGroup Y T E F))).map
      (Stellmacher.twoCoreAmbient (amalgamGroup Y T E F)).subtype := by
  obtain ⟨S, hS⟩ := hT
  have hQT : Stellmacher.twoCoreAmbient (amalgamGroup Y T E F) ≤ lineT T E := by
    rw [← hS]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal S)
  have hQ₁ := core_le_local_core (amalgamGroup Y T E F) (firstAmalgamGroup Y T E F)
    le_sup_left (hQT.trans le_sup_right)
  have hQ₂ := core_le_local_core (amalgamGroup Y T E F) (secondAmalgamGroup T E)
    le_sup_right (hQT.trans le_sup_right)
  have hQV := (le_inf hQ₁ hQ₂).trans hcommon
  intro v hv
  refine mem_map.mpr ⟨⟨v, hVQ hv⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (hQV q.property) v hv).symm

omit [Finite G] in
private theorem sylowIn_intermediate (T H K : Subgroup G) (hTH : T ≤ H) (hHK : H ≤ K)
    (hT : Stellmacher.IsSylowSubgroupIn T K) : Stellmacher.IsSylowSubgroupIn T H := by
  obtain ⟨S, hS⟩ := hT
  let f : H →* K := inclusion hHK
  have hf : Function.Injective f := inclusion_injective hHK
  have hr : (S : Subgroup K) ≤ f.range := by
    intro x hx
    have hxT : (x : G) ∈ T := hS ▸ mem_map.mpr ⟨x, hx, rfl⟩
    exact ⟨⟨x, hTH hxT⟩, rfl⟩
  refine ⟨S.comapOfInjective f hf hr, ?_⟩
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hS ▸ mem_map.mpr ⟨f y, hy, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp (hS ▸ hx)
    exact mem_map.mpr ⟨⟨y, hTH hx⟩, hy, rfl⟩

/-- The nontrivial module supplies a genuine maximal two-local overgroup;
the Sylow assertion there restricts to `G₀`. -/
theorem amalgam_sylow_of_maximalLocals (Y T V E F : Subgroup G) (hV : V ≠ ⊥)
    (hVQ : V ≤ Stellmacher.twoCoreAmbient (amalgamGroup Y T E F))
    (hlocal : ∀ M₀ ∈ Theory.GroupTheory.maximalTwoLocalOvergroups (amalgamGroup Y T E F),
      Stellmacher.IsSylowSubgroupIn (lineT T E) M₀) :
    Stellmacher.IsSylowSubgroupIn (lineT T E) (amalgamGroup Y T E F) := by
  have hQ : pCore 2 (amalgamGroup Y T E F) ≠ ⊥ := by
    intro h
    apply hV
    apply le_bot_iff.mp
    simpa only [Stellmacher.twoCoreAmbient, h, Subgroup.map_bot] using hVQ
  obtain ⟨M₀, hM₀, hGM₀⟩ :=
    Theory.GroupTheory.maximalTwoLocalOvergroups_nonempty_of_twoCore_ne_bot _ hQ
  exact sylowIn_intermediate _ _ _ (le_sup_right.trans le_sup_left) hGM₀
    (hlocal M₀ ⟨hM₀, hGM₀⟩)

/-- A two-group ambient centralizer of `V ≤ O₂(P)` eliminates `O(P)`:
the two normal cores commute, and their orders are coprime. -/
theorem oddCore_eq_bot (P V R : Subgroup G)
    (hV : V ≤ Stellmacher.twoCoreAmbient P)
    (hC : centralizer (V : Set G) ≤ R) (hR : IsPGroup 2 R) : pPrimeCore 2 P = ⊥ := by
  have hcop : (Nat.card (pPrimeCore 2 P)).Coprime (Nat.card (pCore 2 P)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := P)).exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := P)).symm.pow_right n
  have hc : pPrimeCore 2 P ≤ centralizer (pCore 2 P : Set P) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hcop))
  have hOR : (pPrimeCore 2 P).map P.subtype ≤ R := by
    rintro x ⟨x, hx, rfl⟩
    apply hC
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨v, hvQ, rfl⟩ := hV hv
    exact congrArg P.subtype (mem_centralizer_iff.mp (hc hx) v hvQ)
  have hcopR : (Nat.card ((pPrimeCore 2 P).map P.subtype)).Coprime (Nat.card R) := by
    rw [card_map_of_injective P.subtype_injective]
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := P)).symm.pow_right n
  have hbot : (pPrimeCore 2 P).map P.subtype = ⊥ :=
    le_bot_iff.mp ((le_inf le_rfl hOR).trans_eq (disjoint_of_coprime_natCard hcopR).eq_bot)
  exact ((pPrimeCore 2 P).map_eq_bot_iff_of_injective P.subtype_injective).mp hbot

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
