module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Control
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Definitions
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Frattini descent to the original line normalizer

The kernel is formed in `G_E/E`, where `E` is relatively normal. Since
`V_E` is normal in `G_E`, this kernel is normal too, and `T_E` meets it
in a Sylow subgroup. A refined Frattini argument corrects elements of the
normal Thompson subgroup `I` by elements in its intersection with this
kernel. Thus `I = I₀ C_I(V_E/E)` without identifying the original two-core
with the temporary one.

An element centralizing `V_E/E` stabilizes `V` because `E ≤ V ≤ V_E`.
The earlier bound `N_G(V) ≤ M` absorbs the correction subgroup in `M_E`.
A coset bijection then transfers the recognized index three from `I₀`
to the original `G_E`; `M_E` need not be normal.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed pp.1153–1154, PDF pp.1170–1171. The remaining
common-residual and quotient identifications are separate obligations.
-/

@[expose] public section

open Subgroup
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G]

-- Correct inside the normal subgroup, rather than only inside the whole kernel.
private theorem normal_frattini [Finite G] (I K : Subgroup G) [I.Normal] [K.Normal]
    (P : Sylow 2 K) :
    (I : Set G) = (I ⊓ normalizer ((P : Subgroup K).map K.subtype : Set G) : Set G) *
      (I ⊓ K : Set G) := by
  let Q := (P : Subgroup K).map K.subtype
  let W := I ⊔ Q
  let N := K ⊓ W
  have hQK : Q ≤ K := map_subtype_le _
  have hQN : Q ≤ N := le_inf hQK le_sup_right
  have hidxK : ¬ 2 ∣ Q.relIndex K := by
    change ¬ 2 ∣ ((P : Subgroup K).map K.subtype |>.comap K.subtype).index
    rw [comap_map_eq_self_of_injective K.subtype_injective]
    exact P.not_dvd_index
  have hidxN : ¬ 2 ∣ Q.relIndex N := by
    intro hd
    exact hidxK (dvd_trans hd (dvd_of_mul_right_eq
      (N.relIndex K) (relIndex_mul_relIndex Q N K hQN inf_le_left)))
  let PN : Sylow 2 N := ((P.isPGroup'.map K.subtype).comap_subtype (K := N)).toSylow hidxN
  have hPN : (PN : Subgroup N).map N.subtype = Q := map_subgroupOf_eq_of_le hQN
  have hWN : W ≤ normalizer (N : Set G) :=
    (le_inf le_normalizer_of_normal W.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hfr : W ≤ normalizer (Q : Set G) ⊔ N := by
    simpa only [hPN] using le_normalizer_sylow_sup N W inf_le_right hWN PN
  have hnormN : normalizer (Q : Set G) ≤ normalizer (N : Set G) := by
    have hnW : normalizer (Q : Set G) ≤ normalizer (W : Set G) :=
      (le_inf le_normalizer_of_normal le_rfl).trans
        (normalizer_inf_normalizer_le_normalizer_sup I Q)
    exact (le_inf le_normalizer_of_normal hnW).trans inf_normalizer_le_normalizer_inf
  apply Set.Subset.antisymm
  · intro i hi
    have hi' : i⁻¹ ∈ N ⊔ normalizer (Q : Set G) := by
      rw [sup_comm]
      exact hfr (mem_sup_left (I.inv_mem hi))
    have hiProd : i⁻¹ ∈ (N : Set G) * (normalizer (Q : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left N _ hnormN]
      exact hi'
    obtain ⟨n, hn, u, hu, hnu⟩ := hiProd
    change n * u = i⁻¹ at hnu
    obtain ⟨j, hj, q, hq, hjq⟩ := mem_sup_of_normal_left.mp hn.2
    have hjK : j ∈ K := by
      have := K.mul_mem hn.1 (K.inv_mem (hQK hq))
      rwa [← hjq, mul_inv_cancel_right] at this
    have hqu : q * u ∈ normalizer (Q : Set G) := mul_mem (Q.le_normalizer hq) hu
    have hquI : q * u ∈ I := by
      have := I.mul_mem (I.inv_mem hj) (I.inv_mem hi)
      rw [← hnu, ← hjq] at this
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using this
    refine ⟨(q * u)⁻¹, ⟨I.inv_mem hquI, inv_mem hqu⟩, j⁻¹,
      ⟨I.inv_mem hj, K.inv_mem hjK⟩, ?_⟩
    have he : j * (q * u) = i⁻¹ := by rw [← mul_assoc, hjq, hnu]
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv he
  · rintro i ⟨n, hn, k, hk, rfl⟩
    exact I.mul_mem hn.1 hk.1

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent

/-- The inverse image of `C_{G_E/E}(V_E/E)` in the original `G_E`. -/
def sectionKernel (V E : Subgroup G) : Subgroup G :=
  (centralizerModulo ⊤ ((lineV V E).subgroupOf (lineNormalizer E))
    (E.subgroupOf (lineNormalizer E))).map (lineNormalizer E).subtype

/-- The source `C_I(V_E/E)`, using the original `I = J(C_G(E))`. -/
noncomputable def thompsonKernel (V E : Subgroup G) : Subgroup G := lineI E ⊓ sectionKernel V E

/-- The quotient-centralizer kernel belongs to the original line normalizer. -/
theorem sectionKernel_le (V E : Subgroup G) : sectionKernel V E ≤ lineNormalizer E :=
  map_subtype_le _

/-- The actual quotient centralizer has the expected ambient commutator criterion. -/
theorem mem_sectionKernel_iff (V E : Subgroup G)
    (hV : lineV V E ≤ lineNormalizer E) (x : G) :
    x ∈ sectionKernel V E ↔ x ∈ lineNormalizer E ∧ ∀ v ∈ lineV V E, ⁅v, x⁆ ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨_, hc⟩ := mem_centralizerModulo_iff.mp hy
    exact ⟨y.property, fun v hv => hc ⟨v, hV hv⟩ hv⟩
  · rintro ⟨hx, hc⟩
    refine mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    exact mem_centralizerModulo_iff.mpr ⟨mem_top _, fun v hv => hc v hv⟩

/-- Normality of the line span makes its quotient-action kernel relatively normal. -/
theorem sectionKernel_normal (V E : Subgroup G) [IsMulCommutative V] (hEV : E ≤ V) :
    ((sectionKernel V E).subgroupOf (lineNormalizer E)).Normal := by
  let H := lineNormalizer E
  let A := (lineV V E).subgroupOf H
  let N := E.subgroupOf H
  let : A.Normal := lineV_normal_in_lineNormalizer V E hEV
  let f := QuotientGroup.mk' N
  let : (A.map f).Normal := Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective N)
  change ((centralizerModulo ⊤ A N).map H.subtype |>.comap H.subtype).Normal
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  dsimp only [centralizerModulo]
  infer_instance

/-- The source `C_T(V_E/E)` is the Sylow intersection with the full kernel. -/
theorem quotientCentralizer_eq_inf (T V E : Subgroup G)
    (hV : lineV V E ≤ lineNormalizer E) :
    lineQuotientCentralizer T V E = T ⊓ sectionKernel V E := by
  ext x
  rw [mem_lineQuotientCentralizer_iff T V E hV, mem_inf, mem_sectionKernel_iff V E hV]
  simp only [lineT, mem_inf, and_assoc]

/-- Trivial action modulo `E ≤ V` stabilizes `V`. -/
theorem thompsonKernel_le_normalizer (V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) : thompsonKernel V E ≤ lineI E ⊓ normalizer (V : Set G) := by
  refine le_inf inf_le_left ?_
  intro x hx
  have hc := ((mem_sectionKernel_iff V E (lineV_le_lineNormalizer V E hEV) x).mp hx.2).2
  have hc' := ((mem_sectionKernel_iff V E (lineV_le_lineNormalizer V E hEV) x⁻¹).mp
    ((sectionKernel V E).inv_mem hx.2)).2
  intro v
  constructor
  · intro hv
    have h := V.mul_mem (V.inv_mem (hEV (hc v (le_conjugateSpanBy V _ hv)))) hv
    convert h using 1
    group
    rfl
  · intro hv
    have h := V.mul_mem (V.inv_mem (hEV (hc' (x * v * x⁻¹)
      (le_conjugateSpanBy V _ hv)))) hv
    convert h using 1
    group
    rfl

/-- The earlier normalizer bound confines the whole `N_I(V)` to `M_E`. -/
theorem thompsonNormalizer_le_lineM (M V E : Subgroup G)
    (hNM : normalizer (V : Set G) ≤ M) :
    lineI E ⊓ normalizer (V : Set G) ≤ lineM M E :=
  le_inf (inf_le_right.trans hNM) (inf_le_left.trans (lineI_le_lineNormalizer E))

/-- The earlier normalizer bound puts the correction subgroup in `M_E`. -/
theorem thompsonKernel_le_lineM (M V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (hNM : normalizer (V : Set G) ≤ M) :
    thompsonKernel V E ≤ lineM M E :=
  (thompsonKernel_le_normalizer V E hEV).trans (thompsonNormalizer_le_lineM M V E hNM)


/-- The Frattini correction after dropping the temporary assumption on p.1154. -/
theorem frattini_correction [Finite G] (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    (lineI E : Set G) = (lineI0 T V E : Set G) * (thompsonKernel V E : Set G) := by
  let H := lineNormalizer E
  let K := (sectionKernel V E).subgroupOf H
  let J := (lineI E).subgroupOf H
  let : K.Normal := sectionKernel_normal V E hEV
  let : J.Normal := lineI_normal_in_lineNormalizer E
  obtain ⟨P, hP⟩ := U.exists_sylow_map_eq_inf_of_normal K
  have hmap : ((P : Subgroup K).map K.subtype).map H.subtype =
      lineQuotientCentralizer T V E := by
    rw [hP, map_inf _ _ _ H.subtype_injective, hU,
      map_subgroupOf_eq_of_le (sectionKernel_le V E),
      quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
    rw [lineT, inf_assoc, inf_of_le_right (sectionKernel_le V E)]
  have hfr := normal_frattini J K P
  apply Set.Subset.antisymm
  · intro i hi
    let iH : H := ⟨i, lineI_le_lineNormalizer E hi⟩
    have hiJ : iH ∈ (J : Set H) := hi
    rw [hfr] at hiJ
    obtain ⟨n, hn, k, hk, hnk⟩ := hiJ
    have hnN : (n : G) ∈ normalizer (lineQuotientCentralizer T V E : Set G) := by
      rw [← hmap]
      exact ((P : Subgroup K).map K.subtype).le_normalizer_map H.subtype
        (mem_map.mpr ⟨n, hn.2, rfl⟩)
    exact ⟨n, ⟨hn.1, hnN⟩, k, ⟨hk.1, hk.2⟩, congrArg Subtype.val hnk⟩
  · rintro i ⟨n, hn, k, hk, rfl⟩
    exact (lineI E).mul_mem hn.1 hk.1


/-- Absorb the correction subgroup in `M_E`, retaining the original `G_E`. -/
theorem original_product [Finite G] (M T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hNM : normalizer (V : Set G) ≤ M)
    (hprod : (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI E : Set G)) :
    (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI0 T V E : Set G) := by
  apply Set.Subset.antisymm
  · intro g hg
    rw [hprod] at hg
    obtain ⟨m, hm, i, hi, hmi⟩ := hg
    have hi' : i⁻¹ ∈ (lineI0 T V E : Set G) * (thompsonKernel V E : Set G) := by
      rw [← frattini_correction T V E hEV U hU]
      exact (lineI E).inv_mem hi
    obtain ⟨n, hn, k, hk, hnk⟩ := hi'
    have he : i = k⁻¹ * n⁻¹ := by simpa only [mul_inv_rev, inv_inv] using
      (congrArg Inv.inv hnk).symm
    refine ⟨m * k⁻¹, (lineM M E).mul_mem hm
      ((lineM M E).inv_mem (thompsonKernel_le_lineM M V E hEV hNM hk)),
      n⁻¹, (lineI0 T V E).inv_mem hn, ?_⟩
    change m * k⁻¹ * n⁻¹ = g
    rw [mul_assoc, ← he]
    exact hmi
  · rintro g ⟨m, hm, i, hi, rfl⟩
    exact (lineNormalizer E).mul_mem hm.2 (lineI_le_lineNormalizer E hi.1)

private theorem relative_index_of_product (A B H : Subgroup G) (hBH : B ≤ H)
    (hprod : (H : Set G) = (A : Set G) * (B : Set G)) :
    A.relIndex H = A.relIndex B := by
  let f : (B ⧸ A.subgroupOf B) → (H ⧸ A.subgroupOf H) :=
    Quotient.map (inclusion hBH) (by
      intro a b h
      apply QuotientGroup.leftRel_apply.mpr
      have h' := (QuotientGroup.leftRel_apply (s := A.subgroupOf B)).mp h
      exact h')
  have hf : Function.Injective f := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        intro h
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        have he : ((inclusion hBH a : H) : H ⧸ A.subgroupOf H) =
            ((inclusion hBH b : H) : H ⧸ A.subgroupOf H) := h
        have h' := QuotientGroup.eq.mp he
        exact h'
  have hs : Function.Surjective f := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      have hx : (x : G)⁻¹ ∈ (A : Set G) * (B : Set G) := by
        rw [← hprod]
        exact H.inv_mem x.property
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      refine ⟨Quotient.mk _ (⟨b⁻¹, B.inv_mem hb⟩ : B), ?_⟩
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change (b⁻¹)⁻¹ * (x : G) ∈ A
      have he : b * (x : G) = a⁻¹ := by
        have he' : a * b = (x : G)⁻¹ := hab
        rw [← inv_inj, mul_inv_rev, inv_inv, ← he']
        group
      simpa only [inv_inv, he] using A.inv_mem ha
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)).symm

/-- Transport the recognized index in `I₀` to the original line normalizer. -/
theorem original_index_three [Finite G] (M T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hNM : normalizer (V : Set G) ≤ M)
    (hprod : (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI E : Set G))
    (hindex : (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3) :
    (lineM M E).relIndex (lineNormalizer E) = 3 := by
  rw [inf_relIndex_left] at hindex
  exact (relative_index_of_product (lineM M E) (lineI0 T V E) (lineNormalizer E)
    (inf_le_left.trans (lineI_le_lineNormalizer E))
    (original_product M T V E hEV U hU hNM hprod)).trans hindex

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
