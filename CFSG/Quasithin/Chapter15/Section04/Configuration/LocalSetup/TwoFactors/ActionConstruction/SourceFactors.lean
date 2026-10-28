module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal.Fixed
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Fixed lines of the Section 15.4 source factors

The single-factor omega decomposition identifies the printed `E_Y` with
`C_E(Y)` and gives its index two. In the double case the index four and a
conjugation exchanging the invariant summands force each fixed line to have
order two: their orders are equal and their product is four. The resulting
coordinates use the actual subgroups `[V(M),Y_i]`, with the conjugation formula
and exact kernel supplied by `Coordinates`.

The fixed decompositions in the mixed argument follow from a small-module
calculation. A nontrivial invariant subgroup of a fixed-point-free group of
order four is the whole group: an invariant subgroup of order two would be
centralized. This identifies `[E,Y_i]`, its intersection with `E`, and the
order-four intersection `[E,X] ∩ E`. Relative normality of the source factors
implies their cross-centralization on the disjoint commutator modules.

The source factor permutation, its nontriviality on `T`, and the residual
construction of the factors remain explicit inputs to be realized from the
preceding source witnesses. These conditional lemmas do not assert completion
of 15.4.14 or 15.4.18, and define neither a replacement family nor new factors.
In particular, they never assert that the chosen `Y₂` is `T`-invariant or belongs
to the source family.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.12(5–6), 15.4.14, and the first two paragraphs
of 15.4.18, printed pp.1160–1162. The factor action is traced in the source to
E.2.3(1–2), printed pp.216–217.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors
variable {G : Type*} [Group G]

/-- The Sylow subgroup normalizes its exact Baumann subgroup. -/
theorem baumann_normalized (T : Subgroup G) :
    T ≤ normalizer (ChapterB.baumann T : Set G) := by
  exact (le_inf T.le_normalizer
    ((MixedLocal.normalizes_alpha T).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

/-- The printed fixed summand is normalized by `T`; the two-core is taken inside `YT`. -/
theorem omega_core_fixed_normalized {T Y : Subgroup G}
    (hY : T ≤ normalizer (Y : Set G)) :
    T ≤ normalizer ((Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2) ⊓
      centralizer (Y : Set G) : Subgroup G) : Set G) := by
  have hcore : T ≤ normalizer ((Y ⊔ T).pCoreIn 2 : Set G) := by
    exact le_sup_right.trans ((Y ⊔ T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (Y ⊔ T) (pCore 2 (Y ⊔ T : Subgroup G))))
  have hU : T ≤ normalizer (Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2) : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2)).map
      (MulAut.conj t).toMonoidHom = _
    have hQ : ((Y ⊔ T).pCoreIn 2).map (MulAut.conj t).toMonoidHom = (Y ⊔ T).pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp (hcore ht)
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective,
      hQ]
  exact (le_inf hU (hY.trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf

/-- Relative invariance of a factor and the ambient module preserves their commutator. -/
theorem commutator_factors_normalized {S V Y : Subgroup G}
    (hV : S ≤ normalizer (V : Set G)) (hY : S ≤ normalizer (Y : Set G)) :
    S ≤ normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hv : V.map (MulAut.conj s).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp (hV hs)
  have hy : Y.map (MulAut.conj s).toMonoidHom = Y := mem_normalizer_iff_map_conj_eq.mp (hY hs)
  change (⁅V, Y⁆ : Subgroup G).map (MulAut.conj s).toMonoidHom = _
  rw [map_commutator, hv, hy]

/-- Conjugation of the actual group factor transports its actual commutator module. -/
theorem map_commutator_factor {V Y Y' : Subgroup G} {t : G}
    (hV : t ∈ normalizer (V : Set G))
    (hY : Y.map (MulAut.conj t).toMonoidHom = Y') :
    ⁅V, Y⁆.map (MulAut.conj t).toMonoidHom = ⁅V, Y'⁆ := by
  have hv : V.map (MulAut.conj t).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp hV
  rw [map_commutator, hv, hY]

/-- A nontrivial action on the unordered pair interchanges both factors. -/
theorem swap_of_pair_invariant {T V₁ V₂ : Subgroup G}
    (hp : ∀ t ∈ T, ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)),
      V.map (MulAut.conj t).toMonoidHom ∈ ({V₁, V₂} : Set (Subgroup G)))
    (hn : ¬ T ≤ normalizer (V₁ : Set G)) :
    ∃ t ∈ T, V₁.map (MulAut.conj t).toMonoidHom = V₂ ∧
      V₂.map (MulAut.conj t).toMonoidHom = V₁ := by
  classical
  obtain ⟨t, ht, hnt⟩ := Set.not_subset.mp hn
  have h₁ : V₁.map (MulAut.conj t).toMonoidHom = V₂ := by
    have h := hp t ht V₁ (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h.resolve_left (fun he => hnt (mem_normalizer_iff_map_conj_eq.mpr he))
  have h₂ : V₂.map (MulAut.conj t).toMonoidHom = V₁ := by
    have h := hp t ht V₂ (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    refine h.resolve_right ?_
    intro he
    have heq : V₁ = V₂ := Subgroup.map_injective (MulAut.conj t).injective (h₁.trans he.symm)
    exact hnt (mem_normalizer_iff_map_conj_eq.mpr (h₁.trans heq.symm))
  exact ⟨t, ht, h₁, h₂⟩

private theorem card_complement [Finite G] {C F E : Subgroup G}
    (hE : C ⊔ F = E) (hd : Disjoint C F)
    (hc : C ≤ centralizer (F : Set G)) : Nat.card F = C.relIndex E := by
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C F hd hc
  have hcard : Nat.card E = Nat.card C * Nat.card F := by
    rw [← hE, ← Nat.card_congr e.toEquiv, Nat.card_prod]
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) C E bot_le (hE ▸ le_sup_left)
  rw [relIndex_bot_left, relIndex_bot_left, hcard] at hi
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hi).symm

/-- The printed index four and exchange of the invariant factors force two fixed lines. -/
theorem fixed_line_orders_of_swap [Finite G]
    {C E V₁ V₂ S : Subgroup G}
    (hE : C ⊔ ((V₁ ⊔ V₂) ⊓ centralizer (S : Set G)) = E)
    (hd₀ : Disjoint C (V₁ ⊔ V₂)) (hd₁₂ : Disjoint V₁ V₂)
    (hc₀ : C ≤ centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G))
    (hc₁₂ : V₁ ≤ centralizer (V₂ : Set G))
    (hn₁ : S ≤ normalizer (V₁ : Set G)) (hn₂ : S ≤ normalizer (V₂ : Set G))
    (hi : C.relIndex E = 4) {t : G} (hnS : t ∈ normalizer (S : Set G))
    (hs : V₁.map (MulAut.conj t).toMonoidHom = V₂) :
    Nat.card (V₁ ⊓ centralizer (S : Set G) : Subgroup G) = 2 ∧
      Nat.card (V₂ ⊓ centralizer (S : Set G) : Subgroup G) = 2 := by
  have hsplit := fixed_subgroup_split_of_internal_factors hd₁₂ hc₁₂ hn₁ hn₂
  have hcard := card_complement hE (hd₀.mono_right inf_le_left)
    (hc₀.trans (centralizer_le inf_le_left))
  rw [hi, hsplit] at hcard
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (V₁ ⊓ centralizer (S : Set G)) (V₂ ⊓ centralizer (S : Set G))
    (hd₁₂.mono inf_le_left inf_le_left)
    (inf_le_left.trans (hc₁₂.trans (centralizer_le inf_le_left)))
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod] at hcard
  have heq : Nat.card (V₁ ⊓ centralizer (S : Set G) : Subgroup G) =
      Nat.card (V₂ ⊓ centralizer (S : Set G) : Subgroup G) := by
    rw [← map_fixed_subgroup_of_normalizes hnS hs,
      Subgroup.card_map_of_injective (MulAut.conj t).injective]
  constructor <;> nlinarith

/-- Identify the printed fixed summand and obtain the single coordinate alternative. -/
theorem single_coordinate_of_omega_decomposition [Finite G]
    {E Y C V S U : Subgroup G} [IsMulCommutative U]
    (hC : C = U ⊓ centralizer (Y : Set G)) (hVU : V ≤ U)
    (hE : C ⊔ (V ⊓ centralizer (S : Set G)) = E)
    (hd : Disjoint C V) (hi : C.relIndex E = 2) :
    E ⊓ centralizer (Y : Set G) = C ∧
      (E ⊓ centralizer (Y : Set G)).relIndex E = 2 := by
  have hCY : C ≤ centralizer (Y : Set G) := hC ▸ inf_le_right
  have hc : C ≤ centralizer ((V ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
    intro c hc v hv
    exact setLike_mul_comm (hVU hv.1) ((hC ▸ inf_le_left : C ≤ U) hc)
  have hVF : (V ⊓ centralizer (S : Set G)) ⊓ centralizer (Y : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hvC : v ∈ C := hC ▸ (show v ∈ U ⊓ centralizer (Y : Set G) from ⟨hVU hv.1.1, hv.2⟩)
    exact (disjoint_iff.mp hd).le ⟨hvC, hv.1.1⟩
  have he := fixed_summand_eq_centralizer hE hc hCY hVF
  exact ⟨he, he ▸ hi⟩

/-- Construct the double coordinate alternative from the preceding decomposition and the factor permutation. All three required normalizations and both fixed-line orders are derived. -/
theorem double_coordinates_of_factor_pair [Finite G]
    (T Y V Y₁ Y₂ : Subgroup G)
    (hTY : T ≤ normalizer (Y : Set G)) (hTV : T ≤ normalizer (V : Set G))
    (hS₁ : ChapterB.baumann T ≤ normalizer (Y₁ : Set G))
    (hS₂ : ChapterB.baumann T ≤ normalizer (Y₂ : Set G))
    (hpair : ∀ t ∈ T, ∀ L ∈ ({Y₁, Y₂} : Set (Subgroup G)),
      L.map (MulAut.conj t).toMonoidHom ∈ ({Y₁, Y₂} : Set (Subgroup G)))
    (hmoved : ¬ T ≤ normalizer (Y₁ : Set G))
    (hVU : ⁅V, Y₁⁆ ⊔ ⁅V, Y₂⁆ ≤ Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2))
    (hE : (Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2) ⊓ centralizer (Y : Set G)) ⊔
      ((⁅V, Y₁⁆ ⊔ ⁅V, Y₂⁆) ⊓ centralizer (ChapterB.baumann T : Set G)) = ChapterB.thompsonAlpha T)
    (hd₀ : Disjoint (Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2) ⊓
      centralizer (Y : Set G)) (⁅V, Y₁⁆ ⊔ ⁅V, Y₂⁆))
    (hd₁₂ : Disjoint ⁅V, Y₁⁆ ⁅V, Y₂⁆)
    (hi : (Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2) ⊓
      centralizer (Y : Set G)).relIndex (ChapterB.thompsonAlpha T) = 4) :
    ChapterB.thompsonAlpha T ⊓ centralizer (Y : Set G) =
        Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2) ⊓ centralizer (Y : Set G) ∧
      Nat.card (⁅V, Y₁⁆ ⊓ centralizer (ChapterB.baumann T : Set G) : Subgroup G) = 2 ∧
      Nat.card (⁅V, Y₂⁆ ⊓ centralizer (ChapterB.baumann T : Set G) : Subgroup G) = 2 ∧
      Nonempty (SwappedBinaryQuotient (ChapterB.thompsonAlpha T) T Y) := by
  let U := Stellmacher.omegaOneCenterAmbient ((Y ⊔ T).pCoreIn 2)
  let C := U ⊓ centralizer (Y : Set G)
  let : IsElementaryAbelian 2 U := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hc₀ : C ≤ centralizer ((⁅V, Y₁⁆ ⊔ ⁅V, Y₂⁆ : Subgroup G) : Set G) := by
    intro c hc v hv
    exact setLike_mul_comm (hVU hv) hc.1
  have hc₁₂ : ⁅V, Y₁⁆ ≤ centralizer ((⁅V, Y₂⁆ : Subgroup G) : Set G) := by
    intro a ha b hb
    exact setLike_mul_comm (hVU (mem_sup_right hb)) (hVU (mem_sup_left ha))
  have hn₁ := commutator_factors_normalized (inf_le_left.trans hTV) hS₁
  have hn₂ := commutator_factors_normalized (inf_le_left.trans hTV) hS₂
  obtain ⟨t, ht, hs₁, hs₂⟩ := swap_of_pair_invariant hpair hmoved
  have hv₁ := map_commutator_factor (hTV ht) hs₁
  have hv₂ := map_commutator_factor (hTV ht) hs₂
  have hnE := MixedLocal.normalizes_alpha T ht
  have hnC := omega_core_fixed_normalized hTY ht
  have hnS := baumann_normalized T ht
  obtain ⟨hc₁, hc₂⟩ := fixed_line_orders_of_swap hE hd₀ hd₁₂ hc₀ hc₁₂ hn₁ hn₂ hi hnS hv₁
  obtain ⟨hfix, hq⟩ := swappedBinaryQuotient_of_omega_decomposition
    (U := U) rfl hVU hE hd₀ hd₁₂ hn₁ hn₂ hc₁ hc₂ t ht hnE hnC hnS hv₁ hv₂
  exact ⟨hfix, hc₁, hc₂, hq⟩

/-- A saturated moved module intersects `E` in exactly its displayed complement. -/
theorem moved_intersection_of_saturation {E C F V Y U : Subgroup G}
    [IsMulCommutative U] (hCU : C ≤ U) (hVU : V ≤ U)
    (hE : C ⊔ F = E) (hFV : F ≤ V) (hd : Disjoint C V)
    (hsat : ⁅E, Y⁆ = V) : ⁅E, Y⁆ ⊓ E = F := by
  have hc : C ≤ centralizer (F : Set G) := by
    intro c hc f hf
    exact setLike_mul_comm (hVU (hFV hf)) (hCU hc)
  rw [hsat]
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (C : Set G) * (F : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right C F
        (hc.trans (Subgroup.centralizer_le_normalizer _))]
      exact hE.symm ▸ hx.2
    obtain ⟨c, hcC, f, hf, rfl⟩ := hxprod
    have hcV : c ∈ V := by
      simpa only [mul_inv_cancel_right] using V.mul_mem hx.1 (V.inv_mem (hFV hf))
    have hc1 : c = 1 := mem_bot.mp ((disjoint_iff.mp hd).le ⟨hcC, hcV⟩)
    change c * f ∈ F
    rw [hc1, one_mul]
    exact hf
  · exact le_inf hFV (hE ▸ le_sup_right)

/-- Identify both factors of the fixed/moved decomposition from module saturation. -/
theorem fixed_decomposition_of_saturation {E C F V Y U : Subgroup G}
    [IsMulCommutative U] (hCU : C ≤ U) (hVU : V ≤ U)
    (hE : C ⊔ F = E) (hFV : F ≤ V) (hd : Disjoint C V)
    (hCY : C ≤ centralizer (Y : Set G))
    (hVY : V ⊓ centralizer (Y : Set G) = ⊥) (hsat : ⁅E, Y⁆ = V) :
    E ⊓ centralizer (Y : Set G) = C ∧ ⁅E, Y⁆ ⊓ E = F ∧
      (E ⊓ centralizer (Y : Set G)) ⊔ (⁅E, Y⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (Y : Set G)) (⁅E, Y⁆ ⊓ E) := by
  have hc : C ≤ centralizer (F : Set G) := by
    intro c hc f hf
    exact setLike_mul_comm (hVU (hFV hf)) (hCU hc)
  have hfix := fixed_summand_eq_centralizer hE hc hCY
    (le_bot_iff.mp ((inf_le_inf_right _ hFV).trans hVY.le))
  have hline := moved_intersection_of_saturation hCU hVU hE hFV hd hsat
  exact ⟨hfix, hline, by rwa [hfix, hline], by rw [hfix, hline]; exact hd.mono_right hFV⟩

private theorem centralizes_of_card_two {K Y : Subgroup G}
    (hcard : Nat.card K = 2) (hn : Y ≤ normalizer (K : Set G)) :
    K ≤ centralizer (Y : Set G) := by
  let N := normalizer (K : Set G)
  let K' := K.subgroupOf N
  let : K'.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  have hc : Nat.card K' = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe K.le_normalizer).toEquiv).trans hcard
  have hcentral := central_of_normal_card_two K' hc
  intro k hk y hy
  exact congrArg Subtype.val ((mem_center_iff.mp
    (hcentral (show (⟨k, K.le_normalizer hk⟩ : N) ∈ K' from hk))) ⟨y, hn hy⟩)

/-- A nonzero part of a fixed-point-free module of order four generates the full commutator module. -/
theorem four_module_saturation [Finite G] {E F V Y : Subgroup G}
    (hFV : F ≤ V) (hFE : F ≤ E) (hF : F ≠ ⊥) (hV : Nat.card V = 4)
    (hfix : V ⊓ centralizer (Y : Set G) = ⊥) (hbound : ⁅E, Y⁆ ≤ V) :
    ⁅E, Y⁆ = V := by
  have hne : ⁅E, Y⁆ ≠ ⊥ := by
    intro he
    have hcentral := commutator_eq_bot_iff_le_centralizer.mp he
    apply hF
    exact le_bot_iff.mp ((le_inf hFV (hFE.trans hcentral)).trans hfix.le)
  have hcge := one_lt_card_iff_ne_bot (⁅E, Y⁆ : Subgroup G) |>.mpr hne
  have hdvd : Nat.card (⁅E, Y⁆ : Subgroup G) ∣ 4 := hV ▸ card_dvd_of_le hbound
  have hcle : Nat.card (⁅E, Y⁆ : Subgroup G) ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hcnot : Nat.card (⁅E, Y⁆ : Subgroup G) ≠ 2 := by
    intro hc
    have hcentral := centralizes_of_card_two hc (normalizer_commutator_ge_right E Y)
    exact hne (le_bot_iff.mp ((le_inf hbound hcentral).trans hfix.le))
  have hcard : Nat.card (⁅E, Y⁆ : Subgroup G) = 4 := by
    have hc : Nat.card (⁅E, Y⁆ : Subgroup G) = 3 ∨ Nat.card (⁅E, Y⁆ : Subgroup G) = 4 := by omega
    rcases hc with hc | hc
    · norm_num [hc] at hdvd
    · exact hc
  exact eq_of_le_of_card_ge hbound (by rw [hcard, hV])

private theorem commutator_bound_of_fixed_complement {E C F V Y : Subgroup G}
    (hE : C ⊔ F = E) (hFV : F ≤ V) (hCF : C ≤ centralizer (F : Set G))
    (hCV : C ≤ normalizer (V : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hYV : Y ≤ normalizer (V : Set G)) : ⁅E, Y⁆ ≤ V := by
  apply commutator_le.mpr
  intro e he y hy
  have heprod : e ∈ (C : Set G) * (F : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right C F
      (hCF.trans (Subgroup.centralizer_le_normalizer _))]
    exact hE.symm ▸ he
  obtain ⟨c, hc, f, hf, rfl⟩ := heprod
  have hfy : ⁅f, y⁆ ∈ V := (le_normalizer_iff_commutator_le_left.mp hYV)
    (commutator_mem_commutator (hFV hf) hy)
  have hcy : ⁅c, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr ((hCY hc y hy).symm)
  rw [commutatorElement_mul_left_eq_conj_mul, hcy, mul_one]
  exact (mem_normalizer_iff.mp (hCV hc) _).mp hfy

/-- Derive the genuine commutator-intersection line and its direct complement in `E`. -/
theorem fixed_decomposition_of_four_module [Finite G]
    {E C F V Y U : Subgroup G} [IsMulCommutative U]
    (hCU : C ≤ U) (hVU : V ≤ U) (hE : C ⊔ F = E) (hFV : F ≤ V)
    (hd : Disjoint C V) (hCY : C ≤ centralizer (Y : Set G))
    (hVY : V ⊓ centralizer (Y : Set G) = ⊥)
    (hVcard : Nat.card V = 4) (hFcard : Nat.card F = 2)
    (hYV : Y ≤ normalizer (V : Set G)) :
    E ⊓ centralizer (Y : Set G) = C ∧ ⁅E, Y⁆ ⊓ E = F ∧
      (E ⊓ centralizer (Y : Set G)) ⊔ (⁅E, Y⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (Y : Set G)) (⁅E, Y⁆ ⊓ E) ∧
      Nat.card (⁅E, Y⁆ ⊓ E : Subgroup G) = 2 ∧ ⁅E, Y⁆ = V := by
  have hF : F ≠ ⊥ := by
    intro he
    have h1 := Subgroup.card_eq_one.mpr he
    omega
  have hc : C ≤ centralizer (V : Set G) := by
    intro c hc v hv
    exact setLike_mul_comm (hVU hv) (hCU hc)
  have hbound := commutator_bound_of_fixed_complement hE hFV
    (hc.trans (centralizer_le hFV)) (hc.trans (Subgroup.centralizer_le_normalizer _)) hCY hYV
  have hsat := four_module_saturation hFV (hE ▸ le_sup_right) hF hVcard hVY hbound
  obtain ⟨hfix, hline, hsplit, hdis⟩ :=
    fixed_decomposition_of_saturation hCU hVU hE hFV hd hCY hVY hsat
  exact ⟨hfix, hline, hsplit, hdis, hline ▸ hFcard, hsat⟩

/-- The single-factor source omega decomposition gives the mixed fixed decomposition, with the moved intersection of order two. -/
theorem single_fixed_decomposition [Finite G] {E C V Y S U : Subgroup G}
    [IsMulCommutative U]
    (hC : C = U ⊓ centralizer (Y : Set G)) (hVU : V ≤ U)
    (hE : C ⊔ (V ⊓ centralizer (S : Set G)) = E) (hd : Disjoint C V)
    (hi : C.relIndex E = 2) (hVcard : Nat.card V = 4)
    (hYV : Y ≤ normalizer (V : Set G)) :
    E ⊓ centralizer (Y : Set G) = C ∧
      ⁅E, Y⁆ ⊓ E = V ⊓ centralizer (S : Set G) ∧
      (E ⊓ centralizer (Y : Set G)) ⊔ (⁅E, Y⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (Y : Set G)) (⁅E, Y⁆ ⊓ E) ∧
      Nat.card (⁅E, Y⁆ ⊓ E : Subgroup G) = 2 := by
  have hCU : C ≤ U := hC ▸ inf_le_left
  have hCY : C ≤ centralizer (Y : Set G) := hC ▸ inf_le_right
  have hc : C ≤ centralizer ((V ⊓ centralizer (S : Set G) : Subgroup G) : Set G) := by
    intro c hc v hv
    exact setLike_mul_comm (hVU hv.1) (hCU hc)
  have hcard := (card_complement hE (hd.mono_right inf_le_left) hc).trans hi
  have hVY : V ⊓ centralizer (Y : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    exact (disjoint_iff.mp hd).le ⟨hC ▸ (show v ∈ U ⊓ centralizer (Y : Set G) from
      ⟨hVU hv.1, hv.2⟩), hv.1⟩
  obtain ⟨hfix, hline, hsplit, hdis, hcard, _⟩ :=
    fixed_decomposition_of_four_module hCU hVU hE inf_le_left hd hCY hVY hVcard hcard hYV
  exact ⟨hfix, hline, hsplit, hdis, hcard⟩

private theorem disjoint_regroup {C A B U : Subgroup G} [IsMulCommutative U]
    (hCU : C ≤ U) (hBU : B ≤ U)
    (hC : Disjoint C (A ⊔ B)) (hAB : Disjoint A B) : Disjoint (C ⊔ B) A := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  have hc : C ≤ centralizer (B : Set G) := by
    intro c hc b hb
    exact setLike_mul_comm (hBU hb) (hCU hc)
  have hxprod : x ∈ (C : Set G) * (B : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right C B
      (hc.trans (Subgroup.centralizer_le_normalizer _))]
    exact hx.1
  obtain ⟨c, hcC, b, hb, rfl⟩ := hxprod
  have hcAB : c ∈ A ⊔ B := by
    simpa only [mul_inv_cancel_right] using
      (A ⊔ B).mul_mem (mem_sup_left hx.2) ((A ⊔ B).inv_mem (mem_sup_right hb))
  have hc1 : c = 1 := mem_bot.mp ((disjoint_iff.mp hC).le ⟨hcC, hcAB⟩)
  have hbA : b ∈ A := by
    have hh : c * b ∈ A := hx.2
    rwa [hc1, one_mul] at hh
  have hb1 : b = 1 := mem_bot.mp ((disjoint_iff.mp hAB).le ⟨hbA, hb⟩)
  simp only [hc1, hb1, mul_one, mem_bot]

/-- Relative normality and disjointness force a factor to centralize its sibling module. -/
theorem factor_centralizes_sibling_module {V Y₁ Y₂ : Subgroup G}
    (hV : Y₁ ⊔ Y₂ ≤ normalizer (V : Set G))
    (hY₁ : Y₁ ⊔ Y₂ ≤ normalizer (Y₁ : Set G))
    (hd : Disjoint ⁅V, Y₁⁆ ⁅V, Y₂⁆) :
    ⁅V, Y₁⁆ ≤ centralizer (Y₂ : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  have hV₁ : ⁅V, Y₁⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hV)
  have hn : Y₂ ≤ normalizer ((⁅V, Y₁⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans (commutator_factors_normalized hV hY₁)
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hn)
    (commutator_mono hV₁ le_rfl)).trans (disjoint_iff.mp hd).le

private theorem fixed_trivial_of_cross {C V U A B : Subgroup G}
    (hC : C = U ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G))
    (hVU : V ≤ U) (hd : Disjoint C V) (hcross : V ≤ centralizer (B : Set G)) :
    V ⊓ centralizer (A : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have hcentral : v ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    have ha : A ≤ centralizer ({v} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (hv.2 a ha)
    have hb : B ≤ centralizer ({v} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hcross hv.1 b hb)
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((sup_le ha hb) hx)
  exact (disjoint_iff.mp hd).le ⟨hC ▸ (show v ∈ U ⊓ centralizer ((A ⊔ B : Subgroup G) : Set G) from
    ⟨hVU hv.1, hcentral⟩), hv.1⟩

/-- Regroup the double decomposition to obtain both single fixed complements and the actual whole commutator-intersection subgroup of order four. -/
theorem double_factor_fixed_decomposition [Finite G]
    {E C V₁ V₂ F₁ F₂ Y₁ Y₂ U : Subgroup G} [IsMulCommutative U]
    (hC : C = U ⊓ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G))
    (hVU : V₁ ⊔ V₂ ≤ U) (hE : C ⊔ (F₁ ⊔ F₂) = E)
    (hF₁ : F₁ ≤ V₁) (hF₂ : F₂ ≤ V₂)
    (hd₀ : Disjoint C (V₁ ⊔ V₂)) (hd₁₂ : Disjoint V₁ V₂)
    (hc₁₂ : V₁ ≤ centralizer (Y₂ : Set G)) (hc₂₁ : V₂ ≤ centralizer (Y₁ : Set G))
    (hn₁ : Y₁ ≤ normalizer (V₁ : Set G)) (hn₂ : Y₂ ≤ normalizer (V₂ : Set G))
    (hv₁ : Nat.card V₁ = 4) (hv₂ : Nat.card V₂ = 4)
    (hf₁ : Nat.card F₁ = 2) (hf₂ : Nat.card F₂ = 2) :
    (E ⊓ centralizer (Y₁ : Set G)) ⊔ (⁅E, Y₁⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (Y₁ : Set G)) (⁅E, Y₁⁆ ⊓ E) ∧
      Nat.card (⁅E, Y₁⁆ ⊓ E : Subgroup G) = 2 ∧
      (E ⊓ centralizer (Y₂ : Set G)) ⊔ (⁅E, Y₂⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (Y₂ : Set G)) (⁅E, Y₂⁆ ⊓ E) ∧
      Nat.card (⁅E, Y₂⁆ ⊓ E : Subgroup G) = 2 ∧
      (E ⊓ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G)) ⊔
        ((⁅E, Y₁⁆ ⊓ E) ⊔ (⁅E, Y₂⁆ ⊓ E)) = E ∧
      Disjoint (E ⊓ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G))
        ((⁅E, Y₁⁆ ⊓ E) ⊔ (⁅E, Y₂⁆ ⊓ E)) ∧
      Disjoint (⁅E, Y₁⁆ ⊓ E) (⁅E, Y₂⁆ ⊓ E) ∧
      ⁅E, Y₁ ⊔ Y₂⁆ ⊓ E = (⁅E, Y₁⁆ ⊓ E) ⊔ (⁅E, Y₂⁆ ⊓ E) ∧
      Nat.card (⁅E, Y₁ ⊔ Y₂⁆ ⊓ E : Subgroup G) = 4 := by
  have hCU : C ≤ U := hC ▸ inf_le_left
  have hCwhole : C ≤ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) := hC ▸ inf_le_right
  have hV₁U : V₁ ≤ U := le_sup_left.trans hVU
  have hV₂U : V₂ ≤ U := le_sup_right.trans hVU
  have hfix₁ := fixed_trivial_of_cross hC hV₁U (hd₀.mono_right le_sup_left) hc₁₂
  have hfix₂ := fixed_trivial_of_cross (A := Y₂) (B := Y₁) (by simpa only [sup_comm Y₂ Y₁] using hC)
    hV₂U (hd₀.mono_right le_sup_right) hc₂₁
  have hd₁ : Disjoint (C ⊔ F₂) V₁ :=
    (disjoint_regroup hCU hV₂U hd₀ hd₁₂).mono_left (sup_le_sup_left hF₂ C)
  have hd₂ : Disjoint (C ⊔ F₁) V₂ :=
    (disjoint_regroup hCU hV₁U (by simpa only [sup_comm] using hd₀) hd₁₂.symm).mono_left
      (sup_le_sup_left hF₁ C)
  have he₁ : (C ⊔ F₂) ⊔ F₁ = E := by simpa only [sup_assoc, sup_comm F₂ F₁] using hE
  have he₂ : (C ⊔ F₁) ⊔ F₂ = E := by simpa only [sup_assoc] using hE
  obtain ⟨_, hline₁, hs₁, hd₁, hcard₁, hsat₁⟩ := fixed_decomposition_of_four_module
    (sup_le hCU (hF₂.trans hV₂U)) hV₁U he₁ hF₁ hd₁
    (sup_le (hCwhole.trans (centralizer_le (fun _ hy => mem_sup_left hy))) (hF₂.trans hc₂₁)) hfix₁ hv₁ hf₁ hn₁
  obtain ⟨_, hline₂, hs₂, hd₂, hcard₂, hsat₂⟩ := fixed_decomposition_of_four_module
    (sup_le hCU (hF₁.trans hV₁U)) hV₂U he₂ hF₂ hd₂
    (sup_le (hCwhole.trans (centralizer_le (fun _ hy => mem_sup_right hy))) (hF₁.trans hc₁₂)) hfix₂ hv₂ hf₂ hn₂
  have hFF : F₁ ⊔ F₂ ≤ V₁ ⊔ V₂ := sup_le_sup hF₁ hF₂
  have hcf : C ≤ centralizer ((F₁ ⊔ F₂ : Subgroup G) : Set G) := by
    intro c hc f hf
    exact setLike_mul_comm (hVU (hFF hf)) (hCU hc)
  have hfixed : (F₁ ⊔ F₂) ⊓ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro f hf
    have hfC : f ∈ C := hC ▸ (show f ∈ U ⊓ centralizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) from
      ⟨hVU (hFF hf.1), hf.2⟩)
    exact (disjoint_iff.mp hd₀).le ⟨hfC, hFF hf.1⟩
  have hfixX := fixed_summand_eq_centralizer hE hcf hCwhole hfixed
  have hcw : C ≤ centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by
    intro c hc v hv
    exact setLike_mul_comm (hVU hv) (hCU hc)
  have hn : Y₁ ⊔ Y₂ ≤ normalizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by
    apply sup_le
    · exact (le_inf hn₁ ((le_centralizer_iff.mp hc₂₁).trans (Subgroup.centralizer_le_normalizer _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup V₁ V₂)
    · exact (le_inf ((le_centralizer_iff.mp hc₁₂).trans (Subgroup.centralizer_le_normalizer _)) hn₂).trans
        (normalizer_inf_normalizer_le_normalizer_sup V₁ V₂)
  have hsat : ⁅E, Y₁ ⊔ Y₂⁆ = V₁ ⊔ V₂ := by
    apply le_antisymm (commutator_bound_of_fixed_complement hE hFF hcf
      (hcw.trans (Subgroup.centralizer_le_normalizer _)) hCwhole hn)
    rw [← hsat₁, ← hsat₂]
    exact sup_le (commutator_mono le_rfl le_sup_left) (commutator_mono le_rfl le_sup_right)
  have hwhole := moved_intersection_of_saturation hCU hVU hE hFF hd₀ hsat
  have hcardwhole : Nat.card (F₁ ⊔ F₂ : Subgroup G) = 4 := by
    have hc : F₁ ≤ centralizer (F₂ : Set G) := by
      intro a ha b hb
      exact setLike_mul_comm (hV₂U (hF₂ hb)) (hV₁U (hF₁ ha))
    obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting F₁ F₂
      (hd₁₂.mono hF₁ hF₂) hc
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hf₁, hf₂]
  refine ⟨hs₁, hd₁, hcard₁, hs₂, hd₂, hcard₂, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hfixX, hline₁, hline₂]
  · rw [hfixX, hline₁, hline₂]
    exact hd₀.mono_right hFF
  · rw [hline₁, hline₂]
    exact hd₁₂.mono hF₁ hF₂
  · rwa [hline₁, hline₂]
  · rwa [hwhole]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors
