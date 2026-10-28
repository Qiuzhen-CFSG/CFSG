module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Terminal
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Faithful transport of the Hall--Janko moved subgroup

The earlier normalizer identity makes [V,Y₊] normal in M ∩ I. Centrality
of V in O₂(Y₊S) makes O₂(Y₊) act trivially on V. Schur--Zassenhaus and
coprime action then show that [V,Y₊] meets C_G(L) trivially. Thus its
order is preserved by the actual map I → Aut(J₂), even though this map
need not be injective on V.

The same map has a two-group kernel, so it preserves the local two-core.
Consequently the image of the moved subgroup lies in the center of that
core. The original dichotomy makes its order either four or sixteen; an
order-four upper bound for the model center therefore suffices. No local
J₂ calculation or source classification is asserted by this module.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.42, printed p.1138, using 15.3.36(2) and 15.3.10.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction
variable {G : Type*} [Group G]
variable {I L M Y S V V₁ V₂ Yplus : Subgroup G} [(L.subgroupOf I).Normal]

/-- The theta identity places the residual inside the actual intersection. -/
theorem yplus_le_intersection (d : ComponentSetup I L M Yplus S) : Yplus ≤ M ⊓ I :=
  d.theta_eq ▸ theta_le _

/-- The chosen Sylow subgroup is contained in both local overgroups. -/
theorem sylow_le_intersection (d : ComponentSetup I L M Yplus S) : S ≤ M ⊓ I :=
  le_inf d.sylow_le_M (d.join_eq ▸ le_sup_right)

/-- The earlier relative normalizer equality gives the actor on Y₊. -/
theorem intersection_normalizes_yplus (d : ComponentSetup I L M Yplus S) :
    M ⊓ I ≤ normalizer (Yplus : Set G) := d.normalizer_eq ▸ inf_le_right

/-- The original M-action keeps the moved subgroup inside V. -/
theorem moved_le (d : ComponentSetup I L M Yplus S)
    (a : ActionSetup M Y S V V₁ V₂ Yplus) : ⁅V, Yplus⁆ ≤ V :=
  le_normalizer_iff_commutator_le_left.mp
    (((yplus_le_intersection d).trans inf_le_left).trans a.normalized)

/-- Both factors of the commutator are invariant under M ∩ I. -/
theorem intersection_normalizes_moved (d : ComponentSetup I L M Yplus S)
    (a : ActionSetup M Y S V V₁ V₂ Yplus) :
    M ⊓ I ≤ normalizer (⁅V, Yplus⁆ : Subgroup G) := by
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (a.normalized hx.1),
    mem_normalizer_iff_map_conj_eq.mp (intersection_normalizes_yplus d hx)]

/-- Normality here is relative to M ∩ I, not to G. -/
theorem moved_normal (d : ComponentSetup I L M Yplus S)
    (a : ActionSetup M Y S V V₁ V₂ Yplus) :
    ((⁅V, Yplus⁆ : Subgroup G).subgroupOf (M ⊓ I)).Normal :=
  normal_subgroupOf_of_le_normalizer (intersection_normalizes_moved d a)

/-- The two-core of the normal subgroup Y₊ lies in O₂(Y₊S). -/
theorem yplus_core_le_radical (d : ComponentSetup I L M Yplus S) :
    Yplus.pCoreIn 2 ≤ (Yplus ⊔ S : Subgroup G).pCoreIn 2 :=
  pCoreIn_mono_of_normalizes le_sup_left
    ((sup_le (yplus_le_intersection d) (sylow_le_intersection d)).trans
      (intersection_normalizes_yplus d))

/-- Centrality in the larger radical kills the two-core action. -/
theorem yplus_core_centralizes (d : ComponentSetup I L M Yplus S)
    (a : ActionSetup M Y S V V₁ V₂ Yplus) :
    Yplus.pCoreIn 2 ≤ centralizer (V : Set G) := by
  apply le_centralizer_iff.mp
  intro v hv q hq
  obtain ⟨z, hz, rfl⟩ := a.central_radical hv
  have hc := mem_center_iff.mp hz ⟨q, yplus_core_le_radical d hq⟩
  exact congrArg Subtype.val hc

/-- An odd complement has the same displacement on V as the whole Y₊. -/
theorem exists_coprime_moving_complement [Finite G]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus) :
    ∃ C : Subgroup G, C ≤ Yplus ∧ Nat.Coprime (Nat.card C) (Nat.card V) ∧
      ⁅V, C⁆ = ⁅V, Yplus⁆ := by
  have hq : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus) :=
    isPGroup_iff_pow_pow_eq_one.mpr fun x => ⟨1, by simpa using d.yplus_exponent x⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hq
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 (pCore 2 Yplus) from pCore_isPGroup)
  have hcop : Nat.Coprime (Nat.card (pCore 2 Yplus)) (pCore 2 Yplus).index := by
    change Nat.Coprime (Nat.card (pCore 2 Yplus)) (Nat.card (Yplus ⧸ pCore 2 Yplus))
    rw [hm, hn]
    exact Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)
  obtain ⟨C, hC⟩ := exists_right_complement'_of_coprime hcop
  have hC3 : IsPGroup 3 C := hq.of_equiv hC.symm.QuotientMulEquiv
  have hCV : Nat.Coprime (Nat.card (C.map Yplus.subtype)) (Nat.card V) := by
    let : IsElementaryAbelian 2 V := a.elementary
    exact IsPGroup.coprime_card_of_ne 3 2 (by decide) _ _
      (hC3.map Yplus.subtype) (IsElementaryAbelian.isPGroup 2 V)
  refine ⟨C.map Yplus.subtype, map_subtype_le _, hCV, ?_⟩
  apply commutator_eq_of_centralizing_sup (C := Yplus.pCoreIn 2)
  · rw [pCoreIn, ← Subgroup.map_sup, hC.sup_eq_top]
    simp only [← MonoidHom.range_eq_map, range_subtype]
  · exact yplus_core_centralizes d a
  · exact (map_subtype_le _).trans
      (((yplus_le_intersection d).trans inf_le_left).trans a.normalized)

/-- Coprime displacement is disjoint from the component-centralizer kernel. -/
theorem moved_disjoint_component_centralizer [Finite G]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus) :
    Disjoint ⁅V, Yplus⁆ (centralizer (L : Set G)) := by
  obtain ⟨C, hCY, hcop, hmove⟩ := exists_coprime_moving_complement d a
  let : IsElementaryAbelian 2 V := a.elementary
  have hnorm : C ≤ normalizer (V : Set G) :=
    (hCY.trans ((yplus_le_intersection d).trans inf_le_left)).trans a.normalized
  have hd := commutator_disjoint_centralizer_of_coprime V C hnorm hcop
  rw [hmove] at hd
  apply disjoint_iff_inf_le.mpr
  intro x hx
  exact disjoint_iff_inf_le.mp hd
    ⟨hx.1, moved_le d a hx.1, centralizer_le (hCY.trans d.yplus_le) hx.2⟩

/-- The actual action on the fixed J₂ carrier. -/
def modelMap (j : JankoTwoIdentification I L) : I →* MulAut Sporadic.LeechRelated.J2.Carrier :=
  j.equivalence.toMonoidHom.comp (centralizerQuotientMap (L.subgroupOf I))

/-- The image of X ∩ I in the fixed automorphism model. -/
def modelImage (j : JankoTwoIdentification I L) (X : Subgroup G) :
    Subgroup (MulAut Sporadic.LeechRelated.J2.Carrier) :=
  (X.subgroupOf I).map (modelMap j)

/-- This is the same transported component image used by Terminal. -/
theorem modelImage_eq (j : JankoTwoIdentification I L) (X : Subgroup G) :
    modelImage j X = (componentImage I L X).map j.equivalence.toMonoidHom := by
  rw [modelImage, componentImage, map_map]
  rfl

/-- The supplied model equivalence introduces no additional kernel. -/
theorem modelMap_ker (j : JankoTwoIdentification I L) :
    (modelMap j).ker = (centralizerQuotientMap (L.subgroupOf I)).ker := by
  ext x
  change j.equivalence (centralizerQuotientMap (L.subgroupOf I) x) = 1 ↔ _
  change j.equivalence (centralizerQuotientMap (L.subgroupOf I) x) = 1 ↔
    centralizerQuotientMap (L.subgroupOf I) x = 1
  constructor
  · intro h
    exact j.equivalence.injective (h.trans (map_one j.equivalence).symm)
  · intro h
    rw [h, map_one]

/-- The quotient is faithful on the moved subgroup; faithfulness on V is not needed. -/
theorem moved_modelMap_injective [Finite G]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L) :
    Function.Injective ((modelMap j).subgroupMap ((⁅V, Yplus⁆ : Subgroup G).subgroupOf I)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  apply Subtype.ext
  apply Subtype.ext
  have hk : (x : I) ∈ (modelMap j).ker := by
    change modelMap j x = 1
    exact congrArg Subtype.val hx
  rw [modelMap_ker j, component_kernel_eq I L d.component_le] at hk
  exact Subgroup.disjoint_def.mp (moved_disjoint_component_centralizer d a) x.property hk

/-- The ambient moved subgroup has the same order as its actual model image. -/
theorem moved_card_eq_modelImage [Finite G]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L) :
    Nat.card (⁅V, Yplus⁆ : Subgroup G) = Nat.card (modelImage j ⁅V, Yplus⁆) := by
  have hWI : ⁅V, Yplus⁆ ≤ I :=
    (moved_le d a).trans (a.le_sylow.trans ((sylow_le_intersection d).trans inf_le_right))
  exact (Nat.card_congr (subgroupOfEquivOfLe hWI).toEquiv).symm.trans
    (Nat.card_congr (Equiv.ofBijective _ ⟨moved_modelMap_injective d a j,
      (modelMap j).subgroupMap_surjective _⟩))

/-- The model commutator is the image of the ambient commutator. -/
theorem modelImage_moved (d : ComponentSetup I L M Yplus S)
    (a : ActionSetup M Y S V V₁ V₂ Yplus) (j : JankoTwoIdentification I L) :
    modelImage j ⁅V, Yplus⁆ = ⁅modelImage j V, modelImage j Yplus⁆ := by
  have hVI : V ≤ I := a.le_sylow.trans ((sylow_le_intersection d).trans inf_le_right)
  have hYI : Yplus ≤ I := d.yplus_le.trans d.component_le
  have heq : (⁅V, Yplus⁆ : Subgroup G).subgroupOf I =
      ⁅V.subgroupOf I, Yplus.subgroupOf I⁆ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le ((moved_le d a).trans hVI), map_commutator,
      map_subgroupOf_eq_of_le hVI, map_subgroupOf_eq_of_le hYI]
  simp only [modelImage, heq, map_commutator]

/-- The two genuine alternatives of Hypothesis 15.3.10 determine these orders. -/
theorem moved_card_four_or_sixteen (a : ActionSetup M Y S V V₁ V₂ Yplus) :
    Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4 ∨ Nat.card (⁅V, Yplus⁆ : Subgroup G) = 16 := by
  rcases a.hypothesis with h | h
  · exact Or.inr (by rw [h, a.moved, a.card])
  · exact Or.inl (by rw [a.caseTwo_moved h, a.second_card])

/-- A model upper bound excludes the order-sixteen alternative. -/
theorem moved_card_four_of_model_bound [Finite G]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L)
    (hb : Nat.card (⁅modelImage j V, modelImage j Yplus⁆ :
      Subgroup (MulAut Sporadic.LeechRelated.J2.Carrier)) ≤ 4) :
    Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4 := by
  rw [← modelImage_moved d a j, ← moved_card_eq_modelImage d a j] at hb
  rcases moved_card_four_or_sixteen a with h | h
  · exact h
  · omega


/-- The centralizer kernel is a two-group because I = LS and Z(L) = O₂(L). -/
theorem modelMap_kernel_isTwoGroup (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) : IsPGroup 2 (modelMap j).ker := by
  rw [modelMap_ker]
  obtain ⟨P, hP⟩ := d.sylow
  have hS : IsPGroup 2 S := hP ▸ P.isPGroup'.map I.subtype
  exact component_kernel_isTwoGroup d.component_le d.join_eq hS
    (d.center_eq ▸ pCore_isPGroup)

/-- The actual map preserves the local two-core, including its full inverse image. -/
theorem modelImage_core [Finite G] (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) (X : Subgroup G) (hXI : X ≤ I) :
    modelImage j (X.pCoreIn 2) = (modelImage j X).pCoreIn 2 := by
  have heq : (X.pCoreIn 2).subgroupOf I = (X.subgroupOf I).pCoreIn 2 := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXI),
      map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
      map_subgroupOf_eq_of_le hXI]
  rw [modelImage, heq]
  exact map_pCoreIn_of_ker_isPGroup (modelMap j) (modelMap_kernel_isTwoGroup d j) _

/-- A central subgroup maps into the center of the actual subgroup image. -/
theorem modelImage_center_le (j : JankoTwoIdentification I L)
    (R : Subgroup G) :
    modelImage j ((center R).map R.subtype) ≤
      (center (modelImage j R)).map (modelImage j R).subtype := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, he⟩ := hx
  change (z : G) = (x : G) at he
  have hxR : (x : G) ∈ R := he ▸ z.property
  refine ⟨⟨modelMap j x, mem_map_of_mem _ hxR⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  rintro ⟨y, ⟨u, hu, rfl⟩⟩
  apply Subtype.ext
  change modelMap j u * modelMap j x = modelMap j x * modelMap j u
  simp only [← map_mul]
  apply congrArg (modelMap j)
  apply Subtype.ext
  have hc := congrArg Subtype.val (mem_center_iff.mp hz ⟨u, hu⟩)
  change (u : G) * (z : G) = (z : G) * (u : G) at hc
  change (u : G) * (x : G) = (x : G) * (u : G)
  exact he ▸ hc

/-- The supplied radical centrality is retained in the quotient model. -/
theorem model_moved_le_radical_center [Finite G]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L) :
    ⁅modelImage j V, modelImage j Yplus⁆ ≤
      (center ((modelImage j (Yplus ⊔ S)).pCoreIn 2)).map
        ((modelImage j (Yplus ⊔ S)).pCoreIn 2).subtype := by
  have hHI : Yplus ⊔ S ≤ I :=
    sup_le (d.yplus_le.trans d.component_le) ((sylow_le_intersection d).trans inf_le_right)
  rw [← modelImage_moved d a j, ← modelImage_core d j (Yplus ⊔ S) hHI]
  exact (map_mono (subgroupOf_mono I ((moved_le d a).trans a.central_radical))).trans
    (modelImage_center_le j _)

/-- Only an upper bound for the model radical center remains to be calculated. -/
theorem moved_card_four_of_radical_center_bound [Finite G]
    (d : ComponentSetup I L M Yplus S) (a : ActionSetup M Y S V V₁ V₂ Yplus)
    (j : JankoTwoIdentification I L)
    (hb : Nat.card (center ((modelImage j (Yplus ⊔ S)).pCoreIn 2)) ≤ 4) :
    Nat.card (⁅V, Yplus⁆ : Subgroup G) = 4 := by
  apply moved_card_four_of_model_bound d a j
  have hcard := Nat.card_le_card_of_injective _
    (Subgroup.inclusion_injective (model_moved_le_radical_center d a j))
  rw [card_map_of_injective ((modelImage j (Yplus ⊔ S)).pCoreIn 2).subtype_injective] at hcard
  exact hcard.trans hb

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction
