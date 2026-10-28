module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCentralizerBound
public import Theory.GroupTheory.NormalSymmetricThree

/-!
# The canonical centralizer-extension quotient

Write D=C_H(K) and P=O₂(K), embedded in H=C_G(z). The marked S₅
quotient gives |Q|=8|D| and |T|=64|D|. The normal closure K has order
192 and H=KT, so |H|=192|D|. Since P∩D=Z(P), the kernel PD has
order16|D| and H/PD has order12. The image of K under this same
quotient map is its actual S₃ quotient. A normal S₃ splits off its
centralizer, which here has order two; hence H/PD≃S₃×C₂.

The calculation retains both possible orders of D. It does not assume
P is self-centralizing or that the extension over P splits. The cubic
centralizer and elementary-four transfer remain source obligations.
Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- Orders of the actual elementary local core and Sylow subgroup. -/
theorem LocalAnalysis.equality_extension_orders
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
        8 * Nat.card (equalityCentralizer L R z) ∧
      Nat.card T = 64 * Nat.card (equalityCentralizer L R z) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := equalityCentralizer L R z
  let V := layer L R
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hVD : V ⊔ D = Q := by
    change V ⊔ D = (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←equality_sylow_centralizer_eq_core h611 hnatural]
    exact (A.equality_sylow_layer_centralizer h611 hnatural hz hTH hp.plusType).symm
  have hDQ : D ≤ Q := A.equality_centralizer_le_local_core h611 hnatural hz hTH
  have hV16 : Nat.card V = 16 := by
    simpa only [hnatural.1, Nat.reduceMul, Nat.reducePow] using hnatural.2.1.card
  have hDV : D ⊓ V = zpowers z := A.equality_centralizer_inf_layer h611 hz hp.core_center
  have hcardQ : Nat.card Q = 8 * Nat.card D := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes V D
      (hDQ.trans ((pCoreIn_le 2 _).trans (sup_le
        (h611.L_le.trans (A.equality_maximal_normalizes_layer h611 hnatural hz horder hTH hbranch))
        h611.sylow_normalizes_layer)))
    rw [hVD,inf_comm V D,hDV,Nat.card_zpowers,horder,hV16] at hc
    omega
  have hQT : Q ≤ (T : Subgroup G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    rw [←equality_sylow_centralizer_eq_core h611 hnatural]
    exact inf_le_left
  have hQM := hQT.trans h611.sylow_le
  obtain ⟨f,hf,hker,_,_⟩ := A.equality_core_permutation_image h611 hnatural hz horder hTH hbranch
  let TM := (T : Subgroup G).subgroupOf M
  let fT := f.comp TM.subtype
  have hT8 : Nat.card fT.range = 8 := by
    rw [MonoidHom.range_comp,range_subtype]
    change Nat.card ((T.subtype h611.sylow_le).mapSurjective hf) = 8
    exact (Nat.card_congr (((T.subtype h611.sylow_le).mapSurjective hf).equiv
      Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.standardSylow).toEquiv).trans
      Theory.SpecificGroups.SymmetricFive.OuterFourGeometry.eight_card
  have hkerT : fT.ker = (Q.subgroupOf M).subgroupOf TM := by
    change f.ker.comap TM.subtype = _
    rw [hker]
    rfl
  have hkerCard : Nat.card fT.ker = Nat.card Q := by
    rw [hkerT,Nat.card_congr (subgroupOfEquivOfLe (subgroupOf_mono M hQT)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hQM).toEquiv]
  have hc := fT.ker.card_mul_index
  rw [index_ker,hT8,hkerCard,Nat.card_congr (subgroupOfEquivOfLe h611.sylow_le).toEquiv,
    hcardQ] at hc
  refine ⟨hcardQ,?_⟩
  change Nat.card T = 64 * Nat.card D
  omega


/-- The canonical normal closure has order 192. -/
theorem LocalAnalysis.equality_closure_order
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nat.card (equalityLayerClosure L R z) = 192 := by
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  let K := equalityLayerClosure L R z
  have h32 : Nat.card (pCore 2 K) = 32 := by
    rw [Nat.card_congr ((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective).toEquiv]
    exact hp.plusType.some.card
  have h6 : (pCore 2 K).index = 6 := by
    rw [index_eq_card,Nat.card_congr hp.quotient.some.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hc := (pCore 2 K).card_mul_index
  rw [h32,h6] at hc
  change Nat.card K = 192
  omega

/-- H has three times the order of its Sylow two-subgroup. -/
theorem LocalAnalysis.equality_centralizer_order
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nat.card (centralizer ({z} : Set G)) =
      192 * Nat.card (equalityCentralizer L R z) := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let S := T.subtype hTH
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have h192 := A.equality_closure_order h611 hnatural hz horder hTH hbranch
  obtain ⟨U,hU⟩ := NormalSylowQuotientAction.intersection_sylow S K (by
    rw [normalizer_eq_top]; exact le_top)
  have h64 : Nat.card (K ⊓ (S : Subgroup H) : Subgroup H) = 64 := by
    have hc : Nat.card U = 64 := by
      rw [U.card_eq_multiplicity,h192]
      decide +kernel
    rw [hU] at hc
    rw [←inf_subgroupOf_right (S : Subgroup H) K,
      Nat.card_congr (subgroupOfEquivOfLe (show (S : Subgroup H) ⊓ K ≤ K from inf_le_right)).toEquiv,
      inf_comm] at hc
    exact hc
  have hgen : K ⊔ (S : Subgroup H) = ⊤ := by
    apply (map_injective H.subtype_injective)
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hp.generation.symm
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes K (S : Subgroup H)
    (by rw [normalizer_eq_top];exact le_top)
  rw [h192,h64,hgen,card_top] at hc
  have hT : Nat.card S = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv
  rw [hT,(A.equality_extension_orders h611 hnatural hz horder hTH hbranch).2] at hc
  omega

/-- The actual outer-action kernel has order sixteen times |D|. -/
theorem LocalAnalysis.equality_outer_kernel_order
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nat.card (equalityCore L R z ⊔ centralizer
      (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))) :
        Subgroup (centralizer ({z} : Set G))) =
      16 * Nat.card (equalityCentralizer L R z) := by
  let H := centralizer ({z} : Set G)
  let P := equalityCore L R z
  let D := centralizer (equalityLayerClosure L R z : Set H)
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hc : P ⊓ D = M22Recognition.CentralizerExtension.coreCenter P := by
    change P ⊓ centralizer (equalityLayerClosure L R z : Set H) = _
    rw [← A.equality_core_centralizer h611 hnatural hz]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x,hx.1⟩,mem_center_iff.mpr (fun y => Subtype.ext (hx.2 y y.property)),rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,fun q hq => congrArg Subtype.val (mem_center_iff.mp hy ⟨q,hq⟩)⟩
  have h2 : Nat.card (P ⊓ D : Subgroup H) = 2 := by
    rw [hc]
    change Nat.card ((center P).map P.subtype) = 2
    rw [Nat.card_congr ((center P).equivMapOfInjective P.subtype P.subtype_injective).toEquiv.symm]
    exact hp.plusType.some.center_card
  have hD : Nat.card D = Nat.card (equalityCentralizer L R z) :=
    Nat.card_congr (D.equivMapOfInjective H.subtype H.subtype_injective).toEquiv
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes P D
    (by rw [normalizer_eq_top];exact le_top)
  rw [hp.plusType.some.card,h2,hD] at hh
  change Nat.card (P ⊔ D : Subgroup H) = _
  dsimp only [P,D,H] at hh ⊢
  omega

/-- The actual quotient by P C_H(K) has order twelve. -/
theorem LocalAnalysis.equality_outer_quotient_order
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nat.card ((centralizer ({z} : Set G)) ⧸ (equalityCore L R z ⊔ centralizer
      (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))))) = 12 := by
  let H := centralizer ({z} : Set G)
  let N := equalityCore L R z ⊔ centralizer (equalityLayerClosure L R z : Set H)
  have hc := N.card_mul_index
  rw [A.equality_outer_kernel_order h611 hnatural hz horder hTH hbranch,
    A.equality_centralizer_order h611 hnatural hz horder hTH hbranch,index_eq_card] at hc
  change Nat.card (H ⧸ N) = 12
  rcases A.equality_centralizer_card h611 hnatural hz horder hTH hbranch with h2 | h4
  · rw [h2] at hc
    dsimp only [N,H] at hc ⊢
    nlinarith [hc]
  · rw [h4] at hc
    dsimp only [N,H] at hc ⊢
    nlinarith [hc]

/-- The extension quotient is the product S₃×C₂ on the actual canonical kernel. -/
theorem LocalAnalysis.equality_extension_quotient
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    Nonempty (((centralizer ({z} : Set G)) ⧸ (equalityCore L R z ⊔ centralizer
      (equalityLayerClosure L R z : Set (centralizer ({z} : Set G))))) ≃*
        (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let P := equalityCore L R z
  let D := centralizer (K : Set H)
  let N := P ⊔ D
  let q := QuotientGroup.mk' N
  let f := q.comp K.subtype
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hPK : P ≤ K := pCoreIn_le 2 K
  have hDK : D ⊓ K ≤ P := by
    intro d hd
    have hh := A.equality_centralizer_inf_closure_le_center
      ⟨mem_map_of_mem H.subtype hd.1,mem_map_of_mem H.subtype hd.2⟩
    obtain ⟨c,hc,he⟩ := hh
    exact (Subtype.ext he : c = d) ▸ map_subtype_le _ hc
  have hk : f.ker = pCore 2 K := by
    ext k
    change q (k : H) = 1 ↔ k ∈ pCore 2 K
    change ((k : H) : H ⧸ N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hkN
      obtain ⟨p,hpP,d,hd,he⟩ := mem_sup_of_normal_right.mp hkN
      have hdK : d ∈ K := by
        have hh := K.mul_mem (K.inv_mem (hPK hpP)) k.property
        rw [←he,inv_mul_cancel_left] at hh
        exact hh
      have hkP : (k : H) ∈ P := he ▸ P.mul_mem hpP (hDK ⟨hd,hdK⟩)
      obtain ⟨x,hx,hxk⟩ := hkP
      exact (Subtype.ext hxk : x = k) ▸ hx
    · intro hkP
      exact mem_sup_left (mem_map_of_mem K.subtype hkP)
  let B := K.map q
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hr : f.range = B := by rw [MonoidHom.range_comp,range_subtype]
  let eB : B ≃* Equiv.Perm (Fin 3) := (MulEquiv.subgroupCongr hr.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans hp.quotient.some))
  obtain ⟨e,_⟩ := NormalSymmetricThree.exists_product_equiv B eB
  have h6 : Nat.card B = 6 := by
    rw [Nat.card_congr eB.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hC : Nat.card (centralizer (B : Set (H ⧸ N))) = 2 := by
    have hc := Nat.card_congr e.toEquiv
    rw [Nat.card_prod,h6] at hc
    have h12 := A.equality_outer_quotient_order h611 hnatural hz horder hTH hbranch
    change Nat.card (H ⧸ N) = 12 at h12
    rw [h12] at hc
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 6) hc
  let eC : centralizer (B : Set (H ⧸ N)) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hC (by simp)
  exact ⟨e.symm.trans (eB.prodCongr eC)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
