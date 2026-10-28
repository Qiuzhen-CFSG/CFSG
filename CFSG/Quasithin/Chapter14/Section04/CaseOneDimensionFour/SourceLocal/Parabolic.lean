module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.Consequences
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPointResidual
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.PrimeSection
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Centralizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual point core and Sylow product in the order-32 branch

The natural action identifies the point parabolic modulo V with the literal
point stabilizer in SL₃(2). Its residual displacements generate V, so the
seed lies in L₁. Both point radicals lift to groups of order 32. Normality
of U in the point parabolic then gives U=O₂(L∩H)=O₂(L₁), and a cubic
supplement of L₁ is constructed. In particular U lies in the actual O²(H).

For the original omitted-point conjugator, W has index two in U by the
extraspecial commutator form. The conjugate Wᵍ lies in O₂(P) and hence in T,
and the already proved E=V gives U∩Wᵍ=V. Counting their normalized product
proves T∩L=UWᵍ. The final application constructs both the cubic supplement
and the omitted-point conjugator from the original flag.

These prove the local parabolic clause 14.4.4(5). The ambient nonsplit
exclusion, fusion argument, U=O₂(H), and order-eighteen inverted quotient
remain with qt-d-14414-g2-source; universal recognition remains with
qt-i45-g2-recognition. The earlier naturality and structural implications
retain their original producers qt-d-1434-source and qt-d-1222-source.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.4.4(4–5), printed p.1007, and 12.8.11, printed p.854.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem card_of_kernel_le {A B : Type*} [Group A] [Group B]
    (f : A →* B) (Y : Subgroup A) (hk : f.ker ≤ Y) :
    Nat.card Y = Nat.card f.ker * Nat.card (Y.map f) := by
  let r := f.comp Y.subtype
  have hr : r.ker = f.ker.subgroupOf Y := rfl
  have hrange : r.range = Y.map f := by
    rw [MonoidHom.range_comp, range_subtype]
  have h := r.ker.card_mul_index
  rw [index_ker, hrange, hr,
    Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv] at h
  exact h.symm

omit [Finite G] in
private theorem point_action (F : InvariantFlag T V 3) [IsElementaryAbelian 2 V]
    {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV 3) :
    ∃ (f : L →* BinaryLinearThree.Group)
      (c : V ≃* Multiplicative BinaryLinearThree.Vector) (z : BinaryLinearThree.Vector),
      Function.Surjective f ∧ f.ker = pCore 2 L ∧ z ≠ 0 ∧
      (F.H.subgroupOf L).map f = BinaryLinearThree.naturalPoint z ∧
      ∀ l : L, ∀ v : V,
        c ⟨(l : G) * v * (l : G)⁻¹, (mem_normalizer_iff.mp (hLV l.property) v).mp v.property⟩ =
          Multiplicative.ofAdd (BinaryLinearThree.W (f l) (c v).toAdd) := by
  let e := BinaryLinear.OuterCyclic.slEquivLinear 3
  let f : L →* BinaryLinearThree.Group := e.symm.toMonoidHom.comp
    (A.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  let c : V ≃* Multiplicative BinaryLinearThree.Vector :=
    A.coordinates.toAddEquiv.toMultiplicativeRight
  obtain ⟨z, hz, hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  let zV : V := ⟨z, F.le_seed 1 (hpoint ▸ mem_zpowers z)⟩
  have hc (l : L) (v : V) :
      c ⟨(l : G) * v * (l : G)⁻¹, (mem_normalizer_iff.mp (hLV l.property) v).mp v.property⟩ =
        Multiplicative.ofAdd (BinaryLinearThree.W (f l) (c v).toAdd) := by
    change A.coordinates (Additive.ofMul ⟨_, _⟩) =
      (e (f l)) (A.coordinates (Additive.ofMul v))
    rw [show e (f l) = A.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) from
      e.apply_symm_apply _]
    exact A.equivariant l (Additive.ofMul v)
  have hf : Function.Surjective f := e.symm.surjective.comp
    (A.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  refine ⟨f, c, (c zV).toAdd, hf, ?_, ?_, ?_, hc⟩
  · dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ A.quotientEquiv.injective, QuotientGroup.ker_mk']
  · intro he
    have hzV : c zV = 1 := he
    exact hz (congrArg Subtype.val (c.map_eq_one_iff.mp hzV))
  · have hm (l : L) : f l ∈ BinaryLinearThree.naturalPoint (c zV).toAdd ↔ (l : G) ∈ F.H := by
      rw [BinaryLinearThree.mem_naturalPoint]
      change Multiplicative.ofAdd (BinaryLinearThree.W (f l) (c zV).toAdd) = c zV ↔ _
      rw [← hc, c.injective.eq_iff, Subtype.ext_iff,
        F.H_eq_centralizer (by decide) z hpoint, mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul
    ext a
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (hm l).mpr hl
    · intro ha
      obtain ⟨l, rfl⟩ := hf a
      exact ⟨l, (hm l).mp ha, rfl⟩

/-- The literal point parabolic and its residual have the original closure as two-core. -/
theorem source_point_core (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    F.U = (L ⊓ F.H).pCoreIn 2 ∧ F.U = (F.Li L 1).pCoreIn 2 ∧
      Nat.card (L ⊓ F.H : Subgroup G) = 192 ∧ Nat.card (F.Li L 1) = 96 := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨hV, hUL⟩ := source_block_core d earlier hq chosen structural alternatives F hne hZ hcard
  obtain ⟨f, c, z, hf, hk, hz, hS, hc⟩ := point_action F H.naturalMarking
  let S := F.H.subgroupOf L
  let R := (pResidual 2 S).map S.subtype
  have hSL : S.map L.subtype = L ⊓ F.H := by
    simp only [S, subgroupOf_map_subtype, inf_comm]
  have hRL : R.map L.subtype = F.Li L 1 := by
    dsimp only [R]
    rw [map_embedded_pResidual, hSL]
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]
    rfl
  have hR : R.map f = (pResidual 2 (BinaryLinearThree.naturalPoint z)).map
      (BinaryLinearThree.naturalPoint z).subtype := by
    dsimp only [R]
    rw [map_embedded_pResidual, hS]
  have hVL : V ≤ L := hV.le.trans (L.pCoreIn_le 2)
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  have hker (x : L) : x ∈ f.ker ↔ (x : G) ∈ V := by
    rw [hk, hV]
    exact ⟨fun hx => mem_map_of_mem _ hx, fun ⟨y, hy, he⟩ => (Subtype.ext he : y = x) ▸ hy⟩
  have hkS : f.ker ≤ S := fun x hx => hVH ((hker x).mp hx)
  have hkcard : Nat.card f.ker = 8 := by
    have he : f.ker.map L.subtype = V := by rw [hk]; exact hV.symm
    rw [← card_map_of_injective L.subtype_injective, he]
    simpa [F.last] using F.card 3 (by decide)
  have hkR : f.ker ≤ R := by
    have hn : S ≤ normalizer (R : Set L) := le_normalizer_embedded_pResidual 2 S
    have hcomm : ⁅R, S⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hn
    intro v hv
    let vV : V := ⟨v, (hker v).mp hv⟩
    obtain ⟨a, ha, b, hb, x, y, he⟩ := BinaryLinearThree.naturalPoint_residual_displacements z hz (c vV).toAdd
    obtain ⟨aL, haL, rfl⟩ := (show a ∈ R.map f from hR.symm ▸ ha)
    obtain ⟨bL, hbL, rfl⟩ := (show b ∈ R.map f from hR.symm ▸ hb)
    let xV := c.symm (Multiplicative.ofAdd x)
    let yV := c.symm (Multiplicative.ofAdd y)
    let xL : L := ⟨xV, hVL xV.property⟩
    let yL : L := ⟨yV, hVL yV.property⟩
    have hxS : xL ∈ S := hVH xV.property
    have hyS : yL ∈ S := hVH yV.property
    have hm := R.mul_mem (hcomm (commutator_mem_commutator haL hxS))
      (hcomm (commutator_mem_commutator hbL hyS))
    have hformula (l : L) (w : V) :
        c ⟨⁅(l : G), (w : G)⁆, V.mul_mem
          ((mem_normalizer_iff.mp (chosen.normalizes l.property) w).mp w.property)
          (V.inv_mem w.property)⟩ =
          Multiplicative.ofAdd (BinaryLinearThree.W (f l) (c w).toAdd - (c w).toAdd) := by
      change c (⟨(l : G) * w * (l : G)⁻¹, (mem_normalizer_iff.mp (chosen.normalizes l.property) w).mp w.property⟩ * w⁻¹) = _
      rw [map_mul, map_inv, hc, ofAdd_sub, ofAdd_toAdd, div_eq_mul_inv]
    have heq : ⁅aL, xL⁆ * ⁅bL, yL⁆ = v := by
      apply Subtype.ext
      have hvv := congrArg Multiplicative.ofAdd he
      change c vV = Multiplicative.ofAdd (BinaryLinearThree.W (f aL) x - x) *
        Multiplicative.ofAdd (BinaryLinearThree.W (f bL) y - y) at hvv
      have h1 := hformula aL xV
      have h2 := hformula bL yV
      dsimp only [xV, yV] at h1 h2
      simp only [c.apply_symm_apply, toAdd_ofAdd] at h1 h2
      rw [← h1, ← h2, ← map_mul] at hvv
      exact (congrArg (fun w : V => (w : G)) (c.injective hvv)).symm
    exact heq ▸ hm
  have hpker : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
  have hkSc : f.ker ≤ S.pCoreIn 2 := le_pCoreIn_of_normalizes hpker hkS
    (by rw [f.ker.normalizer_eq_top]; exact le_top)
  have hkRc : f.ker ≤ R.pCoreIn 2 := le_pCoreIn_of_normalizes hpker hkR
    (by rw [f.ker.normalizer_eq_top]; exact le_top)
  have hSc : (S.pCoreIn 2).map f = (BinaryLinearThree.naturalPoint z).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup f hpker, hS]
  have hRc : (R.pCoreIn 2).map f = (BinaryLinearThree.naturalPoint z).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup f hpker, hR,
      BinaryLinearThree.naturalPoint_residual_core z hz]
  have hScard : Nat.card (S.pCoreIn 2) = 32 := by
    rw [card_of_kernel_le f _ hkSc, hkcard, hSc, BinaryLinearThree.card_naturalPoint_core z hz]
  have hRcard : Nat.card (R.pCoreIn 2) = 32 := by
    rw [card_of_kernel_le f _ hkRc, hkcard, hRc, BinaryLinearThree.card_naturalPoint_core z hz]
  have hUN : F.U ≤ (L ⊓ F.H).pCoreIn 2 := le_pCoreIn_of_normalizes
    (source_closure d earlier hq chosen structural alternatives F hne).1
    (le_inf hUL F.U_le_H) (inf_le_right.trans (le_normalizer_conjugateSpanBy V F.H))
  have hNc : Nat.card ((L ⊓ F.H).pCoreIn 2) = 32 := by
    rw [← hSL, ← map_pCoreIn_of_injective 2 S L.subtype L.subtype_injective,
      card_map_of_injective L.subtype_injective, hScard]
  have hU : F.U = (L ⊓ F.H).pCoreIn 2 := eq_of_le_of_card_ge hUN (by omega)
  have hRle : (F.Li L 1).pCoreIn 2 ≤ (L ⊓ F.H).pCoreIn 2 := by
    apply pCoreIn_mono_of_normalizes (F.Li_le L 1)
    exact le_normalizer_embedded_pResidual 2 (L ⊓ F.H)
  have hLc : Nat.card ((F.Li L 1).pCoreIn 2) = 32 := by
    rw [← hRL, ← map_pCoreIn_of_injective 2 R L.subtype L.subtype_injective,
      card_map_of_injective L.subtype_injective, hRcard]
  refine ⟨hU, hU.trans (eq_of_le_of_card_ge hRle (by omega)).symm, ?_, ?_⟩
  · rw [← hSL, card_map_of_injective L.subtype_injective, card_of_kernel_le f S hkS,
      hkcard, hS, BinaryLinearThree.naturalPoint_card z hz]
  · rw [← hRL, card_map_of_injective L.subtype_injective, card_of_kernel_le f R hkR,
      hkcard, hR, BinaryLinearThree.naturalPoint_residual_card z hz]

/-- Apply the identified point core to construct the actual cubic supplement.
In particular U lies in the literal O²(H), as required by the normalizer-action
and split-block consumers. -/
theorem source_point_cubic (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nat.card (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) = 3 ∧
      F.U ≤ (pResidual 2 F.H).map F.H.subtype ∧
      ∃ a : G, a ∈ F.Li L 1 ∧ orderOf a = 3 ∧ F.U ⊔ zpowers a = F.Li L 1 := by
  obtain ⟨_, hcore, _, hL⟩ := source_point_core d earlier hq chosen structural alternatives
    F hne hZ hcard
  have hc : Nat.card (pCore 2 (F.Li L 1)) = 32 := by
    rw [← card_map_of_injective (F.Li L 1).subtype_injective]
    change Nat.card ((F.Li L 1).pCoreIn 2) = 32
    rw [← hcore, hcard]
  have hq3 : Nat.card (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) = 3 := by
    have hh := (pCore 2 (F.Li L 1)).card_mul_index
    rw [hc, index_eq_card, hL] at hh
    omega
  have hLR : F.Li L 1 ≤ (pResidual 2 F.H).map F.H.subtype :=
    embedded_pResidual_mono 2 (show L ⊓ F.H ≤ F.H from inf_le_right)
  refine ⟨hq3, (hcore.le.trans ((F.Li L 1).pCoreIn_le 2)).trans hLR, ?_⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨a, ha, hgen⟩ := exists_prime_order_sup_pCore_eq_top
    (G := F.Li L 1) (p := 2) (q := 3) (by decide) hq3
  refine ⟨a, a.property, (Subgroup.orderOf_coe a).trans ha, ?_⟩
  have hm := congrArg (map (F.Li L 1).subtype) hgen
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at hm
  change zpowers (a : G) ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 at hm
  rw [← hcore, sup_comm] at hm
  exact hm


/-- The original omitted-point conjugate gives the full Sylow subgroup of L.
The set product and intersection refer to the literal Wᵍ, including its center. -/
theorem source_sylow_product (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.U ⊔ F.X g = (T : Subgroup G) ⊓ L ∧
      Nat.card F.W = 16 ∧ F.U ⊓ F.X g = V ∧
      (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) = (F.U : Set G) * (F.X g : Set G) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, hphi, hcenter⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let B := F.uhatBilinearForm (by decide) htwo hphi
  have hb (u v : F.U) :
      B (Symplectic.hatElement F u) (Symplectic.hatElement F v) = 0 ↔ Commute u v := by
    change (SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) hphi)
      (F.uhatCommutator htwo (QuotientGroup.mk' (center F.U) u)
        (QuotientGroup.mk' (center F.U) v))).toAdd = 0 ↔ _
    change SmallFrattini.binaryMark (F.frattini_card_two_of_point (by decide) hphi)
      (F.uhatCommutator htwo (QuotientGroup.mk' (center F.U) u)
        (QuotientGroup.mk' (center F.U) v)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, Subtype.ext_iff, F.uhatCommutator_apply_mk]
    exact commutatorElement_eq_one_iff_mul_comm
  have hi := Symplectic.W_relIndex_U_eq_two F (by decide) hcenter B hb
    (F.uhatBilinearForm_nondegenerate (by decide) htwo hphi)
  have hWcard : Nat.card F.W = 16 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) F.W F.U bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, hi, hcard] at hh
    omega
  have hXcard : Nat.card (F.X g) = 16 := by
    rw [X, conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hWcard]
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hXC := F.X_le_plane_centralizer g hgG
  have hUL := (source_block_core d earlier hq chosen structural alternatives F hne hZ hcard).2
  have hgN : g ∈ normalizer (L : Set G) :=
    (sup_le L.le_normalizer (H.sylow_normalizes structural)) hgP.1
  have hXL : F.X g ≤ L := conjugate_le_of_normalizes (inf_le_left.trans hUL) g hgN
  have hXP : F.X g ≤ F.P L := by
    refine le_inf (hXL.trans le_sup_left) ?_
    apply le_iInf
    intro i
    apply le_iInf
    intro hi
    have hei : i = 2 := by omega
    subst i
    exact hXC.trans (Subgroup.centralizer_le_normalizer _)
  have hXcore : F.X g ≤ (F.P L).pCoreIn 2 :=
    (le_inf hXP hXC).trans_eq
      (F.binary_parabolic_core (by decide) L chosen.normalizes
        (H.binarySeedAction_surjective F) (H.centralizer_LT structural)).1
  have hcoreT : (F.P L).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := (pCore_isPGroup (p := 2) (G := F.P L)).le_sylow_of_normal
      (T.subtype (F.binary_sylow_le_P L))
    rintro x ⟨y, hy, rfl⟩
    exact hh hy
  have hXT : F.X g ≤ (T : Subgroup G) := hXcore.trans hcoreT
  have hUX : F.U ⊓ F.X g = V := by
    apply Eq.trans ?_ (source_intersection_eq_seed d earlier hq chosen structural alternatives
      F hne hZ hcard g hgP hgH)
    apply le_antisymm
    · intro x hx
      exact ⟨⟨hx.1, hXC hx.2⟩, hx.2⟩
    · exact inf_le_inf_right _ inf_le_left
  have hnorm := F.X_normalizes_U g hgG
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.U (F.X g) hnorm
  have hvcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [hcard, hXcard, hUX, hvcard] at hc
  have hTL := (source_sylow_index d earlier hq chosen structural alternatives F hne hZ hcard).1
  have he : F.U ⊔ F.X g = (T : Subgroup G) ⊓ L :=
    eq_of_le_of_card_ge (sup_le
      (le_inf (source_closure_le_sylow d earlier hq chosen structural alternatives F) hUL)
      (le_inf hXT hXL)) (by omega)
  refine ⟨he, hWcard, hUX, ?_⟩
  rw [← he]
  exact coe_mul_of_right_le_normalizer_left F.U (F.X g) hnorm


/-- The source flags supply both actual generators needed by the later local
analysis: a cubic supplement of L₁ and an omitted-point conjugator producing
its order-64 Sylow product. No choice of these elements is an input. -/
theorem source_parabolic_generators (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    ∃ g a : G, g ∈ F.P L ∧ g ∉ F.H ∧ a ∈ F.Li L 1 ∧ orderOf a = 3 ∧
      F.U ⊔ zpowers a = F.Li L 1 ∧ F.U ⊔ F.X g = (T : Subgroup G) ⊓ L ∧
      F.U ⊓ F.X g = V := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  let β := H.naturalMarking.coordinates
  obtain ⟨b, _, hcuts⟩ := F.exists_naturalFlag_marking L chosen.normalizes H.full_L_action β
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (H.sylow_normalizes_seed structural) (H.full_LT_action structural) β b hcuts
  obtain ⟨_, _, a, ha, ha3, hgen⟩ := source_point_cubic d earlier hq chosen structural alternatives
    F hne hZ hcard
  obtain ⟨hsylow, _, hinter, _⟩ := source_sylow_product d earlier hq chosen structural alternatives
    F hne hZ hcard g hgP hgH
  exact ⟨g, a, hgP, hgH, ha, ha3, hgen, hsylow, hinter⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
