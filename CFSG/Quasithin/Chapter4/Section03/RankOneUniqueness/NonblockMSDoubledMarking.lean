module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSRowSelection
public import Theory.SpecificGroups.PSL3.LinearThreeRootFixed
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialCenter

/-!
# Initial markings and the doubled core in the nonblock branch

The original full module W lies in the initial moved omega layer and
centralizes O₂(L). In the point-parabolic orientation, radical-fixed
vectors on both natural summands would be fixed by all of L, contradicting
[W,L]=W≠1. Thus the initial layer has the line orientation. The proved
natural first-cohomology splitting then gives C_S(K)=C_KS(K)=1 without
assuming the whole-core alternatives of C.1.34.

In the whole doubled row, O₂(K) centralizes Q. The three-subgroups lemma
and C_S(K)=1 make O₂(K) abelian; first-cohomology vanishing removes its
K-fixed supplement to Q. Hence O₂(K)=Q, including over the field of order
four. A second splitting gives C_KS(Q)=Q, the centralizer conclusion of
C.1.36(1). One inner conjugation then aligns the original S∩L with the
upper unipotent subgroup, transporting both natural summands together.

The final consumer retains the original five-row classification as an
explicit premise and returns either this marked doubled core or the
constructed third-row MSData with both original markings. The full quotient
recognition, whole-core classification, doubled-row exclusion using
C.1.36(2), and strict secondary-core enlargement remain separate obligations.
In particular no equality W=[Q,L] is assumed in the doubled row.

Source: Aschbacher--Smith, C.4.1(3) and C.4.7, printed pp.151--153;
original 4.3.9--10, pp.616--617; C.1.36(1), p.140, and I.1.6, p.408.
The simultaneous Sylow transport adapts NonblockMSMarking to the doubled row.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

omit [Finite G] in
private theorem fullModule_moved : ⁅W c,L⁆ = W c := by
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  exact (show W c = ⁅W c,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm

private theorem fullModule_centralizes_localCore :
    W c ≤ centralizer (L.pCoreIn 2 : Set G) := by
  have hIN : c.I ≤ normalizer (L : Set G) := by
    rw [c.I_eq]
    exact sup_le L.le_normalizer (c.c28.radical_le.trans inf_le_right)
  have hcore : L.pCoreIn 2 ≤ c.I.pCoreIn 2 := pCoreIn_mono_of_normalizes c.le_I hIN
  intro w hw l hl
  obtain ⟨v,hv,hvw⟩ := c.c28.module_le_center_radical hw
  have hh := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
    (mem_center_iff.mp hv ⟨l,hcore hl⟩)
  change l * (v : G) = (v : G) * l at hh
  change (v : G) = w at hvw
  rwa [hvw] at hh

private theorem local_core_image {F : Type} [Field F] [Finite F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ((L.pCoreIn 2).subgroupOf (K c)).map (linearThreeActor e) =
      ((L.subgroupOf (K c)).map (linearThreeActor e)).pCoreIn 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : (linearThreeActor e).ker = pCore 2 (K c) := by
    ext k
    change e (QuotientGroup.mk' (pCore 2 (K c)) k) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hp : IsPGroup 2 (linearThreeActor e).ker := hk ▸ pCore_isPGroup
  have hlocal : (L.subgroupOf (K c)).pCoreIn 2 = (L.pCoreIn 2).subgroupOf (K c) := by
    apply map_injective (K c).subtype_injective
    rw [map_pCoreIn_of_injective 2 _ _ (K c).subtype_injective,
      map_subgroupOf_eq_of_le c.le_component,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 L).trans c.le_component)]
  rw [←hlocal]
  exact map_pCoreIn_of_ker_isPGroup _ hp _

omit [Finite G] in
private theorem double_coordinates {F : Type*} [Field F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (A : Subgroup G)
    (hm : HasSectionModel (K c) A ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    ∃ f : A ≃* Multiplicative ((Fin 3 → F) × (Fin 3 → F)),
      ∀ (k : K c) (u v : A), (v : G) = k * (u : G) * (k : G)⁻¹ →
        (f v).toAdd = ((linearThreeActor e k).val.mulVec (f u).toAdd.1,
          (linearThreeActor e k).val.mulVec (f u).toAdd.2) := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,f,hf⟩ := hm
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans f,hf⟩

private theorem doubled_line {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G) (hWA : W c ≤ A)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) A ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (hp : (L.subgroupOf (K c)).map (linearThreeActor e) = pointLocalSL F ∨
      (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F := by
  rcases hp with hp | hp
  · exfalso
    obtain ⟨f,he⟩ := double_coordinates e A hm
    have hc : ((L.pCoreIn 2).subgroupOf (K c)).map (linearThreeActor e) =
        (pointRadicalSL F).map (pointLocalSL F).subtype := by
      rw [local_core_image e,hp]
      change (pCore 2 (pointLocalSL F)).map _ = _
      rw [pointLocalSL_twoCore_eq]
    have hfixed (w : W c) : ∀ g ∈ pointLocalSL F,
        (g.val.mulVec (f ⟨w,hWA w.property⟩).toAdd.1,
          g.val.mulVec (f ⟨w,hWA w.property⟩).toAdd.2) =
        (f ⟨w,hWA w.property⟩).toAdd := by
      let u : A := ⟨w,hWA w.property⟩
      have hrad (g : pointLocalSL F) (hg : g ∈ pointRadicalSL F) :
          (g.val.val.mulVec (f u).toAdd.1,g.val.val.mulVec (f u).toAdd.2) = (f u).toAdd := by
        obtain ⟨k,hk,hkg⟩ := hc.ge (mem_map_of_mem _ hg)
        have hcomm := fullModule_centralizes_localCore w.property k hk
        have hh := he k u u (by
          change (w : G) = k * (w : G) * (k : G)⁻¹
          rw [hcomm,mul_inv_cancel_right])
        rw [hkg] at hh
        exact hh.symm
      obtain ⟨a,ha⟩ := (pointRadicalSL_fixed_iff F (f u).toAdd.1).mp
        (fun g hg => congrArg Prod.fst (hrad g hg))
      obtain ⟨b,hb⟩ := (pointRadicalSL_fixed_iff F (f u).toAdd.2).mp
        (fun g hg => congrArg Prod.snd (hrad g hg))
      intro g hg
      change (g.val.mulVec (f u).toAdd.1,g.val.mulVec (f u).toAdd.2) = (f u).toAdd
      apply Prod.ext
      · rw [ha,Matrix.mulVec_smul]
        exact congrArg (a • ·) hg
      · rw [hb,Matrix.mulVec_smul]
        exact congrArg (b • ·) hg
    have hcomm : ⁅W c,L⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro w hw l hl
      let k : K c := ⟨l,c.le_component hl⟩
      let u : A := ⟨w,hWA hw⟩
      let v := A.normalizerMonoidHom ⟨k,hm.2.1 k.property⟩ u
      have hv : (v : G) = l*w*l⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
      have hh := (he k u v hv).trans (hfixed ⟨w,hw⟩ _ (hp.le (mem_map_of_mem _ hl)))
      have hvu : v = u := f.injective (Multiplicative.toAdd.injective hh)
      exact mul_inv_eq_iff_eq_mul.mp (hv.symm.trans (congrArg Subtype.val hvu))
    exact c.c28.module_nontrivial ((fullModule_moved (c := c)).symm.trans hcomm)
  · exact hp

omit [Finite G] in
private theorem natural_reframe {F : Type*} [Field F]
    (a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (g : SL(3,F)) (v : Fin 3 → F) :
    a (Representation.specialLinearNatural 3 g v) =
      Representation.specialLinearNatural 3 (Matrix.HigherLinear.SubspaceTransport.slConj a g) (a v) := by
  symm
  simpa only [Representation.specialLinearNatural_apply,LinearEquiv.symm_apply_apply,
    Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply] using
    Matrix.HigherLinear.SubspaceTransport.slConj_apply a g (a v)

/-- A doubled layer containing the original full module has the line marking.
The same change of coordinates is made on both copies of the layer. -/
theorem exists_doubled_line {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (A : Subgroup G) (hWA : W c ≤ A)
    (hm : HasSectionModel (K c) A ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    ∃ a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      let e' := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)
      HasSectionModel (K c) A ⊥ (linearThreeActor e')
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)) ∧
      (L.subgroupOf (K c)).map (linearThreeActor e') = lineLocalSL F := by
  obtain ⟨a,ha⟩ := nonblock_linearThree_local_frame D hf hn hF e
  let e' := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)
  have hm' : HasSectionModel (K c) A ⊥ (linearThreeActor e')
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)) := by
    apply hm.transport (a.toAddEquiv.prodCongr a.toAddEquiv)
    intro k v
    exact Prod.ext (natural_reframe a (linearThreeActor e k) v.1)
      (natural_reframe a (linearThreeActor e k) v.2)
  exact ⟨a,hm',doubled_line A hWA e' hm' ha⟩

/-- Both initial alternatives supply the original line marking and C_S(K)=1.
No whole-core classification or nonabelianity of Q is required. -/
theorem initial_line_and_centralizer {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      (HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        (Representation.specialLinearNatural (k := F) 3) ∨
       HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3))) ∧
      (L.subgroupOf (K c)).map (linearThreeActor mark) = lineLocalSL F ∧
      S c ⊓ centralizer (K c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (K c : Set G) = ⊥ := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨mark,hm | hm⟩ := ms_initial_moved_section_models c D hf n hn hF e
  · obtain ⟨a,ha,hL,hS,hQ⟩ := InitialCenter.exists_natural_line_and_fixed D hf hn hF mark hm
    exact ⟨mark.trans (Matrix.HigherLinear.SubspaceTransport.slConj a),Or.inl ha,hL,hS,hQ⟩
  · obtain ⟨a,ha,hL⟩ := exists_doubled_line D hf hn hF mark (movedCoreOmega c)
      (InitialCenter.fullModule_le_initial hf) hm
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
    have hc := sylow_centralizer_eq_bot_of_natural_omega c hf hlarge _ (Or.inr ha) hL.ge
    exact ⟨mark.trans (Matrix.HigherLinear.SubspaceTransport.slConj a),Or.inr ha,hL,hc,
      bot_unique ((inf_le_inf_right _ (core_le_sylow c)).trans_eq hc)⟩

/-- Source 4.3.9 on the literal Sylow intersection, from the full quotient alone. -/
theorem sylow_centralizer {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    S c ⊓ centralizer (K c : Set G) = ⊥ := by
  obtain ⟨_,_,_,hc,_⟩ := initial_line_and_centralizer D hf n hn hF e
  exact hc


/-- The component centralizer in KS is trivial. The centralizer's
commutator with O₂(KS) lies in C_S(K), and the constrained core then
places the entire centralizer inside S. -/
theorem join_centralizer {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    (K c ⊔ S c) ⊓ centralizer (K c : Set G) = ⊥ := by
  let J := K c ⊔ S c
  let P := J.pCoreIn 2
  let C := J ⊓ centralizer (K c : Set G)
  have hS := sylow_centralizer D hf n hn hF e
  have hPS : P ≤ S c := c.block_join_core_le.trans (c.core_sylow.le.trans inf_le_left)
  have hJK : J ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
  have hJC : J ≤ normalizer (C : Set G) :=
    (le_inf J.le_normalizer (hJK.trans (normalizer_le_normalizer_centralizer (K c)))).trans
      inf_normalizer_le_normalizer_inf
  have hJP : J ≤ normalizer (P : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hCP : C ⊓ P = ⊥ := bot_unique
    ((le_inf (inf_le_right.trans hPS) (inf_le_left.trans inf_le_right)).trans_eq hS)
  have hcomm : ⁅C,P⁆ = ⊥ := by
    apply bot_unique
    apply le_trans (le_inf ?_ ?_) hCP.le
    · exact (commutator_mono le_rfl (pCoreIn_le 2 J)).trans
        (le_normalizer_iff_commutator_le_left.mp hJC)
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_right.mp hJP)
  have hCcore : C ≤ P := (le_inf inf_le_left
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans (c.nonblock_join_selfCentralizing hf)
  exact bot_unique ((le_inf (hCcore.trans hPS) inf_le_right).trans_eq hS)

/-- In the whole doubled row the intrinsic component core is exactly Q,
including over the field of order four. The original ambient centralizer
kills its derived group; natural first cohomology removes the fixed factor. -/
theorem component_core_eq_of_doubled {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    (K c).pCoreIn 2 = Q c := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  have hS := sylow_centralizer D hf n hn hF e
  let P := (K c).pCoreIn 2
  have hPS : P ≤ S c := by
    rw [show P = (c.K.pCoreIn 2).map c.H.subtype from
      (map_pCoreIn_of_injective 2 c.K c.H.subtype c.H.subtype_injective).symm]
    exact ((map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
      c.c28.ambient_core_le_radical).trans (c.core_sylow.le.trans inf_le_left)
  have hQP : Q c ≤ P := le_normalizer_iff_commutator_le_left.mp
    ((K c).le_normalizer.trans (normalizer_le_normalizer_characteristic_image
      (K c) (pCore 2 (K c))))
  obtain ⟨f,he⟩ := double_coordinates e (Q c) hm
  have hPQ : ⁅P,Q c⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro p ⟨k,hk,rfl⟩ q hq
    let u : Q c := ⟨q,hq⟩
    let v := (Q c).normalizerMonoidHom ⟨k,hm.2.1 k.property⟩ u
    have hv : (v : G) = k*q*(k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hk1 : linearThreeActor e k = 1 := by
      change e (QuotientGroup.mk' (pCore 2 (K c)) k) = 1
      apply e.map_eq_one_iff.mpr
      exact (QuotientGroup.eq_one_iff k).mpr hk
    have hh := he k u v hv
    simp only [hk1,Matrix.SpecialLinearGroup.coe_one,Matrix.one_mulVec,Prod.mk.eta] at hh
    have hvu : v = u := f.injective (Multiplicative.toAdd.injective hh)
    exact (mul_inv_eq_iff_eq_mul.mp (hv.symm.trans (congrArg Subtype.val hvu))).symm
  have hPPK : ⁅⁅P,P⁆,K c⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · change ⁅Q c,P⁆ = ⊥
      rwa [commutator_comm]
    · rw [commutator_comm (K c) P]
      change ⁅Q c,P⁆ = ⊥
      rwa [commutator_comm]
  have hPP : ⁅P,P⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf (((Subgroup.commutator_le_sup P P).trans (sup_le le_rfl le_rfl)).trans hPS)
      (commutator_eq_bot_iff_le_centralizer.mp hPPK)).trans_eq hS
  have hPc : P ⊓ centralizer (K c : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hPS).trans_eq hS)
  let ρ := (Representation.specialLinearNatural (k := F) 3).prod
    (Representation.specialLinearNatural (k := F) 3)
  let := Representation.OneCohomology.SLHigherNatural.H1_subsingleton_sl3_large_field hlarge
  let := Representation.OneCohomology.H1_prod_subsingleton
    (Representation.specialLinearNatural (k := F) 3) (Representation.specialLinearNatural (k := F) 3)
  have hE (k : K c) (v) :
      (f.symm (Multiplicative.ofAdd (ρ (linearThreeActor e k) v)) : G) =
        k * (f.symm (Multiplicative.ofAdd v) : G) * (k : G)⁻¹ := by
    let u := f.symm (Multiplicative.ofAdd v)
    let w := (Q c).normalizerMonoidHom ⟨k,hm.2.1 k.property⟩ u
    have hw : (w : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hh := he k u w hw
    have hf' : f w = Multiplicative.ofAdd (ρ (linearThreeActor e k) v) := by
      apply Multiplicative.toAdd.injective
      change (f w).toAdd = ((linearThreeActor e k).val.mulVec v.1,
        (linearThreeActor e k).val.mulVec v.2)
      simpa only [u,f.apply_symm_apply,toAdd_ofAdd] using hh
    rw [←hf',f.symm_apply_apply]
    exact hw
  have hsplit := Representation.OneCohomology.sup_centralizer_eq_of_conjugation_H1
    (K c) P (Q c) hQP (linearThreeActor e)
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ρ f hE
    (fun k hk => by
      have hkP : k ∈ pCore 2 (K c) := (QuotientGroup.eq_one_iff _).mp
        (e.map_eq_one_iff.mp hk)
      exact (commutator_eq_bot_iff_le_centralizer.mp hPP) (mem_map_of_mem _ hkP))
    (fun k u => by
      change ⁅(k : G),(u : G)⁆ ∈ Q c
      change ⁅(k : G),(u : G)⁆ ∈ ⁅P,K c⁆
      rw [commutator_comm]
      exact commutator_mem_commutator k.property u.property)
  rw [hPc,sup_bot_eq] at hsplit
  exact hsplit.symm

/-- The doubled whole core is self-centralizing in the original KS.
This supplies C.1.36(1) on the actual ambient join. -/
theorem join_core_centralizer_of_doubled {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    (K c ⊔ S c) ⊓ centralizer (Q c : Set G) = Q c := by
  let C := (K c ⊔ S c) ⊓ centralizer (Q c : Set G)
  have hcore := component_core_eq_of_doubled D hf n hn hF e hm
  let a : c.K ≃* K c := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  have hcK : centralizer (pCore 2 (K c) : Set (K c)) ≤ pCore 2 (K c) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 a).mp
      (hf ▸ centralizer_generalizedFitting_le c.K)
  have hkc : K c ⊓ centralizer (Q c : Set G) ≤ Q c := by
    rw [←hcore]
    intro x hx
    apply mem_map_of_mem (K c).subtype (x := ⟨x,hx.1⟩)
    apply hcK
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp hx.2 y (mem_map_of_mem _ hy))
  have hCK : C ≤ normalizer (K c : Set G) :=
    inf_le_left.trans ((sup_le (map_subtype_le _) inf_le_right).trans c.normalizer_component.le)
  have hKQ : K c ≤ normalizer (Q c : Set G) :=
    (map_subtype_le _).trans (core_normalized c)
  have hcomm : ⁅C,K c⁆ ≤ Q c := by
    apply le_trans (le_inf (le_normalizer_iff_commutator_le_right.mp hCK) ?_) hkc
    exact (commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (hKQ.trans (normalizer_le_normalizer_centralizer (Q c))))
  obtain ⟨f,he⟩ := double_coordinates e (Q c) hm
  have habel : IsMulCommutative (Q c) :=
    ⟨⟨fun x y => f.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
  have hQC : Q c ≤ C := le_inf ((core_le_sylow c).trans le_sup_right)
    (le_centralizer_iff_isMulCommutative.mpr habel)
  have hfix : C ⊓ centralizer (K c : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ inf_le_left).trans_eq (join_centralizer D hf n hn hF e))
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  let ρ := (Representation.specialLinearNatural (k := F) 3).prod
    (Representation.specialLinearNatural (k := F) 3)
  let := Representation.OneCohomology.SLHigherNatural.H1_subsingleton_sl3_large_field hlarge
  let := Representation.OneCohomology.H1_prod_subsingleton
    (Representation.specialLinearNatural (k := F) 3) (Representation.specialLinearNatural (k := F) 3)
  have hE (k : K c) (v) :
      (f.symm (Multiplicative.ofAdd (ρ (linearThreeActor e k) v)) : G) =
        k * (f.symm (Multiplicative.ofAdd v) : G) * (k : G)⁻¹ := by
    let u := f.symm (Multiplicative.ofAdd v)
    let w := (Q c).normalizerMonoidHom ⟨k,hm.2.1 k.property⟩ u
    have hw : (w : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have hh := he k u w hw
    have hf' : f w = Multiplicative.ofAdd (ρ (linearThreeActor e k) v) := by
      apply Multiplicative.toAdd.injective
      change (f w).toAdd = ((linearThreeActor e k).val.mulVec v.1,
        (linearThreeActor e k).val.mulVec v.2)
      simpa only [u,f.apply_symm_apply,toAdd_ofAdd] using hh
    rw [←hf',f.symm_apply_apply]
    exact hw
  have hsplit := Representation.OneCohomology.sup_centralizer_eq_of_conjugation_H1
    (K c) C (Q c) hQC (linearThreeActor e)
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ρ f hE
    (fun k hk => by
      have hkP : k ∈ pCore 2 (K c) := (QuotientGroup.eq_one_iff _).mp
        (e.map_eq_one_iff.mp hk)
      have hkQ : (k : G) ∈ Q c := hcore ▸ mem_map_of_mem (K c).subtype hkP
      exact (le_centralizer_iff.mp (show C ≤ centralizer (Q c : Set G) from inf_le_right)) hkQ)
    (fun k u => by
      change ⁅(k : G),(u : G)⁆ ∈ Q c
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator k.property u.property))
  rw [hfix,sup_bot_eq] at hsplit
  exact hsplit.symm

private theorem original_sylow (D : Chapter12.Section02.ChosenModule T L V) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S c ⊓ L := by
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let e : A ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype D.sylow_normalizes_component).exists_sylow_map_eq_inf_of_normal A
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup A).map e.toMonoidHom).map L.subtype = _
  have hf : L.subtype.comp e.toMonoidHom = N.subtype.comp A.subtype := rfl
  rw [map_map,hf,←map_map,hP]
  rw [Subgroup.map_inf _ _ _ N.subtype_injective,map_subgroupOf_eq_of_le L.le_normalizer]
  change ((T : Subgroup G).subgroupOf N).map N.subtype ⊓ L = _
  rw [map_subgroupOf_eq_of_le D.sylow_normalizes_component]
  change (T : Subgroup G) ⊓ L = ((T : Subgroup G) ⊓ c.H) ⊓ L
  rw [inf_assoc,inf_eq_right.mpr (c.le_component.trans (map_subtype_le _))]

private theorem unipotent_le_line (F : Type*) [Field F] :
    unipotentSL F ≤ lineLocalSL F := inf_le_right

private theorem line_image_sylow {F : Type} [Field F] [Finite F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    ∃ P : Sylow 2 (lineLocalSL F),
      (P : Subgroup (lineLocalSL F)).map (lineLocalSL F).subtype =
        ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor e) := by
  let f := (linearThreeActor e).comp (inclusion c.le_component)
  have hfr : f.range = lineLocalSL F := by
    rw [MonoidHom.range_comp]
    have hi : (inclusion c.le_component).range = L.subgroupOf (K c) := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩; exact y.property
      · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
    rw [hi,hL]
  let f' : L →* lineLocalSL F := f.codRestrict _ (fun x => hfr.le ⟨x,rfl⟩)
  have hs : Function.Surjective f' := by
    intro y
    obtain ⟨x,hx⟩ := hfr.ge y.property
    exact ⟨x,Subtype.ext hx⟩
  obtain ⟨P,hP⟩ := original_sylow (c := c) D
  refine ⟨P.mapSurjective (f := f') hs,?_⟩
  change ((P : Subgroup L).map f').map (lineLocalSL F).subtype = _
  rw [map_map]
  change (P : Subgroup L).map f = _
  rw [←map_map]
  congr 1
  apply map_injective (K c).subtype_injective
  rw [map_map,map_subgroupOf_eq_of_le (inf_le_right.trans c.le_component)]
  exact hP

private theorem line_sylow_conjugate {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (n : ℕ) (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hL : (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    ∃ g : lineLocalSL F,
      (L.subgroupOf (K c)).map (linearThreeActor (e.trans (MulAut.conj g.val))) = lineLocalSL F ∧
      ((S c ⊓ L).subgroupOf (K c)).map
        (linearThreeActor (e.trans (MulAut.conj g.val))) = unipotentSL F := by
  obtain ⟨P,hP⟩ := line_image_sylow e D hL
  let P₀ := (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow F
    hn hF).subtype (unipotent_le_line F)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (lineLocalSL F) P P₀
  have hh := congrArg (fun Q : Sylow 2 (lineLocalSL F) =>
    (Q : Subgroup (lineLocalSL F)).map (lineLocalSL F).subtype) hg
  have he : (((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor e)).map
      (MulAut.conj g.val).toMonoidHom = unipotentSL F := by
    change ((P : Subgroup (lineLocalSL F)).map
      (MulAut.conj g).toMonoidHom).map (lineLocalSL F).subtype = _ at hh
    have hf : (lineLocalSL F).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g.val).toMonoidHom.comp (lineLocalSL F).subtype := rfl
    rw [map_map,hf,←map_map,hP] at hh
    change _ = ((unipotentSL F).subgroupOf (lineLocalSL F)).map
      (lineLocalSL F).subtype at hh
    rwa [map_subgroupOf_eq_of_le (unipotent_le_line F)] at hh
  refine ⟨g,?_,?_⟩
  · change (L.subgroupOf (K c)).map
      ((MulAut.conj g.val).toMonoidHom.comp (linearThreeActor e)) = _
    rw [←map_map,hL]
    exact mem_normalizer_iff_map_conj_eq.mp ((lineLocalSL F).le_normalizer g.property)
  · change ((S c ⊓ L).subgroupOf (K c)).map
      ((MulAut.conj g.val).toMonoidHom.comp (linearThreeActor e)) = _
    rwa [←map_map]

omit [Finite G] in
private theorem section_conjugate {B A F : Type*} [Group B] [AddCommGroup A]
    [Field F] [Module F A] {J P C : Subgroup G} {a : J →* B}
    {rho : Representation F B A} (hm : HasSectionModel J P C a rho) (g : B) :
    HasSectionModel J P C ((MulAut.conj g).toMonoidHom.comp a) rho := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (rho.asGroupHom g)
  apply hm.transport e.toAddEquiv
  intro x v
  change rho g (rho (a x) v) = rho (g * a x * g⁻¹) (rho g v)
  simp only [← Module.End.mul_apply,← map_mul]
  simp

/-- Simultaneous line and Sylow markings for the entire original Q, preserving
the same full quotient on both summands and both intrinsic core conclusions. -/
theorem whole_doubled_line_and_core {F : Type} [Field F] [Finite F]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (Q c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)) ∧
      (L.subgroupOf (K c)).map (linearThreeActor mark) = lineLocalSL F ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor mark) = unipotentSL F ∧
      S c ⊓ centralizer (K c : Set G) = ⊥ ∧ (K c).pCoreIn 2 = Q c ∧
      (K c ⊔ S c) ⊓ centralizer (Q c : Set G) = Q c := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨a,ha,hL⟩ := exists_doubled_line D hf hn hF e (Q c) (fullModule_lt_core c hf).le hm
  let e' := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)
  obtain ⟨g,hgL,hgS⟩ := line_sylow_conjugate D n (by omega) hF e' hL
  exact ⟨e'.trans (MulAut.conj g.val),section_conjugate ha g.val,hgL,hgS,
    sylow_centralizer D hf n hn hF e,component_core_eq_of_doubled D hf n hn hF e hm,
    join_core_centralizer_of_doubled D hf n hn hF e hm⟩

/-- The exact original five rows now yield a fully oriented doubled whole core
or the constructed third-row MS witness, with no nonabelianity premise. The
doubled-row exclusion and whole-core classification are still required. -/
theorem marked_doubled_or_msData
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ ChapterC.IsBlock c.K)
    (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hm : MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F.Carrier e) :
    (∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier),
      HasSectionModel (K c) (Q c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F.Carrier) 3).prod
          (Representation.specialLinearNatural (k := F.Carrier) 3)) ∧
      (L.subgroupOf (K c)).map (linearThreeActor mark) = lineLocalSL F.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor mark) = unipotentSL F.Carrier ∧
      S c ⊓ centralizer (K c : Set G) = ⊥ ∧ (K c).pCoreIn 2 = Q c ∧
      (K c ⊔ S c) ⊓ centralizer (Q c : Set G) = Q c ∧
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P) ∨
    (∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) := by
  rcases source_doubled_or_msData D hf hb n hn F hdegree e P hP hm with hd | hd
  · have hF : Nat.card F.Carrier = 2^n := F.card_eq.trans (congrArg (2^·) hdegree)
    obtain ⟨mark,hmodel,hline,hSylow,hC,hcore,hCQ⟩ := whole_doubled_line_and_core D hf n hn hF e hd.1
    exact Or.inl ⟨mark,hmodel,hline,hSylow,hC,hcore,hCQ,hd.2⟩
  · exact Or.inr hd

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.DoubledMarking
