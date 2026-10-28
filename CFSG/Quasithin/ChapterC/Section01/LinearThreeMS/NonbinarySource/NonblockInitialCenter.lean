module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSNaturalCenter
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSParabolicMarking

/-!
# Orienting the natural initial layer in the original nonblock configuration

The original source module W lies in the initial moved omega layer A:
W is elementary, centralizes the original radical and lies in Q, hence
lies in the central omega of O₂(KS); now [W,L]=W puts it in A.
It is proper in A because the original K does not normalize L.

If A is natural, a point-parabolic marking would fix every proper invariant
additive subgroup, contradicting [W,L]=W. Thus the original L has the line
marking. The existing initial cohomology and crossing-normalizer argument
then proves C_S(K)=C_Q(K)=1, without a whole-center recognition hypothesis.
The final application uses the unconditional initial natural/doubled
classification: its natural branch now includes this line marking and both
centralizer conclusions, while its doubled branch retains the full module
and every eligible Sylow radical inequality.

These are original-ambient consequences of the initial layer. They do not
identify all of Z(Q), Q/Z(Q), or the upper Frattini sections and do not
establish the remaining C.1.34 alternatives. All statements include field
four and retain the original full quotient and actual Sylow intersection.
Source: Aschbacher--Smith original 4.3.8--10, pp.616--617, C.1.34,
pp.136--137, and C.4.7, p.153.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.InitialCenter
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

omit [Finite G] in
private theorem fullModule_moved : ⁅W c,L⁆ = W c := by
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  exact (show W c = ⁅W c,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm

private theorem fullModule_le_initialOmega (hf : generalizedFitting c.K = pCore 2 c.K) :
    W c ≤ coreOmega c := by
  have hQN : Q c ≤ (K c ⊔ S c).pCoreIn 2 := by
    rw [←sylow_join_commutator_eq]
    exact le_normalizer_iff_commutator_le_left.mp
      ((le_sup_left : K c ≤ K c ⊔ S c).trans
        ((K c ⊔ S c).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
            (pCore 2 (K c ⊔ S c : Subgroup G)))))
  intro w hw
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨hQN ((fullModule_lt_core c hf).le hw),?_,?_⟩
  · intro q hq
    obtain ⟨z,hz,hzw⟩ := c.c28.module_le_center_radical hw
    have hh := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
      (mem_center_iff.mp hz ⟨q,c.block_join_core_le hq⟩)
    have hzw' : (z : G) = w := hzw
    simpa only [Subgroup.coe_mul,hzw'] using hh
  · let := c.c28.module_elementary
    exact congrArg (W c).subtype
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (W c)) ⟨w,hw⟩)

/-- The original source module is contained in the initial moved omega layer. -/
theorem fullModule_le_initial (hf : generalizedFitting c.K = pCore 2 c.K) :
    W c ≤ movedCoreOmega c := by
  rw [←fullModule_moved (c := c)]
  exact commutator_mono (fullModule_le_initialOmega hf) c.le_component

private theorem fullModule_lt_initial (hf : generalizedFitting c.K = pCore 2 c.K) :
    W c < movedCoreOmega c := by
  apply lt_of_le_of_ne (fullModule_le_initial hf)
  intro he
  have hn : K c ≤ normalizer (W c : Set G) := by
    rw [he]
    exact normalizer_commutator_ge_right _ _
  exact c.component_outside ((le_inf (map_subtype_le _) hn).trans
    (c.c28.module_normalizer.trans inf_le_right))

private theorem natural_initial_line {F : Type*} [Field F]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hp : (L.subgroupOf (K c)).map (linearThreeActor e) = pointLocalSL F ∨
      (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F := by
  rcases hp with hp | hp
  · exfalso
    rw [HasSectionModel,bot_subgroupOf] at hm
    obtain ⟨_,_,_,hn,a,ha⟩ := hm
    let := hn
    let E : movedCoreOmega c ≃* Multiplicative (Fin 3 → F) :=
      QuotientGroup.quotientBot.symm.trans a
    let B := (((W c).subgroupOf (movedCoreOmega c)).map E.toMonoidHom).toAddSubgroup'
    have hproper : B ≠ ⊤ := by
      intro ht
      apply (fullModule_lt_initial hf).not_ge
      intro x hx
      have hh : (E ⟨x,hx⟩).toAdd ∈ B := ht ▸ trivial
      obtain ⟨w,hw,hew⟩ := hh
      have hwx : w = ⟨x,hx⟩ := E.injective hew
      change (w : G) ∈ W c at hw
      simpa only [hwx] using hw
    have hnW : L ≤ normalizer (W c : Set G) := by
      apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm,fullModule_moved]
    have hinv : ∀ g ∈ pointLocalSL F, ∀ v ∈ B, g.val.mulVec v ∈ B := by
      intro g hg v hv
      obtain ⟨k,hk,rfl⟩ := hp.ge hg
      obtain ⟨u,hu,rfl⟩ := hv
      let w : movedCoreOmega c := (movedCoreOmega c).normalizerMonoidHom
        ⟨k,normalizer_commutator_ge_right (coreOmega c) (K c) k.property⟩ u
      have hw : (w : G) = k * (u : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
      have he : (E w).toAdd = (linearThreeActor e k).val.mulVec (E u).toAdd := ha k u w hw
      refine ⟨w,?_,Multiplicative.toAdd.injective he⟩
      change (w : G) ∈ W c
      rw [hw]
      exact (mem_normalizer_iff.mp (hnW hk) u).mp hu
    have hfixed := Representation.SL3ParabolicNatural.point_invariant_fixed B hproper hinv
    have hcomm : ⁅W c,L⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro w hw l hl
      let u : movedCoreOmega c := ⟨w,fullModule_le_initial hf hw⟩
      let k : K c := ⟨l,c.le_component hl⟩
      let u' : movedCoreOmega c := (movedCoreOmega c).normalizerMonoidHom
        ⟨k,normalizer_commutator_ge_right (coreOmega c) (K c) k.property⟩ u
      have hu' : (u' : G) = l*w*l⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
      have he : (E u').toAdd = (linearThreeActor e k).val.mulVec (E u).toAdd := ha k u u' hu'
      have hfix := hfixed (linearThreeActor e k) (hp.le (mem_map_of_mem _ hl))
        (E u).toAdd (show (E u).toAdd ∈ B from ⟨u,hw,rfl⟩)
      have hue : u' = u := E.injective (Multiplicative.toAdd.injective (he.trans hfix))
      have hh : l*w*l⁻¹ = w := hu'.symm.trans (congrArg Subtype.val hue)
      exact mul_inv_eq_iff_eq_mul.mp hh
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

/-- A natural initial moved layer already orients the original local group
and kills both the Sylow and whole-core component centralizers. -/
theorem exists_natural_line_and_fixed {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3)) :
    ∃ a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      let e' := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e')
        (Representation.specialLinearNatural (k := F) 3) ∧
      (L.subgroupOf (K c)).map (linearThreeActor e') = lineLocalSL F ∧
      S c ⊓ centralizer (K c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (K c : Set G) = ⊥ := by
  obtain ⟨a,ha⟩ := nonblock_linearThree_local_frame D hf hn hF e
  let e' := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)
  have hm' : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e')
      (Representation.specialLinearNatural (k := F) 3) :=
    hm.transport a.toAddEquiv (fun k v => natural_reframe a (linearThreeActor e k) v)
  have hline := natural_initial_line hf e' hm' ha
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  have hc := sylow_centralizer_eq_bot_of_natural_omega c hf hlarge e' (Or.inl hm') hline.ge
  exact ⟨a,hm',hline,hc,bot_unique ((inf_le_inf_right _ (core_le_sylow c)).trans_eq hc)⟩

/-- The original initial-layer classification now supplies its own line
marking and fixed-factor exclusion in the natural branch. The doubled
branch retains its full model and every original Sylow radical inequality. -/
theorem initial_marked_alternatives {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      (HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        (Representation.specialLinearNatural (k := F) 3) ∧
        (L.subgroupOf (K c)).map (linearThreeActor mark) = lineLocalSL F ∧
        S c ⊓ centralizer (K c : Set G) = ⊥ ∧
        Q c ⊓ centralizer (K c : Set G) = ⊥) ∨
      (HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)) ∧
        ∀ P : Subgroup G, Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2) →
          c.I.pCoreIn 2 ≤ P → MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P) := by
  obtain ⟨mark,hm | hm⟩ := ms_initial_moved_section_models c D hf n hn hF e
  · obtain ⟨a,ha,hline,hS,hQ⟩ := exists_natural_line_and_fixed D hf hn hF mark hm
    exact ⟨mark.trans (Matrix.HigherLinear.SubspaceTransport.slConj a),
      Or.inl ⟨ha,hline,hS,hQ⟩⟩
  · refine ⟨mark,Or.inr ⟨hm,?_⟩⟩
    intro P hP hRP
    apply ChapterC.LinearThreeMS.NonbinarySource.RadicalInitial.notCentralizerCore_of_initial_doubled
      (msPair_of_quotient c D hf n (by omega) hF e) hn mark _ hP hRP
    simpa only [ms_initialMoved_eq] using hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.InitialCenter
