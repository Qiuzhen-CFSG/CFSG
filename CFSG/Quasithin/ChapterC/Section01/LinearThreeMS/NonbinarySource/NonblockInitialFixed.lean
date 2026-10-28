module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialCenter
public import Theory.SpecificGroups.PSL3.LinearThreeRootFixed
public import Theory.GroupTheory.PCoreImage

/-!
# Original nonblock fixed factors from both initial module alternatives

The original full module W centralizes O₂(L). Under a point marking, the
literal full quotient carries this local core onto the point radical.
That radical fixes only the distinguished point on each natural summand,
and the point local fixes that point elementwise. Thus either a natural
or a doubled natural initial layer would make L centralize W, contrary
to [W,L]=W≠1. The original local group consequently has the line marking.

The initial cohomology splitting and the original crossing-normalizer
argument now give C_S(K)=C_Q(K)=1 in both initial branches, including
field four. The actual fourth-row fixed-factor order is therefore excluded
in this original ambient configuration, without its disputed ambient
centrality clause. One linear change of basis preserves the supplied
initial model and quotient marking. The final application supplies the
initial alternatives from the genuine MS-pair of the original configuration.

This proves the fixed-factor input of original 4.3.9 before whole-section
recognition. It does not identify the entire center or Frattini sections,
or assert the universal C.1.34 classification. The point-core argument
also follows the original symplectic-point exclusion pattern in
Chapter4.Section03.RankOneUniqueness.BlockSymplectic.Parabolic.
Source: Aschbacher--Smith C.1.34, pp.136--137, C.4.7, p.153, and
original 4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.InitialFixed
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

private theorem fullModule_core_fixed : W c ≤ centralizer (L.pCoreIn 2 : Set G) := by
  have hIN : c.I ≤ normalizer (L : Set G) := by
    rw [c.I_eq]
    exact sup_le L.le_normalizer (c.c28.radical_le.trans inf_le_right)
  have hcore : L.pCoreIn 2 ≤ c.I.pCoreIn 2 := pCoreIn_mono_of_normalizes c.le_I hIN
  intro w hw a ha
  obtain ⟨v,hv,hvw⟩ := c.c28.module_le_center_radical hw
  have hc := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
    (mem_center_iff.mp hv ⟨a,hcore ha⟩)
  change a * (v : G) = (v : G) * a at hc
  change (v : G) = w at hvw
  rwa [hvw] at hc

omit [Finite G] in
private theorem fullModule_moved : ⁅W c,L⁆ = W c := by
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  exact (show W c = ⁅W c,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm

private theorem point_fixed_of_radical {F : Type*} [Field F] (v : Fin 3 → F)
    (hv : ∀ g : pointLocalSL F, g ∈ pointRadicalSL F →
      specialLinearNatural 3 g.val v = v) :
    ∀ g ∈ pointLocalSL F, specialLinearNatural 3 g v = v := by
  obtain ⟨a,rfl⟩ := (pointRadicalSL_fixed_iff F v).mp hv
  intro g hg
  change g.val.mulVec (a • (![1,0,0] : Fin 3 → F)) = _
  rw [Matrix.mulVec_smul,show g.val.mulVec (![1,0,0] : Fin 3 → F) = ![1,0,0] from hg]

private theorem not_point_of_model {F : Type} [Field F] [Finite F] [CharP F 2]
    {E : Type*} [AddCommGroup E] [Module F E]
    (rho : Representation F SL(3,F) E)
    (hfixed : ∀ v : E, (∀ g : pointLocalSL F, g ∈ pointRadicalSL F → rho g.val v = v) →
      ∀ g ∈ pointLocalSL F, rho g v = v)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e) rho) :
    (L.subgroupOf (K c)).map (linearThreeActor e) ≠ pointLocalSL F := by
  intro hp
  let p := linearThreeActor e
  let A := L.subgroupOf (K c)
  have hk : p.ker = pCore 2 (K c) := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K c)))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hcore : (A.pCoreIn 2).map p =
      (pointRadicalSL F).map (pointLocalSL F).subtype := by
    rw [map_pCoreIn_of_ker_isPGroup p (hk ▸ pCore_isPGroup),hp]
    change (pCore 2 (pointLocalSL F)).map (pointLocalSL F).subtype = _
    rw [pointLocalSL_twoCore_eq]
  have hmap : (A.pCoreIn 2).map (K c).subtype = L.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 A _ (K c).subtype_injective,
      map_subgroupOf_eq_of_le c.le_component]
  have hnorm := hm.2.1
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,f,he⟩ := hm
  let := hn
  let a : movedCoreOmega c ≃* Multiplicative E := QuotientGroup.quotientBot.symm.trans f
  have ha (k : K c) (u v : movedCoreOmega c)
      (hv : (v : G) = k * (u : G) * (k : G)⁻¹) :
      (a v).toAdd = rho (p k) (a u).toAdd := he k u v hv
  have hpoint (u : movedCoreOmega c) (hu : (u : G) ∈ W c) :
      ∀ g ∈ pointLocalSL F, rho g (a u).toAdd = (a u).toAdd := by
    apply hfixed
    intro g hg
    have hh : g.val ∈ (A.pCoreIn 2).map p := hcore.symm ▸ mem_map_of_mem _ hg
    obtain ⟨k,hk,hkg⟩ := hh
    rw [←hkg]
    have hkL : (k : G) ∈ L.pCoreIn 2 := hmap ▸ mem_map_of_mem _ hk
    exact (ha k u u (by
      rw [fullModule_core_fixed hu k hkL,mul_inv_cancel_right])).symm
  have hc : ⁅W c,L⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro w hw l hl
    let u : movedCoreOmega c := ⟨w,InitialCenter.fullModule_le_initial hf hw⟩
    let k : K c := ⟨l,c.le_component hl⟩
    let u' : movedCoreOmega c := (movedCoreOmega c).normalizerMonoidHom ⟨k,hnorm k.property⟩ u
    have hu' : (u' : G) = l*w*l⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have heq : a u' = a u := Multiplicative.toAdd.injective
      ((ha k u u' hu').trans (hpoint u hw (p k) (hp ▸ mem_map_of_mem p hl)))
    have hh : l*w*l⁻¹ = w := hu'.symm.trans (congrArg Subtype.val (a.injective heq))
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact c.c28.module_nontrivial ((fullModule_moved (c := c)).symm.trans hc)

private theorem initial_line {F : Type} [Field F] [Finite F] [CharP F 2]
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        (specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    (hp : (L.subgroupOf (K c)).map (linearThreeActor e) = pointLocalSL F ∨
      (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F) :
    (L.subgroupOf (K c)).map (linearThreeActor e) = lineLocalSL F := by
  apply hp.resolve_left
  rcases hm with hm | hm
  · exact not_point_of_model _ point_fixed_of_radical hf e hm
  · apply not_point_of_model _ ?_ hf e hm
    intro v hv g hg
    exact Prod.ext
      (point_fixed_of_radical v.1 (fun r hr => congrArg Prod.fst (hv r hr)) g hg)
      (point_fixed_of_radical v.2 (fun r hr => congrArg Prod.snd (hv r hr)) g hg)

private theorem natural_reframe {F : Type*} [Field F]
    (a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (g : SL(3,F)) (v : Fin 3 → F) :
    a (specialLinearNatural 3 g v) =
      specialLinearNatural 3 (Matrix.HigherLinear.SubspaceTransport.slConj a g) (a v) := by
  symm
  simpa only [specialLinearNatural_apply,LinearEquiv.symm_apply_apply,
    Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply] using
    Matrix.HigherLinear.SubspaceTransport.slConj_apply a g (a v)

/-- Both initial module alternatives carry the line marking and the source fixed-factor exclusion. -/
theorem exists_reframed_initial_line_and_fixed {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        (specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) :
    ∃ a : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      let mark := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)
      (HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        (specialLinearNatural (k := F) 3) ∨
       HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) ∧
      (L.subgroupOf (K c)).map (linearThreeActor mark) = lineLocalSL F ∧
      S c ⊓ centralizer (K c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (K c : Set G) = ⊥ := by
  obtain ⟨a,ha⟩ := nonblock_linearThree_local_frame D hf hn hF e
  let e' := e.trans (Matrix.HigherLinear.SubspaceTransport.slConj a)
  have hm' : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e')
        (specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e')
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)) := by
    rcases hm with hm | hm
    · exact Or.inl (hm.transport a.toAddEquiv (fun k v => natural_reframe a (linearThreeActor e k) v))
    · apply Or.inr
      exact hm.transport (a.prodCongr a).toAddEquiv (fun k v =>
        Prod.ext (natural_reframe a (linearThreeActor e k) v.1)
          (natural_reframe a (linearThreeActor e k) v.2))
  have hline := initial_line hf e' hm' ha
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  have hc := sylow_centralizer_eq_bot_of_natural_omega c hf hlarge e' hm' hline.ge
  exact ⟨a,hm',hline,hc,bot_unique ((inf_le_inf_right _ (core_le_sylow c)).trans_eq hc)⟩

/-- Original 4.3.9 from the full quotient and the proved initial alternatives,
without assuming any whole central or Frattini section model. -/
theorem exists_initial_line_and_fixed {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      (HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        (specialLinearNatural (k := F) 3) ∨
       HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) ∧
      (L.subgroupOf (K c)).map (linearThreeActor mark) = lineLocalSL F ∧
      S c ⊓ centralizer (K c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (K c : Set G) = ⊥ := by
  obtain ⟨mark,hm⟩ := ms_initial_moved_section_models c D hf n hn hF e
  obtain ⟨a,ha⟩ := exists_reframed_initial_line_and_fixed D hf hn hF mark hm
  exact ⟨mark.trans (Matrix.HigherLinear.SubspaceTransport.slConj a),ha⟩

/-- The original whole fixed factor is trivial in both initial branches,
including field four. This excludes the fourth source row without using its
disputed ambient-centrality clause. -/
theorem source_fixed_factors {F : Type} [Field F] [Finite F] [CharP F 2]
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    S c ⊓ centralizer (K c : Set G) = ⊥ ∧
      Q c ⊓ centralizer (K c : Set G) = ⊥ ∧
      Nat.card (Q c ⊓ centralizer (K c : Set G) : Subgroup G) ≠ 2^(2*n) := by
  obtain ⟨mark,_,_,hS,hQ⟩ := exists_initial_line_and_fixed D hf hn hF e
  refine ⟨hS,hQ,?_⟩
  rw [hQ,Subgroup.card_bot]
  have hh : 2^0 < 2^(2*n) := Nat.pow_lt_pow_right (by decide) (by omega)
  exact (show 1 < 2^(2*n) from by simpa using hh).ne

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.InitialFixed
