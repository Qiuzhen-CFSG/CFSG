module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.QuotientInduction

/-!
# Semisimplicity of the original reducible binary moved module

The first two noncentral factors of the purified chief flag form an actual
double-natural extension. B.4.9 splits that extension; its two summands become
disjoint natural submodules of the original action. Removing either summand
gives the faithful smaller source action established in QuotientInduction.
The resulting semisimple quotients embed the original module in their product.
This proves full semisimplicity without assuming a decomposition of the socle.

The final theorem starts with the original B.5.1 hypotheses and the actual
binary SL4/SL5 component mark. It discharges G=L, passes to the literal moved
module and chief flag, and narrows the dimension induction correctly. Earlier
B.4.2 and the genuine smaller-dimension induction remain its stated inputs.
The subsequent identification of the semisimple sum as repeated natural or
natural-plus-dual remains a separate reconstruction step.

Source: Aschbacher--Smith, B.5.1, printed pp.101--102, binary cases (A)--(C)
and B.4.9(2)(i). The two-quotient argument uniformly treats the splitting step.
-/

public section
open Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory Subgroup
open scoped MonoidAlgebra MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem binary_natural_faithful {d : ℕ}
    (hn : IsLinearNatural ρ BinaryField.two d) : Function.Injective ρ := by
  obtain ⟨a⟩ := hn
  change ActionEquiv ρ (specialLinearNatural (k := ZMod 2) d) at a
  intro g h he
  apply a.groupEquiv.injective
  apply specialLinearNatural_injective d
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := a.linearEquiv.surjective v
  rw [← a.intertwines,← a.intertwines]
  exact congrArg a.linearEquiv (LinearMap.congr_fun he w)

private theorem binary_natural_submodule_ne_bot (U : Subrepresentation ρ) {d : ℕ}
    (hd : 2 ≤ d) (hn : IsLinearNatural U.toRepresentation BinaryField.two d) :
    U.toSubmodule ≠ ⊥ := by
  obtain ⟨a⟩ := hn
  let : IsIrreducible U.toRepresentation := ExtensionConsequences.irreducible_of_equiv a
    (ExtensionConsequences.linearNatural_irreducible _ hd)
  let : Nontrivial U.toSubmodule := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  exact Submodule.nontrivial_iff_ne_bot.mp inferInstance

/-- The first double-natural extension gives two actual disjoint natural
submodules of the original action. Both markings are retained through the
literal inclusion and quotient maps. -/
theorem two_natural_kernels_of_extension [Finite G] [FiniteDimensional (ZMod 2) V]
    (hff : IsFFModule ρ) (U W : Subrepresentation ρ) (hUW : U ≤ W)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hnU : IsLinearNatural U.toRepresentation BinaryField.two d)
    (hnQ : IsLinearNatural (sectionRepresentation ρ U W) BinaryField.two d) :
    ∃ C : Subrepresentation ρ, Disjoint U.toSubmodule C.toSubmodule ∧
      IsLinearNatural C.toRepresentation BinaryField.two d ∧
      U.toSubmodule ≠ ⊤ ∧ C.toSubmodule ≠ ⊤ := by
  let N := sectionLower ρ U W
  let q := sectionLowerEquiv ρ hUW
  obtain ⟨a⟩ := hnU
  let b : ActionEquiv N.toRepresentation (linearNatural BinaryField.two d) :=
    ⟨a.groupEquiv,q.trans a.linearEquiv,fun g v => a.intertwines g (q v)⟩
  have hWfaith : Function.Injective W.toRepresentation := by
    intro g h he
    apply binary_natural_faithful U.toRepresentation ⟨a⟩
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun w : W.toSubmodule => w.val)
      (LinearMap.congr_fun he (⟨v.val,hUW v.property⟩ : W.toSubmodule))
  let D : NaturalExtensions.DoubleNatural BinaryField.two d W.toRepresentation :=
    ⟨hWfaith,N,b,binary_naturals_same_or_dual N.quotientRepresentation N.toRepresentation hd hnQ ⟨b⟩⟩
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
  have hffW : IsFFModule W.toRepresentation :=
    ⟨A,(bestOffender_on_subrepresentation ρ W hA).isOffender _⟩
  obtain ⟨C,hC⟩ := doubleNatural_ff_splits D (Or.inr ⟨rfl,by omega⟩) hffW
  let j : C.toSubmodule →ₗ[ZMod 2] V := W.toSubmodule.subtype.comp C.toSubmodule.subtype
  have hj : Function.Injective j := W.toSubmodule.subtype_injective.comp C.toSubmodule.subtype_injective
  let J : Subrepresentation ρ := ⟨j.range,by
    rintro g v ⟨c,rfl⟩
    exact ⟨C.toRepresentation g c,rfl⟩⟩
  let E : C.toSubmodule ≃ₗ[ZMod 2] J.toSubmodule := LinearEquiv.ofInjective j hj
  have hE (g : G) (c : C.toSubmodule) : E (C.toRepresentation g c) = J.toRepresentation g (E c) := by
    apply Subtype.ext
    rfl
  let Q : C.toSubmodule ≃ₗ[ZMod 2] (W.toSubmodule ⧸ N.toSubmodule) :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm
  have hQ (g : G) (c : C.toSubmodule) : Q (C.toRepresentation g c) =
      N.quotientRepresentation g (Q c) := rfl
  obtain ⟨aQ⟩ := hnQ
  have hJnat : IsLinearNatural J.toRepresentation BinaryField.two d := by
    refine ⟨⟨aQ.groupEquiv,(E.symm.trans Q).trans aQ.linearEquiv,?_⟩⟩
    intro g v
    change aQ.linearEquiv (Q (E.symm (J.toRepresentation g v))) = _
    have he : E.symm (J.toRepresentation g v) = C.toRepresentation g (E.symm v) := by
      apply E.injective
      rw [E.apply_symm_apply,hE,E.apply_symm_apply]
    rw [he,hQ]
    exact aQ.intertwines g (Q (E.symm v))
  have hdis : Disjoint U.toSubmodule J.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    rintro v hv ⟨c,rfl⟩
    have hz : c.val = 0 := Submodule.disjoint_def.mp hC.disjoint c.val hv c.property
    exact congrArg (fun w : W.toSubmodule => w.val) hz
  exact ⟨J,hdis,hJnat,
    hdis.symm.ne_top_of_ne_bot (binary_natural_submodule_ne_bot ρ J (by omega) hJnat),
    hdis.ne_top_of_ne_bot (binary_natural_submodule_ne_bot ρ U (by omega) ⟨a⟩)⟩

/-- Splitting only the first double-natural extension suffices for the full
binary semisimplicity induction. -/
theorem binary_semisimple_of_natural_extension [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}}
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤) (hcore : pCore 2 G = ⊥)
    (hm : Coinvariants.ker ρ = ⊤) (hz : ρ.invariants = ⊥)
    (hff : IsFFModule ρ) (U W : Subrepresentation ρ) (hUW : U ≤ W)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hnU : IsLinearNatural U.toRepresentation BinaryField.two d)
    (hnQ : IsLinearNatural (sectionRepresentation ρ U W) BinaryField.two d) :
    IsSemisimpleRepresentation ρ := by
  obtain ⟨C,hdis,hnC,hU,hC⟩ := two_natural_kernels_of_extension ρ hff U W hUW hd hnU hnQ
  exact binary_semisimple_of_two_natural_kernels ρ ih hsq hwhole hcore hm hz hff U C
    hdis hU hC (by omega) hnU hnC


private theorem natural_of_whole_fitting {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (τ : Representation (ZMod 2) G X) (hwhole : generalizedFitting G = ⊤) {d : ℕ}
    (hn : IsLinearNatural (τ.comp (generalizedFitting G).subtype) BinaryField.two d) :
    IsLinearNatural τ BinaryField.two d := by
  obtain ⟨a⟩ := hn
  rw [hwhole] at a
  exact ⟨a.ofTop⟩

/-- The central-free source flag supplies the initial double-natural extension,
so the complete binary action is semisimple by strict quotient induction. -/
theorem binary_semisimple_of_natural_flag [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}}
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤) (hcore : pCore 2 G = ⊥)
    (hm : Coinvariants.ker ρ = ⊤) (hz : ρ.invariants = ⊥) (hff : IsFFModule ρ)
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (hindices : f.noncentral = Finset.range f.length)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hn : ∀ i < f.length, IsLinearNatural
      ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp (generalizedFitting G).subtype)
      BinaryField.two d) : IsSemisimpleRepresentation ρ := by
  have hlen : 1 < f.length := by
    have hh := f.multiple
    rw [hindices,Finset.card_range] at hh
    exact hh
  apply binary_semisimple_of_natural_extension ρ ih hsq hwhole hcore hm hz hff
    (f.chain 1) (f.chain 2) (f.monotone (by omega)) hd
  · exact natural_of_whole_fitting _ hwhole
      (first_chief_natural ρ (generalizedFitting G) f (hn 0 (by omega)))
  · exact natural_of_whole_fitting _ hwhole (hn 1 hlen)

private theorem coinvariants_top_of_actionEquiv
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) H X} (e : ActionEquiv ρ σ)
    (hm : Coinvariants.ker ρ = ⊤) : Coinvariants.ker σ = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  have he : Coinvariants.ker ρ ≤ (Coinvariants.ker σ).comap e.linearEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    change e.linearEquiv (ρ g w - w) ∈ Coinvariants.ker σ
    rw [map_sub,e.intertwines]
    exact Coinvariants.sub_mem_ker (e.groupEquiv g) (e.linearEquiv w)
  exact he (hm ▸ Submodule.mem_top)

/-- The original reducible binary B.5.1 hypotheses imply G=L and semisimplicity
of the actual moved module. All quotient and first-extension premises of the
strict dimension argument are discharged here. -/
theorem binary_moved_semisimple [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : L ≃* SL(d,ZMod 2)) :
    L = ⊤ ∧ ∃ s : MovedSection ρ L, IsSemisimpleRepresentation s.space.toRepresentation := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  have hL := binary_reducible_whole ρ hK earlier h hnot hd mark
  have hfit := binary_source_fitting ρ h hd mark
  obtain ⟨s,A,hA,f,hindices,hn,hpure⟩ := binary_moved_pure_flag ρ hK earlier h hnot hd mark
  let μ := s.space.toRepresentation
  let H := L ⊔ A
  let σ : Representation (ZMod 2) H s.space.toSubmodule := μ.comp H.subtype
  have hH : H = ⊤ := by change L ⊔ A = ⊤; rw [hL,top_sup_eq]
  have hμ := moved_source_hypothesis ρ h s hfit
  have hl := local_source_hypothesis μ L h.sqtk hfit h.twoCore hμ.faithful hA.1
  have hfitH : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore (hA.1.1.2.isPGroup 2 A)
  have hwhole : generalizedFitting H = ⊤ := by
    simp only [hfitH,hL,Subgroup.top_subgroupOf]
  let : IsQuasisimple (generalizedFitting H) := hfitH.symm ▸ hl.quasisimple
  have hsq : IsSQTK K (generalizedFitting H) := hfitH.symm ▸ hl.sqtk
  let E : ActionEquiv ((⊤ : Subrepresentation σ).toRepresentation.comp (generalizedFitting H).subtype) σ :=
    ⟨(MulEquiv.subgroupCongr hwhole).trans Subgroup.topEquiv,Submodule.topEquiv,fun _ _ => rfl⟩
  have ht := hpure f.length le_rfl
  rw [f.top] at ht
  have hm : Coinvariants.ker σ = ⊤ := coinvariants_top_of_actionEquiv _ E ht.1
  have hz : σ.invariants = ⊥ := ExtensionConsequences.invariants_of_equiv
    (ExtensionConsequences.actionSymm E) ht.2
  have hff : IsFFModule σ :=
    ⟨A.subgroupOf H,((hA.1.subgroupOf μ le_sup_right).isOffender _)⟩
  have ihU : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) s.space.toSubmodule) := by
    intro D _ _ X _ _ _ τ C hdX hs
    exact ih D X τ C (hdX.trans_le (Submodule.finrank_le _)) hs
  have hsem := binary_semisimple_of_natural_flag σ ihU hsq hwhole hl.twoCore hm hz hff
    f hindices hd (fun i hi => (hn i hi).2.2)
  let e : ActionEquiv σ μ :=
    ⟨(MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  exact ⟨hL,s,semisimple_of_actionEquiv μ (ExtensionConsequences.actionSymm e) hsem⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
