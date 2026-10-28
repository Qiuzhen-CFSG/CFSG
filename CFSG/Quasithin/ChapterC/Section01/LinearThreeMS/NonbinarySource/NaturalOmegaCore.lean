module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralSections
public import Mathlib.GroupTheory.FixedPointFree
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.Frattini.PGroup

/-!
# Normal layers beneath a natural central omega

A natural whole Ω₁(Z(Q)) is irreducible even as an additive group. Every
nontrivial subgroup of the two-group Q normalized by Q and K meets that
omega and therefore contains it. In particular, when Q is nonabelian,
the entire omega lies in Q' and Φ(Q). For the original MS core it is
exactly the initial moved subgroup, without identifying Z(Q) with Ω₁(Z(Q)).

A determinant-one companion matrix has no fixed vectors on the natural
module or its double. Its lift to K fixes no central involution, hence no
nonidentity element of the finite two-group Z(Q). Surjectivity of the
commutator map gives [Z(Q),K]=Z(Q) and C_Z(Q)(K)=1. This argument needs
neither a nonidentity quotient scalar nor a hypothesis C_Q(K)=1, and
retains possible higher exponent of the whole center.

NonblockNaturalOmegaCore applies both calculations to the original
configuration, retaining the canonical homocyclic lift and the doubled
omega alternatives. Exclusion of these remaining nonabelian alternatives
and construction of the upper sections are still required for C.1.34.
Source: Aschbacher–Smith C.1.34, printed pp.136–137, and original
4.3.8–10, pp.616–617; the normal-layer and fixed-point arguments are elementary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NaturalOmegaCore
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {K Q W : Subgroup G}
variable {F : Type} [Field F]

private theorem exists_fixedFree_matrix :
    ∃ g : SL(3,F), ∀ v : Fin 3 → F, specialLinearNatural 3 g v = v → v = 0 := by
  let g : SL(3,F) := ⟨!![0,1,0; 0,0,1; 1,1,0],by
    simp [Matrix.det_fin_three]⟩
  refine ⟨g,?_⟩
  intro v hv
  change g.val.mulVec v = v at hv
  have he : g.val.mulVec v = ![v 1,v 2,v 0+v 1] := by
    ext i
    fin_cases i <;> simp [g,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  rw [he] at hv
  have h10 : v 1 = v 0 := congrFun hv 0
  have h21 : v 2 = v 1 := congrFun hv 1
  have hsum : v 0+v 1 = v 2 := congrFun hv 2
  have hz : v 0 = 0 := by
    rw [h21] at hsum
    exact add_right_cancel (hsum.trans (zero_add _).symm)
  ext i
  fin_cases i <;> simp [hz,h10,h21]

private theorem natural_invariant_eq
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K W ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (A : Subgroup G) (hAW : A ≤ W) (hKA : K ≤ normalizer (A : Set G))
    (hA : A ≠ ⊥) : A = W := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKW,_,hn,a,ha⟩ := hm
  let := hn
  let b : W ≃* Multiplicative (Fin 3 → F) := QuotientGroup.quotientBot.symm.trans a
  obtain ⟨x,hx,hx1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  let xx : W := ⟨x,hAW hx⟩
  have hx0 : (b xx).toAdd ≠ 0 := by
    intro hh
    exact hx1 (congrArg Subtype.val (b.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh)))
  apply le_antisymm hAW
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ A.one_mem
  let yy : W := ⟨y,hy⟩
  have hy0 : (b yy).toAdd ≠ 0 := by
    intro hh
    exact hy1 (congrArg Subtype.val (b.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh)))
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hx0 hy0
  obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
  let z : W := W.normalizerMonoidHom ⟨k,hKW k.property⟩ xx
  have hz : z = yy := by
    apply b.injective
    apply Multiplicative.toAdd.injective
    have hh := ha k xx z rfl
    change (b z).toAdd = specialLinearNatural 3 (linearThreeActor e k) (b xx).toAdd at hh
    rw [show linearThreeActor e k = g from hk] at hh
    exact hh.trans hg
  have hmz : (z : G) ∈ A := (mem_normalizer_iff.mp (hKA k.property) x).mp hx
  simpa only [hz] using hmz

variable [Finite G]
local notation "O" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn Q
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q

omit [Finite G] in
private theorem section_fixed_eq_bot {V : Type*} [AddCommGroup V] [Module F V]
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (ρ : Representation F SL(3,F) V)
    (hm : HasSectionModel K W ⊥ (linearThreeActor e) ρ) (k : K)
    (hfix : ∀ v, ρ (linearThreeActor e k) v = v → v = 0) :
    W ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,a,ha⟩ := hm
  let := hn
  apply bot_unique
  rintro x ⟨hx,hxk⟩
  let xx : W := ⟨x,hx⟩
  have hc : (xx : G) = k * (xx : G) * (k : G)⁻¹ := by
    rw [mem_centralizer_iff.mp hxk k (Set.mem_singleton _),mul_inv_cancel_right]
  have hz := hfix _ (ha k xx xx hc).symm
  have he : QuotientGroup.mk' (⊥ : Subgroup W) xx = 1 :=
    a.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)
  exact congrArg Subtype.val (mem_bot.mp ((QuotientGroup.eq_one_iff xx).mp he))

private theorem center_fixed_eq_bot_of_omega
    (hQ : IsPGroup 2 Q) (k : G)
    (ho : O ⊓ centralizer ({k} : Set G) = ⊥) :
    Z ⊓ centralizer ({k} : Set G) = ⊥ := by
  let A := Z ⊓ centralizer ({k} : Set G)
  have hAQ : A ≤ Q := inf_le_left.trans (map_subtype_le _)
  have hQA : Q ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    rintro q hq x hx
    obtain ⟨z,hz,he⟩ := hx.1
    have hcomm : q*x=x*q := he ▸ congrArg Q.subtype (mem_center_iff.mp hz ⟨q,hq⟩)
    simpa only [hcomm,mul_inv_cancel_right] using hx
  by_contra hn
  apply inf_omegaCenterIn_ne_bot_of_normalized_twoGroup A Q hAQ hQ hQA hn
  apply bot_unique
  exact (le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq ho

/-- A natural or doubled-natural whole central omega supplies an actual
component element fixing only the identity in the whole center. No quotient
scalar or trivial C_Q(K) hypothesis is required. -/
theorem exists_center_fixedFree
    (hQ : IsPGroup 2 Q)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K O ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    ∃ k : K, Z ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  obtain ⟨g,hg⟩ := exists_fixedFree_matrix (F := F)
  obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
  refine ⟨k,center_fixed_eq_bot_of_omega hQ k ?_⟩
  rcases hm with hm | hm
  · exact section_fixed_eq_bot e _ hm k (by rwa [show linearThreeActor e k = g from hk])
  · apply section_fixed_eq_bot e _ hm k
    intro v hv
    rw [show linearThreeActor e k = g from hk] at hv
    exact Prod.ext (hg v.1 (congrArg Prod.fst hv)) (hg v.2 (congrArg Prod.snd hv))

/-- The entire center is generated by its component commutators as soon as
its whole central omega is natural or doubled natural. This retains possible
higher exponent and works without nonidentity central scalars. -/
theorem center_moved_of_omega_models
    (hQ : IsPGroup 2 Q) (hKQ : K ≤ normalizer (Q : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3) ∨
      HasSectionModel K O ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    ⁅Z,K⁆ = Z ∧ Z ⊓ centralizer (K : Set G) = ⊥ := by
  obtain ⟨k,hk⟩ := exists_center_fixedFree hQ e hm
  have hKZ : K ≤ normalizer (Z : Set G) := hKQ.trans
    (normalizer_le_normalizer_characteristic_image Q (center Q))
  let a : MulAut Z := (Z).normalizerMonoidHom ⟨k,hKZ k.property⟩
  have hfree : MonoidHom.FixedPointFree a := by
    intro z hz
    apply Subtype.ext
    apply hk.le
    refine ⟨z.property,mem_centralizer_iff.mpr ?_⟩
    rintro y (rfl : y = (k : G))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hz)
  refine ⟨le_antisymm (le_normalizer_iff_commutator_le_left.mp hKZ) ?_,?_⟩
  · intro z hz
    obtain ⟨x,hx⟩ := hfree.commutatorMap_surjective (⟨z,hz⟩ : Z)
    have he : (x : G) / ((k : G)*(x : G)*(k : G)⁻¹) = z := congrArg Subtype.val hx
    rw [←he]
    simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc] using
      commutator_mem_commutator x.property k.property
  · apply bot_unique
    exact (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr k.property))).trans_eq hk

/-- A natural whole central omega is contained in every nontrivial subgroup
of Q normalized by Q and K. Normality is relative to Q. -/
theorem omega_le_normal
    (hQ : IsPGroup 2 Q)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (A : Subgroup G) (hAQ : A ≤ Q) (hQA : Q ≤ normalizer (A : Set G))
    (hKA : K ≤ normalizer (A : Set G)) (hA : A ≠ ⊥) : O ≤ A := by
  have hi : A ⊓ O ≠ ⊥ :=
    inf_omegaCenterIn_ne_bot_of_normalized_twoGroup A Q hAQ hQ hQA hA
  have he := natural_invariant_eq e hm (A ⊓ O) inf_le_right
    ((le_inf hKA hm.2.1).trans inf_normalizer_le_normalizer_inf) hi
  exact he ▸ inf_le_left

/-- For a nonabelian core with natural central omega, the entire omega lies
in the literal derived and Frattini subgroups. -/
theorem omega_le_derived_and_frattini
    (hQ : IsPGroup 2 Q) (hKQ : K ≤ normalizer (Q : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K O ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (hna : ¬ IsMulCommutative Q) : O ≤ ⁅Q,Q⁆ ∧ O ≤ frattiniIn Q := by
  have hD : (⁅Q,Q⁆ : Subgroup G) ≠ ⊥ := by
    intro hd
    rw [←map_subtype_commutator] at hd
    exact hna ((_root_.commutator_eq_bot_iff Q).mp
      ((map_eq_bot_iff_of_injective _ Q.subtype_injective).mp hd))
  have hKD : K ≤ normalizer ((⁅Q,Q⁆ : Subgroup G) : Set G) := by
    rw [←map_subtype_commutator]
    exact hKQ.trans (normalizer_le_normalizer_characteristic_image Q (_root_.commutator Q))
  have hOD := omega_le_normal hQ e hm ⁅Q,Q⁆ Q.commutator_le_self
    (normalizer_commutator_ge_left Q Q) hKD hD
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  refine ⟨hOD,hOD.trans ?_⟩
  rw [←map_subtype_commutator]
  exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))

variable {R : Subgroup G} {n : ℕ} [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
include h hn

/-- In the natural-omega branch, the whole central omega is exactly the
original initial moved subgroup. This does not identify the whole center. -/
theorem omega_eq_initial
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R))
      ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R) =
      initialMoved K R := by
  apply Eq.symm
  apply natural_invariant_eq e hm (initialMoved K R)
    CentralSections.initialMoved_le_omegaCenter (normalizer_commutator_ge_right _ _)
  intro hu
  have hc : K ≤ centralizer (initialOmega K R : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hu)
  apply component_not_le_centralOmegaKernel h hn
  intro k hk v hv
  exact Subtype.ext (hc hk v (mem_map_of_mem _ hv))

/-- The original natural-omega branch puts its initial moved subgroup in
both intrinsic characteristic layers whenever Q is nonabelian. -/
theorem initial_le_derived_and_frattini
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R))
      ⊥ (linearThreeActor e) (specialLinearNatural 3))
    (hna : ¬ IsMulCommutative (msQ K R)) :
    initialMoved K R ≤ ⁅msQ K R,msQ K R⁆ ∧
      initialMoved K R ≤ frattiniIn (msQ K R) := by
  rw [←omega_eq_initial h hn e hm]
  exact omega_le_derived_and_frattini
    ((isPGroup_pCoreIn 2 (K ⊔ R)).to_le msQ_le_joinCore)
    ((le_sup_left : K ≤ K ⊔ R).trans (CentralSections.join_normalizes_core h hn)) e hm hna

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NaturalOmegaCore
