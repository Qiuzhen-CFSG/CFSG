module
public import Theory.Representation.NormalElementaryQuotient.CommonChief

/-!
# Common chief sections under relative normality

The two residual actors need only be normal in the preimage of the selected
acting subgroup. Restricting to that preimage gives commutator idempotence;
the double moved subgroup is invariant there. A maximal proper invariant
quotient has both factor actions nontrivial, on the original module and
with the original centralizer-quotient representation.

This extends the ambient-normal construction without changing its API.
The relative boundary is needed for a selected odd-prime line, which is
normalized by the smaller actor group but need not be normal in the full
hat group. Source: Aschbacher--Smith 13.1.9, printed pp.870--871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
  (D : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (D : Set G)) (E : Subgroup H)

@[expose] def relativeInvariantSubrepresentation (C : Subgroup G)
    (hCN : E.comap q ≤ normalizer (C : Set G)) :
    Subrepresentation ((representation D q hq hker).comp E.subtype) where
  toSubmodule := subspace D (C.subgroupOf D)
  apply_mem_toSubmodule g v hv := by
    obtain ⟨x,hx⟩ := hq g.val
    change ((representation D q hq hker g.val v).toMul : G) ∈ C
    rw [←hx,representation_apply]
    have hn := hCN (show x ∈ E.comap q from (by change q x ∈ E; rw [hx]; exact g.property))
    exact (mem_normalizer_iff.mp hn _).mp hv

private theorem relative_section_kernel_forces_eq (C A : Subgroup G) (hCN : E.comap q ≤ normalizer (C : Set G))
    (hCD : C ≤ D) (hC : ⁅C,A⁆ = C) (hAE : A.map q ≤ E)
    (N : Subrepresentation ((representation D q hq hker).comp E.subtype))
    (hN : N ≤ relativeInvariantSubrepresentation D q hq hker E C hCN)
    (hk : (A.map q).subgroupOf E ≤ (sectionRepresentation ((representation D q hq hker).comp E.subtype)
      N (relativeInvariantSubrepresentation D q hq hker E C hCN)).ker) :
    N = relativeInvariantSubrepresentation D q hq hker E C hCN := by
  let S : Subgroup G := N.toSubmodule.toAddSubgroup.toSubgroup'.map D.subtype
  have hc : ⁅C,A⁆ ≤ S := by
    apply commutator_le.mpr
    intro c hc a ha
    let v : D := ⟨c,hCD hc⟩
    have he : ∀ s, sectionRepresentation ((representation D q hq hker).comp E.subtype) N
        (relativeInvariantSubrepresentation D q hq hker E C hCN) ⟨q a,hAE (mem_map_of_mem q ha)⟩ s = s :=
      fun s => DFunLike.congr_fun (hk (mem_map_of_mem q ha)) s
    have hv := (sectionRepresentation_trivial_iff _ _ _ _).mp he
      (Additive.ofMul v) hc
    change representation D q hq hker (q a) (Additive.ofMul v) - Additive.ofMul v ∈ N.toSubmodule at hv
    have hm : Additive.ofMul (⟨⁅c,a⁆,(commutator_le_left D ⊤)
        (commutator_mem_commutator v.property (mem_top a))⟩ : D) ∈ N.toSubmodule := by
      rw [vector_commutator D q hq hker v a]
      simpa only [neg_sub] using N.toSubmodule.neg_mem hv
    exact ⟨_,hm,rfl⟩
  rw [hC] at hc
  apply le_antisymm hN
  intro v hv
  obtain ⟨c,hc,he⟩ := hc hv
  have he' : c = v.toMul := Subtype.ext he
  change Additive.ofMul c ∈ N.toSubmodule at hc
  change v ∈ N.toSubmodule
  simpa only [he',ofMul_toMul] using hc

/-- Construct an irreducible invariant section on which both factor images act nontrivially. -/
theorem exists_relative_common_chief_section [Finite G]
    (C A B : Subgroup G) (hCN : E.comap q ≤ normalizer (C : Set G)) (hCD : C ≤ D) (hne : C ≠ ⊥)
    (hA : ⁅C,A⁆ = C) (hB : ⁅C,B⁆ = C)
    (hAE : A.map q ≤ E) (hBE : B.map q ≤ E) :
    ∃ N : Subrepresentation ((representation D q hq hker).comp E.subtype),
      N ≤ relativeInvariantSubrepresentation D q hq hker E C hCN ∧
      IsIrreducible (sectionRepresentation ((representation D q hq hker).comp E.subtype) N
        (relativeInvariantSubrepresentation D q hq hker E C hCN)) ∧
      ¬ (A.map q).subgroupOf E ≤ (sectionRepresentation ((representation D q hq hker).comp E.subtype) N
        (relativeInvariantSubrepresentation D q hq hker E C hCN)).ker ∧
      ¬ (B.map q).subgroupOf E ≤ (sectionRepresentation ((representation D q hq hker).comp E.subtype) N
        (relativeInvariantSubrepresentation D q hq hker E C hCN)).ker := by
  let ρ := (representation D q hq hker).comp E.subtype
  let W := relativeInvariantSubrepresentation D q hq hker E C hCN
  have hW : W.toSubmodule ≠ ⊥ := by
    intro he
    apply hne
    apply bot_unique
    intro c hc
    have hv : Additive.ofMul (⟨c,hCD hc⟩ : D) ∈ W.toSubmodule := hc
    rw [he,Submodule.mem_bot] at hv
    exact mem_bot.mpr (congrArg (fun v : Additive D => (v.toMul : G)) hv)
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let : IsCoatomic (Subrepresentation W.toRepresentation) :=
    SimpleHeadQuotient.subrepresentation_coatomic W.toRepresentation
  obtain ⟨P,hP⟩ := IsCoatomic.exists_coatom (Subrepresentation W.toRepresentation)
  let N : Subrepresentation ρ := {
    toSubmodule := P.toSubmodule.map W.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := by
      obtain ⟨u,hu,rfl⟩ := hv
      exact ⟨W.toRepresentation g u,P.apply_mem_toSubmodule g hu,rfl⟩ }
  have hNW : N ≤ W := Submodule.map_subtype_le _ _
  have hNP : sectionLower ρ N W = P := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_map_eq_of_injective W.toSubmodule.injective_subtype _
  have hNne : N ≠ W := by
    intro he
    apply hP.1
    rw [← hNP,he]
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_subtype_self W.toSubmodule
  refine ⟨N,hNW,?_,?_,?_⟩
  · change IsIrreducible (sectionLower ρ N W).quotientRepresentation
    rw [hNP]
    exact SimpleHeadQuotient.irreducible_quotient_of_isCoatom P hP
  · exact fun hk => hNne (relative_section_kernel_forces_eq D q hq hker E C A hCN hCD hA hAE N hNW hk)
  · exact fun hk => hNne (relative_section_kernel_forces_eq D q hq hker E C B hCN hCD hB hBE N hNW hk)
end Representation.NormalElementaryQuotient

namespace Representation.CommonChief
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- Relative normality suffices for the same two-perfect common-chief construction. -/
theorem exists_of_relative_double_movement
    (D : Subgroup G) [D.Normal] [IsElementaryAbelian 2 D]
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (D : Set G))
    (S K : Subgroup G) (A : Subgroup Q)
    (hSN : (actorGroup (S.map q) (K.map q) A).comap q ≤ normalizer (S : Set G))
    (hKN : (actorGroup (S.map q) (K.map q) A).comap q ≤ normalizer (K : Set G))
    (hpS : IsPPerfect 2 S) (hpK : IsPPerfect 2 K)
    (hc : ⁅S,K⁆ ≤ centralizer (D : Set G)) (hm : ⁅⁅D,S⁆,K⁆ ≠ ⊥) :
    Nonempty (Data (NormalElementaryQuotient.representation D q hq hker)
      (S.map q) (K.map q) A
      (NormalElementaryQuotient.subspace D ((⁅⁅D,S⁆,K⁆).subgroupOf D))) := by
  let E := actorGroup (S.map q) (K.map q) A
  let F := E.comap q
  let C := ⁅⁅D,S⁆,K⁆
  have hDF : D ≤ F := by
    intro d hd
    have hdker : d ∈ q.ker := by
      rw [hker]
      intro u hu
      exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : D) ⟨d,hd⟩)
    change q d ∈ E
    rw [show q d = 1 from hdker]
    exact E.one_mem
  have hSF : S ≤ F := fun s hs => (show S.map q ≤ E from le_sup_left) (mem_map_of_mem q hs)
  have hKF : K ≤ F := fun k hk => (show K.map q ≤ E from le_sup_left.trans le_sup_right) (mem_map_of_mem q hk)
  let D₀ := D.subgroupOf F
  let S₀ := S.subgroupOf F
  let K₀ := K.subgroupOf F
  let : D₀.Normal := inferInstance
  let : S₀.Normal := normal_subgroupOf_of_le_normalizer hSN
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hKN
  have hmapD : D₀.map F.subtype = D := map_subgroupOf_eq_of_le hDF
  have hmapS : S₀.map F.subtype = S := map_subgroupOf_eq_of_le hSF
  have hmapK : K₀.map F.subtype = K := map_subgroupOf_eq_of_le hKF
  have hS : IsPPerfect 2 S₀ := hpS.of_surjective
    (subgroupOfEquivOfLe hSF).symm.toMonoidHom (subgroupOfEquivOfLe hSF).symm.surjective
  have hK : IsPPerfect 2 K₀ := hpK.of_surjective
    (subgroupOfEquivOfLe hKF).symm.toMonoidHom (subgroupOfEquivOfLe hKF).symm.surjective
  have hc₀ : ⁅S₀,K₀⁆ ≤ centralizer (D₀ : Set F) := by
    intro x hx d hd
    have hx' := mem_map_of_mem F.subtype hx
    rw [map_commutator,hmapS,hmapK] at hx'
    exact Subtype.ext (hc hx' d hd)
  have hid₀ := double_commutator_idempotent D₀ S₀ K₀
    ((IsElementaryAbelian.isPGroup 2 D).of_injective
      (subgroupOfEquivOfLe hDF).toMonoidHom (subgroupOfEquivOfLe hDF).injective) hS hK hc₀
  have hCS : ⁅C,S⁆ = C := by
    have hh := congrArg (Subgroup.map F.subtype) hid₀.1
    simpa only [map_commutator,hmapD,hmapS,hmapK] using hh
  have hCK : ⁅C,K⁆ = C := by
    have hh := congrArg (Subgroup.map F.subtype) hid₀.2
    simpa only [map_commutator,hmapD,hmapS,hmapK] using hh
  have hCD : C ≤ D := (commutator_mono (commutator_le_left D S) le_rfl).trans (commutator_le_left D K)
  have hCN : F ≤ normalizer (C : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    dsimp only [C]
    rw [map_commutator,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (show x ∈ normalizer (D : Set G) from le_normalizer_of_normal hx),
      mem_normalizer_iff_map_conj_eq.mp (hSN hx),mem_normalizer_iff_map_conj_eq.mp (hKN hx)]
  obtain ⟨N,hNW,hI,hS,hK⟩ := NormalElementaryQuotient.exists_relative_common_chief_section D q
    hq hker E C S K hCN hCD hm hCS hCK le_sup_left (le_sup_left.trans le_sup_right)
  exact ⟨⟨N,_,hNW,le_rfl,hI,hS,hK⟩⟩
end Representation.CommonChief
