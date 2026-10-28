module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.PerfectNormalizer
public import Theory.GroupAction.PerfectPair

/-!
# The canonical radical forbids a normalizer-invariant pair

The image of the actual N_L(P)-action is perfect, by Frattini factorization
and perfectness of L. A permuted pair in its Frattini quotient must therefore
be fixed pointwise. The original radical action is irreducible, so its first
member is either zero or the entire quotient. This excludes the pair produced
by the component geometry in original 13.1.12(3).

All maps below use the chosen Sylow subgroup of the literal XiP p L.
Source: Aschbacher--Smith, 13.1.12(3), printed p.875.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The genuine N_L(P)-action has no two-point orbit consisting of proper
nonzero Frattini traces. No perfectness of N_L(P) itself is asserted. -/
theorem Context.no_normalizer_pair (h : Context T L p) (P : Sylow p (XiP p L))
    (A B : Subgroup G)
    (hpair : ∀ g ∈ L ⊓ normalizer ((P : Subgroup (XiP p L)).map (XiP p L).subtype : Set G),
      A.conjBy g = A ∨ A.conjBy g = B)
    (hproper : ¬ ((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≤ A)
    (htrace : ¬ ((P : Subgroup (XiP p L)).map (XiP p L).subtype) ⊓ A ≤
      (frattini ((P : Subgroup (XiP p L)).map (XiP p L).subtype)).map
        ((P : Subgroup (XiP p L)).map (XiP p L).subtype).subtype) : False := by
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  let N := L ⊓ normalizer (P₀ : Set G)
  let q := QuotientGroup.mk' (frattini P₀)
  let A₀ := (A.subgroupOf P₀).map q
  let B₀ := (B.subgroupOf P₀).map q
  let ρ := frattiniConjugationAction N P₀ inf_le_right
  let : Group.IsPerfect L := mem_L_isPerfect h.maximal.1.1
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  have hQ := uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2
  have hq := (XiP_oddQuotient_of_A36 h36 h.maximal.1.1 hQ h.nonquasisimple h.odd h.divides).2
  let : Group.IsPerfect ρ.range := normalizer_frattini_image_perfect
    (XiP_invariant p L.le_normalizer) ((pCoreIn_le 2 _).trans (XiP_le p L)) h.odd hq.isPGroup P
  let : MulDistribMulAction ρ.range (P₀ ⧸ frattini P₀) :=
    MulDistribMulAction.compHom _ ρ.range.subtype
  have hp : ∀ a : ρ.range, a • A₀ = A₀ ∨ a • A₀ = B₀ := by
    rintro ⟨a,n,rfl⟩
    change A₀.map (ρ n).toMonoidHom = A₀ ∨ A₀.map (ρ n).toMonoidHom = B₀
    have he := frattini_trace_conjugate P₀ N A inf_le_right n
    rcases hpair n n.property with hn | hn
    · exact Or.inl (he.trans (congrArg (fun C : Subgroup G => (C.subgroupOf P₀).map q) hn))
    · exact Or.inr (he.trans (congrArg (fun C : Subgroup G => (C.subgroupOf P₀).map q) hn))
  have hfix (n : N) : A₀.map (ρ n).toMonoidHom = A₀ :=
    MulAction.fixed_of_isPerfect_pair A₀ B₀ hp ⟨ρ n,⟨n,rfl⟩⟩
  have hi := XiP_normalizer_irreducible_of_A36 h36 h.maximal.1.1 hQ
    h.nonquasisimple h.odd h.divides P
  rcases hi A₀ (fun n a ha => hfix n ▸ mem_map_of_mem (ρ n).toMonoidHom ha) with hz | ht
  · apply htrace
    have hk : A.subgroupOf P₀ ≤ frattini P₀ := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
    intro a ha
    exact ⟨⟨a,ha.1⟩,hk ha.2,rfl⟩
  · apply hproper
    apply subgroupOf_eq_top.mp
    apply frattini_nongenerating
    have he := congrArg (comap q) ht
    simpa only [A₀,comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using he

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
