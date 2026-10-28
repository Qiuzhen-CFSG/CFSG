module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalComponent
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.SelfDualModels
public import Theory.Mathieu.M22.ReeExclusion

/-!
# The remaining Ree F₄ comparison at the original exterior marking

The full Mathieu image cannot embed in either binary G₂ or triality: their
faithful self-dual eight-spaces contradict the ten-dimensional lower bound.
The original seed, both quotient kernels and the whole odd actor's common
fixed component are retained on the remaining actual Ree section.

The remaining Ree section is excluded by lifting the actual Mathieu hexad
local through the full residual-image quotient. Its normalizer has order
divisible by fifteen, contrary to the native Ree two-local order bound.
Hall.OddNormalizer applies this to the original counterexample and proves
normalizer containment. Source: Aschbacher--Smith 4.4.3, printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter12.Section02 Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The same original component data with its containing simple section
identified as an actual positive-parameter Ree F₄ model. -/
@[expose] def ExteriorOddLocalReeCase (s : SylowExteriorMarking D)
    (p : ℕ) (A : Subgroup G) (K : Subgroup (normalizer (A : Set G))) : Prop :=
  ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
    ∃ P : Subgroup (centralizer ({s.marking.z} : Set G) ⊓ centralizer (A : Set G) : Subgroup G),
      P.IsCComponent ∧ P.Normal ∧
      Nonempty ((P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) ∧
      P.map (centralizer ({s.marking.z} : Set G) ⊓ centralizer (A : Set G)).subtype =
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
      IsQuasisimple (P ⧸ pCore 2 P) ∧
      ∃ (Q : Subgroup (centralizer ({s.marking.z} : Set G))) (hn : Q.Normal),
        letI := hn
        Q.IsCComponent ∧ IsQuasisimple (Q ⧸ pCore 2 Q) ∧
        ChapterA.Section02.IsTheoremCModel (SimpleSection Q) ∧
        (T : Subgroup G) ≤ normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G) ∧
        ∃ hPQ : P.map (inclusion inf_le_left) ≤ Q,
          ∃ (x : A) (hx : (x : G) ∈ centralizer ({s.marking.z} : Set G)),
            let a := simpleAction Q (⟨x,hx⟩ : centralizer ({s.marking.z} : Set G))
            let f := (projection Q).comp (seedInclusion inf_le_left hPQ)
            orderOf a = p ∧ f.range ≠ ⊥ ∧ Group.IsSolvable f.ker ∧
              Nonempty ((f.range ⧸ solvableRadical f.range) ≃* Sporadic.Mathieu.M22) ∧
              f.range ≤ a.fixedSubgroup ∧
              ((∃ m, 1 ≤ m ∧ Nonempty (SimpleSection Q ≃* ReeF4.Model m)) ∧
                pCore 2 P ≤ f.ker ∧ IsQuasisimple f.range ∧
                Nonempty ((f.range ⧸ center f.range) ≃* Sporadic.Mathieu.M22) ∧
                (∀ U : Subgroup (SimpleSection Q), IsPGroup 2 U →
                  f.range ≤ normalizer (U : Set (SimpleSection Q)) → U = ⊥) ∧
                ∃ hAC : A ≤ centralizer ({s.marking.z} : Set G),
                  IsComponentIn f.range (commonSimpleFixed Q A hAC))


/-- The degree-eight isometry models cannot contain the original full Mathieu
cover, so the same source seed and common-fixed component lie in a Ree section. -/
theorem exterior_odd_local_ree_case (s : SylowExteriorMarking D)
    {p : ℕ} {A : Subgroup G} {K : Subgroup (normalizer (A : Set G))}
    (d : ExteriorOddLocalComponentCase s p A K) : ExteriorOddLocalReeCase s p A K := by
  obtain ⟨z,hzG,hz,P,hP,hPn,heP,hPm,hPq,Q,hn,hQ,hQq,hm,hTQ,
    hPQ,x,hx,ha,hfn,hfk,he,hfix,hr,hcore,hqs,hcenter,hU,hAC,hcomp⟩ := d
  let := hn
  let := hqs
  have hree := rank_two_mathieu_cover_is_ree hr _ hcenter.some
  exact ⟨z,hzG,hz,P,hP,hPn,heP,hPm,hPq,Q,hn,hQ,hQq,hm,hTQ,
    hPQ,x,hx,ha,hfn,hfk,he,hfix,hree,hcore,hqs,hcenter,hU,hAC,hcomp⟩

/-- The actual residual image cannot occur in the remaining Ree section.
Frattini lifting retains its full kernel and uses the original projection;
no stronger fixed-group component placement is asserted. -/
theorem not_exterior_odd_local_ree_case (s : SylowExteriorMarking D)
    {p : ℕ} {A : Subgroup G} {K : Subgroup (normalizer (A : Set G))}
    (d : ExteriorOddLocalReeCase s p A K) : False := by
  obtain ⟨z,hzG,hz,P,hP,hPn,heP,hPm,hPq,Q,hn,hQ,hQq,hm,hTQ,
    hPQ,x,hx,ha,hfn,hfk,he,hfix,hree,hrest⟩ := d
  let := hn
  let f := (projection Q).comp (seedInclusion inf_le_left hPQ)
  obtain ⟨m,hm,⟨e⟩⟩ := hree
  let b := he.some.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical f.range))
  exact Sporadic.Mathieu.M22LocalSections.no_embedding_ree b
    (he.some.surjective.comp (QuotientGroup.mk'_surjective _)) hm
    (e.toMonoidHom.comp f.range.subtype) (e.injective.comp f.range.subtype_injective)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
