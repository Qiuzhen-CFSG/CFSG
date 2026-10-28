module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalSeed
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.CommonFixed

/-!
# The original residual as a component of the whole odd actor's fixed group

Restrict the original normal residual in C_G(z) intersect C_G(A) to Q,
then use coprime lifting through Q/O₂(Q) and normal-image descent through
its center. The already proved quasisimple image is consequently an ordinary
component of the fixed group of the whole A, with its M₂₂ center quotient
and original covering maps retained. No component assertion is made for the
fixed group of an arbitrarily selected element of A.

Hall.OddNormalizer applies this to the actual Hall counterexample. The three
binary fixed-component exclusions and final normalizer control remain open.
Source: Aschbacher--Smith 4.4.3, printed p.623, the assertion
K_Z* in C(C_{L_Z*}(B*)).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter12.Section02 Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The same full seed, literal quotient, and prime action, together with
componenthood in the fixed group of the entire odd actor. -/
@[expose] def ExteriorOddLocalComponentCase (s : SylowExteriorMarking D)
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
              (RemainingOddLocalRankTwoModel (SimpleSection Q) ∧
                pCore 2 P ≤ f.ker ∧ IsQuasisimple f.range ∧
                Nonempty ((f.range ⧸ center f.range) ≃* Sporadic.Mathieu.M22) ∧
                (∀ U : Subgroup (SimpleSection Q), IsPGroup 2 U →
                  f.range ≤ normalizer (U : Set (SimpleSection Q)) → U = ⊥) ∧
                ∃ hAC : A ≤ centralizer ({s.marking.z} : Set G),
                  IsComponentIn f.range (commonSimpleFixed Q A hAC))

/-- The source fixed-component placement follows from the normality of the
original residual and the quasisimplicity of its literal simple-section image. -/
theorem exterior_odd_local_component_case (s : SylowExteriorMarking D)
    {p : ℕ} (hp : p.Prime) (hpgt : 3 < p) {A : Subgroup G}
    (hA : IsElementaryAbelian p A) (hAV : A ≤ centralizer (V : Set G))
    {K : Subgroup (normalizer (A : Set G))} (d : ExteriorOddLocalSeedCase s p A K) :
    ExteriorOddLocalComponentCase s p A K := by
  obtain ⟨z,hzG,hz,P,hP,hPn,heP,hPm,hPq,Q,hn,hQ,hQq,hm,hTQ,
    hPQ,x,hx,ha,hfn,hfk,he,hfix,hr,hcore,hqs,hcenter,hU⟩ := d
  let := hn
  let := hPn
  have hAC : A ≤ centralizer ({s.marking.z} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((hAV ha) _ s.marking.z_mem).symm
  exact ⟨z,hzG,hz,P,hP,hPn,heP,hPm,hPq,Q,hn,hQ,hQq,hm,hTQ,
    hPQ,x,hx,ha,hfn,hfk,he,hfix,hr,hcore,hqs,hcenter,hU,hAC,
    seed_component_in_common_fixed hAC Q P hPQ hp (by omega) hA.isPGroup hqs⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
