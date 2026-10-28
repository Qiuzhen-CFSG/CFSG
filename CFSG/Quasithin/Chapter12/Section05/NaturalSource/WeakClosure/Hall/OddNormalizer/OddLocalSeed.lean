module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.OddLocalAction
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.SeedCore
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.JankoCentralizer
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank

/-!
# The actual odd-local seed after the J₄ exclusion

The full original residual is a C-component of the simultaneous centralizer
of the marked involution and the whole odd actor. Its three-rank gives a
quasisimple two-core quotient before forming the literal simple-section map.
The J₄ fixed-section exclusion leaves binary G₂, triality and Ree F₄.
Their parabolic bounds kill the original seed's two-core in that map and
make its image a quasisimple Mathieu cover which normalizes no nontrivial
two-subgroup. These conclusions do not assert componenthood in the fixed
group of just one chosen actor element.

Hall.OddNormalizer applies this construction to the literal Hall
counterexample. Source: Aschbacher--Smith 4.4.3, printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter12.Section02 Chapter4 Chapter4.Section04 OddLocalMathieu
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The original odd-local data, with the image of the full residual made
quasisimple in the three remaining binary rows. The J₄ row is excluded. -/
@[expose] def ExteriorOddLocalSeedCase (s : SylowExteriorMarking D)
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
                ∀ U : Subgroup (SimpleSection Q), IsPGroup 2 U →
                  f.range ≤ normalizer (U : Set (SimpleSection Q)) → U = ⊥)

/-- The actual marked residual has a quasisimple two-core quotient before
its image is formed. The binary parabolic bounds then kill precisely its
original two-core in the same simple-section map. -/
theorem exterior_odd_local_seed_case (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (hpgt : 3 < p) {A : Subgroup G}
    {K : Subgroup (normalizer (A : Set G))} (d : ExteriorOddLocalActionData s p A K) :
    ExteriorOddLocalSeedCase s p A K := by
  classical
  obtain ⟨z,hzG,hz,P,hP,hPn,⟨eP⟩,hPm,Q,hn,hQ,hQq,hm,hTQ,hPQ,x,hx,ha,hfn,hfk,⟨e⟩,hfix⟩ := d
  let := hn
  let := hP.perfect
  let := hQ.perfect
  let := hQq
  let C := centralizer ({s.marking.z} : Set G)
  let E := C ⊓ centralizer (A : Set G)
  have hz2 : orderOf s.marking.z = 2 := by
    rw [←hzG,orderOf_coe,orderOf_coe]
    exact hz
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers s.marking.z,fun hb => s.marking.z_ne_one
      (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hz2).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers s.marking.z) = 2^1 by
      rw [Nat.card_zpowers,hz2]; rfl)
  have hE : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show E ≤ C from inf_le_left))).mp
      (hC.subgroup (E.subgroupOf C))
  have hPq : IsQuasisimple (P ⧸ pCore 2 P) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hE hP
      (mathieu_radical_three_rank eP)
  let := hPq
  let a := simpleAction Q (⟨x,hx⟩ : C)
  let f := (projection Q).comp (seedInclusion inf_le_left hPQ)
  let g : f.range →* Sporadic.Mathieu.M22 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical f.range))
  have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfixed : HasMathieuFixedSection (SimpleSection Q) p := ⟨a,ha,
    (ChapterA.Section02.IsSectionOf.of_surjective g hg).ambient_injective
      (inclusion hfix) (inclusion_injective hfix)⟩
  refine ⟨z,hzG,hz,P,hP,hPn,⟨eP⟩,hPm,hPq,Q,hn,hQ,hQq,hm,hTQ,
    hPQ,x,hx,ha,hfn,hfk,⟨e⟩,hfix,?_⟩
  have hr : RemainingOddLocalRankTwoModel (SimpleSection Q) := by
    rcases hfixed.theoremC_rows hp hpgt hm with hr | hj
    · exact hr
    · obtain ⟨ej⟩ := hj
      exact (no_janko_mathieu_fixed_section hp hpgt (hfixed.of_mulEquiv ej)).elim
  obtain ⟨hk,hqs,he⟩ := rank_two_seed_quasisimple hr f hfn e
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact ⟨hr,hk,hqs,he,fun U hU hN =>
    rank_two_normalized_two_group_eq_bot hr f.range U e hU hN⟩
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
