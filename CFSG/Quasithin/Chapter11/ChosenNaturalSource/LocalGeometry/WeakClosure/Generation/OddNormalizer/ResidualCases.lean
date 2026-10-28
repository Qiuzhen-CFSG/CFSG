module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PushingUpReduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ReeTits
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedExclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OrdinaryFinite

/-!
# The remaining sporadic pushing-up components

The perfect-action and full-cover order obstructions exclude the Ree, Tits,
constrained and five small sporadic rows. The actual ordinary component
therefore has central quotient M₂₄, J₂, J₄, He or Ru. This conclusion retains
the original covering residual, its inclusion-compatible full quotient,
relative normality and the conjugate of the same V inside W.

The source endpoint applies this reduction to the literal Hall kernel.
These five rows and the moved components of N(A) remain with this task;
this module does not assert the final odd-normalizer containment.
Source: Aschbacher--Smith C.3.1--5 and C.4.8, pp.149--154, and 4.4.6, p.620.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Only the five remaining actual sporadic central quotients. -/
def RemainingOrdinary (Q : Type*) [Group Q] : Prop :=
  ∃ n : ClassificationModels.SporadicName,
    (n = .m24 ∨ n = .j2 ∨ n = .j4 ∨ n = .he ∨ n = .ru) ∧
      Nonempty (Q ≃* n.Carrier)

include D S
theorem ordinary_remaining_models {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) : RemainingOrdinary (K ⧸ center K) := by
  rcases ordinary_natural_models D S h e K hK with ⟨m,hm,⟨em⟩⟩ | ⟨em⟩ | ⟨n,hn,⟨em⟩⟩
  · exact (no_ordinary_natural_ree D S h e K hK hm em).elim
  · exact (no_ordinary_natural_tits D S h e K hK em.some).elim
  · have hsmall := no_ordinary_natural_small_sporadic D S h e K hK n
    cases n with
    | m11 => exact (hsmall (by simp) em).elim
    | m12 => exact (hsmall (by simp) em).elim
    | m22 => exact (hsmall (by simp) em).elim
    | m23 => exact (hsmall (by simp) em).elim
    | hs => exact (hsmall (by simp) em).elim
    | j3 => exact (hn rfl).elim
    | m24 => exact ⟨.m24,by simp,⟨em⟩⟩
    | j2 => exact ⟨.j2,by simp,⟨em⟩⟩
    | j4 => exact ⟨.j4,by simp,⟨em⟩⟩
    | he => exact ⟨.he,by simp,⟨em⟩⟩
    | ru => exact ⟨.ru,by simp,⟨em⟩⟩

/-- The original pushing-up pair with an ordinary component in the remaining
five sporadic rows. All original covering and module data are retained. -/
def PushingUpRemainingCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G,
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let M := H ⊓ normalizer (L : Set G)
    let R := J.pCoreIn 2
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W ∧
    (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G) ∧
    (B.subgroupOf M).Normal ∧
    (∃ e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L),
      ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_left) b)) ∧
    ¬ ExceptionalQuotient (B ⧸ pCore 2 B) ∧ 64 ≤ Nat.card W ∧
    (∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ M.subgroupOf H ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      RemainingOrdinary (K ⧸ center K)

/-- The constrained branch is excluded; the surviving ordinary branch has
only the five specified sporadic quotients. -/
theorem pushingUp_remaining_case {A : Subgroup G} (hc : PushingUpReducedCase L V A) :
    PushingUpRemainingCase L V A := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,he,hno,hsize,hVW,
    K,hK,hq,hout,_,hnormal,hcases⟩ := hc
  obtain ⟨e,he⟩ := he
  rcases hcases with ⟨ho,hB,hW⟩ | ⟨hfK,_,_⟩
  · exact ⟨J,H,W,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,⟨e,he⟩,hno,hsize,hVW,
      K,ho,hnormal,hout,hB,hW,ordinary_remaining_models D S hC e K ho⟩
  · exact (no_constrained_natural D S hC hN e K hK hq hout hfK).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
