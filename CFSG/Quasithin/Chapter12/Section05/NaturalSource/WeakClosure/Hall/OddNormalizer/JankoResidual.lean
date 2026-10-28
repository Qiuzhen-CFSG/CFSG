module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.ComponentLocals
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.Comparison

/-!
# The marked involution residual in the exterior J₄ branch

The full component carries its original quotient action with odd kernel.
The exterior marking's specified involution z lifts to that same component;
its centralizer residual has simple radical quotient M₂₂. The literal
residual inclusion first places it in C_G(z) intersect C_G(A), then in a
unique normal C-component of C_G(z). Both T and A normalize this component.
No covering center is discarded and no arbitrary fixed involution replaces z.

The original odd actor's T-closure also has a nontrivial two-core and full
normalizer contained in M, using the general proved odd-closure argument.
OddNormalizer applies these constructions to the actual Hall counterexample.
The odd-local identification and component generation on printed p.623,
and the separate pushing-up argument on p.612, remain source obligations.
Source: Aschbacher--Smith, 4.4.3, printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
open Chapter7.NormalizedSource.MathieuGeneration
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The full component and its literal residual at the marked exterior point.
Normality is relative to the displayed centralizer, and the M₂₂ quotient
removes precisely the solvable radical of the residual. -/
@[expose] def ExteriorJankoResidualData (s : SylowExteriorMarking D)
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G))) : Prop :=
  ∃ a : JankoNormalizerAction K,
    Function.Injective (a.projection.comp (V.subgroupOf (normalizer (A : Set G))).subtype) ∧
    (A.subgroupOf (normalizer (A : Set G))).map a.projection = ⊥ ∧
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      (solvableResidual (centralizer ({z} : Set K))).IsCComponent ∧
      Nonempty ((solvableResidual (centralizer ({z} : Set K)) ⧸
        solvableRadical (solvableResidual (centralizer ({z} : Set K)))) ≃* Sporadic.Mathieu.M22) ∧
      ∃ P : Subgroup (centralizer ({s.marking.z} : Set G) ⊓ centralizer (A : Set G) : Subgroup G),
        P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) ∧
        P.map (centralizer ({s.marking.z} : Set G) ⊓ centralizer (A : Set G)).subtype =
          ((solvableResidual (centralizer ({z} : Set K))).map
            (centralizer ({z} : Set K)).subtype).map
              ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
        ∃ Q : Subgroup (centralizer ({s.marking.z} : Set G)),
          Q.IsCComponent ∧ P.map (inclusion inf_le_left) ≤ Q ∧ Q.Normal ∧
          IsQuasisimple (Q ⧸ pCore 2 Q) ∧
          (∀ Q' : Subgroup (centralizer ({s.marking.z} : Set G)),
            Q'.IsCComponent → P.map (inclusion inf_le_left) ≤ Q' → Q'.Normal →
            IsQuasisimple (Q' ⧸ pCore 2 Q') → Q' = Q) ∧
          (T : Subgroup G) ≤ normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G) ∧
          A ≤ normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G)

/-- Construct the actual marked involution, its M₂₂ residual and containing
ambient component from the original normal J₄ cover. -/
theorem exterior_janko_fixed_residual (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (ho : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G))) (hK : IsComponent (normalizer (A : Set G)) K)
    (hn : K.Normal) (hV : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hc : centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)))
    (e : (K ⧸ center K) ≃* Janko4.Model) : ExteriorJankoResidualData s A K := by
  let N := normalizer (A : Set G)
  let := hn
  let := hK.2
  let a := jankoNormalizerAction K e hc
  have hA : (A.subgroupOf N).map a.projection = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [a.kernel]
    apply le_sSup
    refine ⟨inferInstance,?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv]
    exact ho.coprime_two_left
  have hzN : s.marking.z ∈ N :=
    (centralizer_le_normalizer (A : Set G)) ((le_centralizer_iff.mp hAV) s.marking.z_mem)
  have hzK : (⟨s.marking.z,hzN⟩ : N) ∈ K :=
    (mem_map_iff_mem N.subtype_injective).mp (hV s.marking.z_mem)
  let z : K := ⟨⟨s.marking.z,hzN⟩,hzK⟩
  have hz : orderOf z = 2 := by
    rw [← orderOf_coe z,← orderOf_coe (z : N)]
    let := D.elementary
    exact orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian s.marking.z s.marking.z_mem,s.marking.z_ne_one⟩
  obtain ⟨hres,hq⟩ := a.involution_residual z hz
  obtain ⟨P,hP,hPn,⟨qP⟩,hPm⟩ := janko_actor_residual_placement a hc hA z hz
  have hzG : orderOf s.marking.z = 2 := by
    change orderOf (((z : N) : G)) = 2
    rw [orderOf_coe,orderOf_coe]
    exact hz
  obtain ⟨Q,hQ,huniq⟩ := mathieu_residual_ambient_placement h.simpleQTKE hzG inf_le_left P hP qP
  let := hQ.2.2.1
  have hCQ : centralizer ({s.marking.z} : Set G) ≤
      normalizer (Q.map (centralizer ({s.marking.z} : Set G)).subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Q.le_normalizer_map (centralizer ({s.marking.z} : Set G)).subtype
  refine ⟨a,a.injective_on_twoSubgroup _ D.elementary.isPGroup.comap_subtype,hA,
    z,rfl,hz,hres,hq,P,hP,hPn,⟨qP⟩,hPm,Q,hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2,?_,
    s.sylow_centralizes_z.trans hCQ,?_⟩
  · intro Q' hQ' hPQ' hn' hqs'
    exact huniq Q' ⟨hQ',hPQ',hn',hqs'⟩
  · apply le_trans _ hCQ
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hAV hx) _ s.marking.z_mem).symm

/-- The literal closure of the odd actor under T has its full normalizer in M.
Residual uniqueness is not an input to this argument. -/
theorem exterior_oddActor_closure_control (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAM : A ≤ s.marking.M)
    (ho : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G)) :
    let X := conjugateSpanBy A (T : Subgroup G)
    IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
      normalizer (X : Set G) ≤ s.marking.M :=
  D.sourceOrbit_oddActorClosure_control h.toHypothesis1221 A hne
    ((s.marking.centralizing_actor_section hAM hAV).trans inf_le_right) ho

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
