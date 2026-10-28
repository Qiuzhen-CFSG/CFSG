module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureClassifiedImage

/-!
# The original outer central-closure configuration is impossible

The free original U-image forces transitivity and makes the original Sylow
image regular dihedral. The finite one-local sieve supplies a second actual
S4 in every proper overgroup of the original JT image. The two-core excludes
equality with JT. The checked pair theorem then gives the order-168 image.

The original point is transported through the equality Z(W)=<z> and the
retained square isometry, keeping its literal conjugation action. Its JT
fixed line lies in a proper invariant native three-space, contradicting the
original H-orbit span. No second local or recognition conclusion is a premise.

Source: Aschbacher--Smith, following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.AlgebraicGroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
open Theory.SpecificGroups.SymmetricEight
open Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
open ClassicalOrthogonal BinaryD3Comparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The genuine outer branch contradicts the original locally fixed spanning point. -/
theorem original_tripleSix_central_closure_outer_natural_dual_false
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) : False := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let L := J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let Z := zpowers (z:G)
  obtain ⟨hHW, hex, e, r, hrW, hrcore, hcore, hformula, _, _, _, ⟨eL⟩,
      c, hc, hmax, j, hj, _, _, _, x, hx, _, hfix, hspan⟩ := original_tripleSix_central_closure_classified_image
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let := hex
  let f := MulAut.conj c
  let X := r.range.map f.toMonoidHom
  let A := ((L.subgroupOf H).map r).map f.toMonoidHom
  have hAX : A ≤ X := map_mono (map_le_range _ _)
  have hTA : twoGroup ≤ A := by
    rw [← hc]
    exact map_mono (map_mono (subgroupOf_mono H (show (T : Subgroup G) ≤ L from le_sup_right)))
  let eA : A ≃* Equiv.Perm (Fin 4) :=
    (((L.subgroupOf H).map r).equivMapOfInjective f.toMonoidHom f.injective).symm.trans eL
  have hcoreX : pCore 2 X = ⊥ := by
    rw [← pCore_map_iso 2 (r.range.equivMapOfInjective f.toMonoidHom f.injective), hcore,
      Subgroup.map_bot]
  have hobstruction := (core_free_local_image hmax hcoreX A hAX hTA eA).2.2
  let b := (symmetricEquiv c).val
  let r' := f.toMonoidHom.comp r
  have intertwine (g : H) (v : VectorD 3 (ZMod 2)) :
      (symmetricEquiv (r' g)).val (b v) = b ((symmetricEquiv (r g)).val v) := by
    simp [r', f, b, MulAut.conj_apply, map_mul, map_inv]
  have hfixed : ∀ g ∈ A, (symmetricEquiv g).val (b x) = b x := by
    rintro g ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact (intertwine u x).trans (congrArg b (hfix u hu))
  have hspan' : Submodule.span (ZMod 2)
      (Set.range (fun g : X => (symmetricEquiv g.val).val (b x))) = ⊤ := by
    let P := Submodule.span (ZMod 2)
      (Set.range (fun g : X => (symmetricEquiv g.val).val (b x)))
    have hle : Submodule.span (ZMod 2) (Set.range (fun g : r.range => (symmetricEquiv g.val).val x)) ≤
        P.comap b.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      obtain ⟨u, hu⟩ := g.property
      have hm : r' u ∈ X := mem_map_of_mem f.toMonoidHom (show r u ∈ r.range from ⟨u,rfl⟩)
      have hv : (symmetricEquiv (r' u)).val (b x) ∈ P :=
        Submodule.subset_span ⟨⟨r' u, hm⟩, rfl⟩
      change b ((symmetricEquiv g.val).val x) ∈ P
      rw [← hu, ← intertwine]
      exact hv
    have hP : P.comap b.toLinearMap = ⊤ := top_unique (hspan ▸ hle)
    apply top_unique
    intro v _
    have hv : b.symm v ∈ P.comap b.toLinearMap := hP ▸ Submodule.mem_top
    change b (b.symm v) ∈ P at hv
    simpa only [b.apply_symm_apply] using hv
  exact hobstruction (b x) hfixed hspan'


/-- The original closure automizer is contained in the original K-automizer;
the genuine outer alternative is excluded by its actual square module. -/
theorem original_tripleSix_central_closure_automizer_containment
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K := by
  by_contra houter
  exact original_tripleSix_central_closure_outer_natural_dual_false
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter

end CFSG.Quasithin.Chapter12.Section07
