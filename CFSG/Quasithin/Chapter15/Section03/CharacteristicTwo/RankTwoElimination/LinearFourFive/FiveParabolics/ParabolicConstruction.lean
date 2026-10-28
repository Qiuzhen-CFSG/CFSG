module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.Lift
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi

/-!
# Constructing an outside maximal parabolic in the actual component

The image of Y₊(S∩L) in the marked five-dimensional quotient contains an
actual Sylow subgroup. If this image is solvable with three-part nine,
its two maximal flag overgroups generate the quotient. Their full preimages
therefore generate L, and at least one is outside M. The inner diagram
action makes S normalize both. The four actual Levi quotients are transported
through the original maps to the intrinsic two-core quotients of these
preimages.

Solvability, the three-part calculation and the inner action are the
remaining source-preparation obligations; this file does not assert them.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics
variable {G : Type*} [Group G] (d : LocalData G) {L : Subgroup G}

/-- The image of the actual solvable Sylow overgroup Y₊(S∩L). -/
noncomputable def baseImage (e : (L ⧸ pCore 2 L) ≃* Projective 5) :
    Subgroup (LinearGroup 5) :=
  ((d.Yplus ⊔ (d.S ⊓ L)).subgroupOf L).map (linearAction (by decide) e)

/-- The maximal parabolic of L at one specified cut of an actual basis. -/
noncomputable def parabolic (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (b : FiveBasis) (i : Fin 4) : Subgroup G := lift e (flagStabilizer b {i})

omit d in
theorem parabolic_isCoatom (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (b : FiveBasis) (i : Fin 4) : IsCoatom ((parabolic e b i).subgroupOf L) :=
  lift_isCoatom e (singleton_flag_isCoatom b i)

omit d in
/-- The constructed parabolic is normal in PS once S normalizes it.
This does not assert normality in the original ambient group. -/
theorem parabolic_normal_in_join (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (b : FiveBasis) (i : Fin 4) (S : Subgroup G)
    (hn : S ≤ normalizer (parabolic e b i : Set G)) :
    ((parabolic e b i).subgroupOf (parabolic e b i ⊔ S)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le (parabolic e b i).le_normalizer hn)

variable [Finite G]

omit d in
noncomputable def parabolicQuotientEquiv (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (b : FiveBasis) (i : Fin 4) :
    (parabolic e b i ⧸ pCore 2 (parabolic e b i)) ≃*
      LinearGroup (i.val + 1) × LinearGroup (4 - i.val) :=
  (liftQuotientEquiv e (flagStabilizer b {i})).trans (singletonQuotientEquiv b i)

omit d in
theorem parabolicQuotientEquiv_mk (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (b : FiveBasis) (i : Fin 4) (x : parabolic e b i) :
    parabolicQuotientEquiv e b i (QuotientGroup.mk' _ x) =
      singletonQuotientEquiv b i (QuotientGroup.mk' _ (liftMap e _ x)) := rfl

omit d in
theorem parabolic_quotient_models (e : (L ⧸ pCore 2 L) ≃* Projective 5)
    (b : FiveBasis) (i : Fin 4) :
    Nonempty ((parabolic e b i ⧸ pCore 2 (parabolic e b i)) ≃*
      (Equiv.Perm (Fin 3) × Projective 3)) ∨
    Nonempty ((parabolic e b i ⧸ pCore 2 (parabolic e b i)) ≃* Projective 4) := by
  rcases singleton_quotient_models b i with hp | hp
  · obtain ⟨f⟩ := hp
    exact Or.inl ⟨(liftQuotientEquiv e _).trans f⟩
  · obtain ⟨f⟩ := hp
    exact Or.inr ⟨(liftQuotientEquiv e _).trans f⟩

/-- Construct the two generating maximal parabolics over Y₊(S∩L), and
choose one outside M. Solvability, the three-part calculation and the
inner diagram action are inputs to be discharged by the source preparation. -/
theorem exists_outside_parabolic {I : Subgroup G}
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 5)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hYL : d.Yplus ≤ c.L)
    (hθ : c.L = theta I)
    (hsol : Group.IsSolvable (baseImage d e))
    (h3 : (Nat.card (baseImage d e)).factorization 3 = 2)
    (hi : IsInnerOnModel e d.S
      ((Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ))) :
    ∃ (b : FiveBasis) (i : Fin 4),
      d.Yplus ⊔ (d.S ⊓ c.L) ≤ parabolic e b i ∧
      ¬ parabolic e b i ≤ d.M ∧
      d.S ≤ normalizer (parabolic e b i : Set G) := by
  let q := linearAction (by decide) e
  obtain ⟨T, hT⟩ := sylow_intersection_of_eq_theta d hS hθ
  have hT' : (T : Subgroup c.L) = (d.S ⊓ c.L).subgroupOf c.L := by
    rw [← hT]
    exact (comap_map_eq_self_of_injective c.L.subtype_injective _).symm
  let U := T.mapSurjective (f := q) (linearAction_surjective (by decide) e)
  have hU : (U : Subgroup (LinearGroup 5)) =
      ((d.S ⊓ c.L).subgroupOf c.L).map q := by
    change (T : Subgroup c.L).map q = _
    rw [hT']
  have hUB : (U : Subgroup (LinearGroup 5)) ≤ baseImage d e := by
    rw [hU]
    exact map_mono (subgroupOf_mono c.L le_sup_right)
  obtain ⟨b, i, j, hij, hb, hiB, hjB, _, _, hgen⟩ :=
    solvable_overgroup_two_maximals U (baseImage d e) hUB hsol h3
  have hbaseL : d.Yplus ⊔ (d.S ⊓ c.L) ≤ c.L := sup_le hYL inf_le_right
  have hbi : d.Yplus ⊔ (d.S ⊓ c.L) ≤ parabolic e b i := le_lift hbaseL e _ hiB
  have hbj : d.Yplus ⊔ (d.S ⊓ c.L) ≤ parabolic e b j := le_lift hbaseL e _ hjB
  have hgenL : parabolic e b i ⊔ parabolic e b j = c.L := by
    rw [parabolic, parabolic, ← lift_sup, hgen, lift_top]
  have hnL : d.S ≤ normalizer (c.L : Set G) :=
    (Chapter1.isSylowIn_iff.mp hS).2.1.trans (normalizes_of_eq_theta hθ)
  have hnD : d.S ≤ normalizer ((d.S ⊓ c.L : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro s hs x hx
    exact ⟨(d.S.le_normalizer hs x).mp hx.1, (hnL hs x).mp hx.2⟩
  have hn (k : Fin 4) : d.S ≤ normalizer (parabolic e b k : Set G) :=
    normalizes_lift_flag e d.S (d.S ⊓ c.L) inf_le_right hnL hnD hi b
      (hU.symm.trans hb) {k}
  by_cases hiM : parabolic e b i ≤ d.M
  · refine ⟨b, j, hbj, ?_, hn j⟩
    intro hjM
    exact c.outside (hgenL.symm ▸ sup_le hiM hjM)
  · exact ⟨b, i, hbi, hiM, hn i⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics

end
