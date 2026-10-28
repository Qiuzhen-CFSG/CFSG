module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.CartanTransport

/-!
# All perfect source roots in their original rank-one quotients

The actual Cartan complement in each original factor satisfies the uniform
rank-one fixed-pair theorem. Transport to the literal marked endpoint panel
and the finite commutator argument put its canonical simple root in that
factor image, including the special and projective unitary cases. If both
factors are perfect, both roots lie in the same two-residual.

Lift the root through the injective original factor map. The original
local two-core is normalized by the entire endpoint and lies in the Borel,
so its image lies in the conjugate Borel as well. The canonical root meets
that conjugate Borel trivially. Projection of the lifted root to the
original Lᵢ/O₂(Lᵢ) is therefore injective and lands in its actual quotient
Sylow. This constructs a literal local model map, without identifying
coordinates on different roots or asserting mixed commutator relations.

Source: Aschbacher–Smith F.1.1–3, pp.259–260; DGS, Groups and Graphs,
Part II, pp.80–81 and Theorem D, p.224. The same marking can come from
the universal apartment quotient; no descent to the original completion
is needed. Ordered-root generation and the seven Lie comparisons remain
separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

theorem simpleRoot_le_factor (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) :
    simpleRoot Q split i ≤ (factorMap Q e i).range := by
  obtain ⟨hD, hodd, hdis, hsup⟩ := localCartan_complement Q e h split i
  exact simpleRoot_le_factor_of_localCartan Q e h split i
    (h.borel_two_fixed_cosets i hp _ hD hodd hdis hsup)

include e in
theorem simpleRoot_le_twoResidual (h : HypothesisF11 L S)
    (hp : ∀ i, Group.IsPerfect (L i)) (split : SplitData Q.tits) (i : Fin 2) :
    simpleRoot Q split i ≤ pResidual 2 (X ⧸ Q.D) := by
  rw [(perfect_residual Q e h hp split).1]
  exact (simpleRoot_le_factor Q e h split i (hp i)).trans (by
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right)

/-- Lift the actual simple root through its original marked factor. -/
def simpleRootLift (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) : simpleRoot Q split i →* L i :=
  (MonoidHom.ofInjective (factorMap_injective Q e i)).symm.toMonoidHom.comp
    (inclusion (simpleRoot_le_factor Q e h split i hp))

@[simp] theorem factorMap_simpleRootLift (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) (r : simpleRoot Q split i) :
    factorMap Q e i (simpleRootLift Q e h split i hp r) = (r : X ⧸ Q.D) := by
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (factorMap_injective Q e i)).apply_symm_apply
      (inclusion (simpleRoot_le_factor Q e h split i hp) r))

theorem simpleRootLift_injective (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) :
    Function.Injective (simpleRootLift Q e h split i hp) := by
  intro r s hrs
  apply Subtype.ext
  simpa only [factorMap_simpleRootLift] using congrArg (factorMap Q e i) hrs

theorem simpleRootLift_mem_sylow (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) (r : simpleRoot Q split i) :
    simpleRootLift Q e h split i hp r ∈ (S ⊓ L i).subgroupOf (L i) := by
  rw [← factor_unipotent_comap Q e h split i]
  change factorMap Q e i (simpleRootLift Q e h split i hp r) ∈ split.U
  rw [factorMap_simpleRootLift]
  exact (simpleRoot_le Q split i) r.property


/-- The image of the original local two-core is normalized by the whole endpoint. -/
theorem factorCore_normalizes (h : HypothesisF11 L S) (i : Fin 2) :
    Q.tits.standardParabolic {Q.simple i} ≤
      normalizer ((pCore 2 (L i)).map (factorMap Q e i) : Set (X ⧸ Q.D)) := by
  let f := factorMap Q e i
  let a := MonoidHom.ofInjective (factorMap_injective Q e i)
  have he : (pCore 2 (L i)).map f =
      (pCore 2 f.range).map f.range.subtype := by
    rw [← pCore_map_iso 2 a, map_map]
    rfl
  rw [he]
  exact (factor_parabolic_normalizes Q e h i).trans
    (normalizer_le_normalizer_characteristic_image f.range (pCore 2 f.range))

/-- The original two-core image lies in the actual Borel. -/
theorem factorCore_le_borel (h : HypothesisF11 L S) (i : Fin 2) :
    (pCore 2 (L i)).map (factorMap Q e i) ≤ Q.tits.B := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ Q.tits.B.comap (factorMap Q e i)
  rw [factor_borel_comap Q e h i]
  obtain ⟨T, hT⟩ := h.sylow i
  exact twoCore_le_borel_of_sylow (L i) S T hT (mem_map_of_mem (L i).subtype hx)

/-- The root has trivial intersection with the original local two-core image. -/
theorem simpleRoot_disjoint_factorCore (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) :
    Disjoint (simpleRoot Q split i) ((pCore 2 (L i)).map (factorMap Q e i)) := by
  apply (simpleRoot_disjoint_conjugateBorel Q split i).mono_right
  intro x hx
  let n := representative (Q.simple i)
  have hnP : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  exact factorCore_le_borel Q e h i
    ((mem_normalizer_iff.mp (factorCore_normalizes Q e h i hnP) x).mp hx)

/-- The actual quotient of the original local factor, applied to the lifted root. -/
def simpleRootProjection (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) :
    simpleRoot Q split i →* (L i) ⧸ pCore 2 (L i) :=
  (QuotientGroup.mk' (pCore 2 (L i))).comp (simpleRootLift Q e h split i hp)

theorem simpleRootProjection_injective (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (hp : Group.IsPerfect (L i)) :
    Function.Injective (simpleRootProjection Q e h split i hp) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro r hr
  have hrCore : simpleRootLift Q e h split i hp r ∈ pCore 2 (L i) :=
    (QuotientGroup.eq_one_iff _).mp hr
  have hrMap : (r : X ⧸ Q.D) ∈ (pCore 2 (L i)).map (factorMap Q e i) := by
    rw [← factorMap_simpleRootLift Q e h split i hp r]
    exact mem_map_of_mem _ hrCore
  exact Subtype.ext ((disjoint_def.mp (simpleRoot_disjoint_factorCore Q e h split i))
    r.property hrMap)

@[simp] theorem simpleRootProjection_apply (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) (hp : Group.IsPerfect (L i))
    (r : simpleRoot Q split i) :
    simpleRootProjection Q e h split i hp r =
      QuotientGroup.mk' (pCore 2 (L i)) (simpleRootLift Q e h split i hp r) := by rfl

/-- Restriction to the original quotient Sylow, with its original witness retained. -/
def simpleRootSylowProjection (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) [Finite (L i)] (hp : Group.IsPerfect (L i)) (T : Sylow 2 (L i))
    (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i) :
    simpleRoot Q split i →* quotientSylow T :=
  (simpleRootProjection Q e h split i hp).codRestrict _ (by
  intro r
  apply mem_map_of_mem (QuotientGroup.mk' (pCore 2 (L i)))
  have hr := simpleRootLift_mem_sylow Q e h split i hp r
  rw [← hT] at hr
  exact (comap_map_eq_self_of_injective (L i).subtype_injective _).le hr)

theorem simpleRootSylowProjection_injective (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) [Finite (L i)] (hp : Group.IsPerfect (L i))
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i) :
    Function.Injective (simpleRootSylowProjection Q e h split i hp T hT) := by
  intro r t hrt
  exact simpleRootProjection_injective Q e h split i hp (congrArg Subtype.val hrt)

@[simp] theorem simpleRootSylowProjection_coe (h : HypothesisF11 L S)
    (split : SplitData Q.tits) (i : Fin 2) [Finite (L i)] (hp : Group.IsPerfect (L i))
    (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
    (r : simpleRoot Q split i) :
    (simpleRootSylowProjection Q e h split i hp T hT r : (L i) ⧸ pCore 2 (L i)) =
      simpleRootProjection Q e h split i hp r := by rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal


namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Uniform containment in the original factor image under the same quotient map. -/
theorem quotient_simpleRoot_le_original_factor (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
    (hp : Group.IsPerfect (L i)) :
    simpleRoot Q split i ≤ ((L i).subgroupOf (generated L S)).map Q.q := by
  rw [← original_factorMap_range Q i]
  exact MarkedLocal.simpleRoot_le_factor Q (originalMarkedIso Q) h split i hp

/-- The root lift is a preimage under the literal original quotient q. -/
theorem quotient_simpleRootLift_apply (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
    (hp : Group.IsPerfect (L i)) (r : simpleRoot Q split i) :
    Q.q ⟨MarkedLocal.simpleRootLift Q (originalMarkedIso Q) h split i hp r,
      local_le_generated i (MarkedLocal.simpleRootLift Q (originalMarkedIso Q) h split i hp r).property⟩ =
        (r : (generated L S) ⧸ Q.D) := by
  rw [← original_factorMap_apply]
  exact MarkedLocal.factorMap_simpleRootLift Q (originalMarkedIso Q) h split i hp r

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
