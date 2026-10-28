module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.GeometryTransfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors.Geometry.Transfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.Position

/-!
# The two prime-five geometries and their local E-member consumer

A solvable Sylow overgroup joined with the weak-closure normalizer may generate
the ambient group. Alternatively an original family actor may have an outer
four-group image in the actual S₅ radical quotient of the involution-centralizer
supplement. In the second case, positioned S₅ generation lifts to the centralizer;
the proved split monomial mixing then generates the ambient group.

These alternatives are concrete group geometry, not E-membership assumptions.
Their existence remains to be proved. The two conjugacy classes of eight-actors
in the prime-five diagnostic require different alternatives; the solved
single-family normalizer escape does not imply this stronger geometry.
Families containing a four-actor are separately reduced using its proved
centralizer E-member, retaining that genuine member of the original family.

Source: Aschbacher--Smith E.1.8, E.1.10, E.1.13 and E.1.14(7), pp.210--214.
The bounded GAP exploration in `Scratch/EightActorContinuation` is diagnostic
only and is not used in the proofs below.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
variable (F : Type*) [Field F] [Finite F]

/-- The finite geometry still needed at five. The quotient, actor image and
weak closure are literal; the actor belongs to the original family. -/
@[expose] def FiveGeometryAt (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) (z : graphExtension F) : Prop :=
  (∃ H : Subgroup (graphExtension F), (T : Subgroup _) ≤ H ∧ Group.IsSolvable H ∧
    H ⊔ normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) = ⊤) ∨
  (let K := PSUThreeGeneration.centralizerResidualOvergroup T z
   let q := QuotientGroup.mk' (solvableRadical K)
   ∃ B ∈ Ω, B ≤ (T : Subgroup _) ∧
     ∃ e : (K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5),
       Nat.card ((B.subgroupOf K).map q) = 4 ∧
       ¬ (((B.subgroupOf K).map q).map e.toMonoidHom) ≤ alternatingGroup (Fin 5))

/-- The remaining prime-five producer need only consider families whose
nonidentity actors in the Sylow all have order eight. -/
@[expose] def FiveEightGeometry : Prop :=
  ∀ (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F))),
    IsElementaryFamily Ω → LargeActors F T Ω → ¬ HasInnerActor F T Ω →
    (∀ B ∈ Ω, B ≤ (T : Subgroup _) → B ≠ ⊥ → Nat.card B = 8) →
    ∀ A ∈ Ω, A ≤ (T : Subgroup _) → Nat.card A = 8 →
    Nat.card (A ⊓ innerPart F : Subgroup _) = 4 →
    ∀ z : graphExtension F, orderOf z = 2 → z ∈ innerPart F → z ∈ A →
    (T : Subgroup _) ≤ centralizer ({z} : Set _) → FiveGeometryAt F T Ω z

private def obstruction {T : Sylow 2 (graphExtension F)}
    {Ω : Set (Subgroup (graphExtension F))} (hΩ : IsElementaryFamily Ω)
    (hlarge : LargeActors F T Ω) {M : Subgroup (graphExtension F)}
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (hnot : ¬ FamilyEscapes F T Ω M) : PSUThreeGeneration.LargeFamilyObstruction T where
  family := Ω
  elementary := hΩ
  overgroup := M
  proper := hM
  sylow_le := hTM
  normalizer_le := hN
  large := hlarge
  nontrivial_member := exists_nontrivial_actor F T Ω M hM hN
  members_le := by
    intro B hB hBT K hK
    by_contra hKM
    exact hnot ⟨B, hB, hBT, K, hK, hKM⟩

variable [IsSimpleGroup PSL(3,F)]

/-- Either concrete geometry supplies actual escaping E-members. The S₅
premise is precisely the positioned outer-four generation theorem, whose
independent source owner must supply it. -/
theorem familyEscapes_of_five_geometry (hF : Nat.card F = 5)
    (hfive : ∀ (S : Sylow 2 (Equiv.Perm (Fin 5))) (B : Subgroup (Equiv.Perm (Fin 5))),
      IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ (S : Subgroup _) →
      ¬ B ≤ alternatingGroup (Fin 5) → eSubgroup 1 (S : Subgroup _) B ⊔ (S : Subgroup _) = ⊤)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (M : Subgroup (graphExtension F)) (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (hgeometry : FiveGeometryAt F T Ω z) : FamilyEscapes F T Ω M := by
  classical
  by_contra hnot
  let d := obstruction F hΩ hlarge hTM hM hN hnot
  rcases hgeometry with ⟨H, hTH, hs, hjoin⟩ | ⟨B, hB, hBT, e, hcard, hout⟩
  · let _ := hs
    apply hM
    exact top_unique (hjoin ▸ sup_le
      (PSUThreeGeneration.solvable_sylow_overgroup_le d H hTH) hN)
  · let K := PSUThreeGeneration.centralizerResidualOvergroup T z
    let q := QuotientGroup.mk' (solvableRadical K)
    let a := (B.subgroupOf K).map q
    let S := (T.subtype (show (T : Subgroup _) ≤ K from le_sup_right)).mapSurjective
      (f := q) (QuotientGroup.mk'_surjective _)
    let _ := hΩ.1 B hB
    let _ : IsElementaryAbelian 2 (B.subgroupOf K) :=
      IsElementaryAbelian.subgroupOf (hBT.trans le_sup_right)
    let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.map q
    have haS : a ≤ (S : Subgroup _) := map_mono (comap_mono hBT)
    have hc : Nat.card (a.map e.toMonoidHom) = 4 := by
      rw [card_map_of_injective e.injective]
      exact hcard
    have hg := hfive (S.mapSurjective (f := e.toMonoidHom) e.surjective)
      (a.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom) hc (map_mono haS) hout
    have hgen : eSubgroup 1 (S : Subgroup _) a ⊔ (S : Subgroup _) = ⊤ := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_sup, map_eSubgroup_equiv, map_top_of_surjective _ e.surjective]
      exact hg
    have hCM : centralizer ({z} : Set (graphExtension F)) ≤ M :=
      PSUThreeGeneration.OuterFamilies.EightActors.centralizer_le_of_quotient_actor_generation
        d hB hBT hTz hgen
    obtain ⟨H, hTH, hs, hm⟩ :=
      InnerGenerationGeometry.solvableMixing_of_card_mod_four_eq_one F (by omega) T z hz hzL hTz
    let _ := hs
    exact hM (InnerGenerationGeometry.eq_top_of_mixing F z M hCM
      (hm.mono F (PSUThreeGeneration.solvable_sylow_overgroup_le d H hTH)))

/-- At five, any genuine four-actor already forces escape, independently
of the remaining eight-actor finite geometry. -/
theorem familyEscapes_of_four_actor_at_five (hF : Nat.card F = 5)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F))
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 4) : FamilyEscapes F T Ω M := by
  have hne : A ≠ ⊥ := by
    intro h
    have := (eq_bot_iff_card A).mp h
    omega
  have hout : ¬ A ≤ innerPart F := fun h => houter ⟨A, hA, hAT, hne, h⟩
  have hfour : Nat.card (A ⊓ innerPart F : Subgroup _) = 2 := by
    have := outer_intersection_card F A hout
    omega
  obtain ⟨B, hB, hBT, hc, hi, z, hz, hzL, hzB, hTz⟩ :=
    exists_positioned_four_actor F (by decide : Odd 5) hF T hΩ hA hcard hfour
  exact familyEscapes_of_positioned_four_actor_of_generation F (by decide : Nat.Prime 5)
    (by decide) (by decide) hF
    (fourActorCentralizerGeneration_of_solvable_mixing F
      (InnerGenerationGeometry.solvableMixing_of_card_mod_four_eq_one F (by omega)))
    T Ω hΩ hlarge houter M hTM hM hN B hB hBT hc hi z hz hzL hzB hTz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
