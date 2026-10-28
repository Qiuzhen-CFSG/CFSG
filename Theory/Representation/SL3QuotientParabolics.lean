module
public import Theory.Representation.SL3NaturalFlagInvariant
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.GroupAction.SolvableSylowInvariance
public import Theory.GroupTheory.EquivariantParabolicLift

/-!
# Lifting parabolics from a compatible natural SL3 quotient

A solvable actor containing the inner Sylow image preserves that Sylow.
The compatible additive natural action then fixes both adjacent parabolics.
Their full preimages are proper, generate the original group, and contain
its intersection with the actor. The quotient kernel is unrestricted.

Source: the invariant-parabolic argument of Aschbacher–Smith 15.3.20,
printed pp.1127–1128, applied to the actual B.5 moved-section quotient.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Representation.SL3NaturalFlagInvariant
open Matrix.PSL3.LinearThree
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
private theorem solvable_SL3_sylow_normalizer (hF : 4 ≤ Nat.card F)
    (P : Sylow 2 SL(3,F)) (H : Subgroup SL(3,F))
    (hs : Group.IsSolvable H) (hPH : (P : Subgroup _) ≤ H) :
    H ≤ normalizer (P : Set SL(3,F)) := by
  let := Fintype.ofFinite F
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F 2
  rw [← Nat.card_eq_fintype_card] at hcard
  obtain ⟨g,hg,_⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate
    F n.pos hcard P
  let e := MulAut.conj g⁻¹
  have hP : (P : Subgroup SL(3,F)).map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotentSL F := by
    rw [← hg]
    rw [Subgroup.map_map]
    have he : e.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
      simp [mul_assoc]
    rw [he, Subgroup.map_id]
  let : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hU : Matrix.PSL3.LinearThree.unipotentSL F ≤ H.map e.toMonoidHom :=
    hP ▸ map_mono hPH
  have hN := (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_le_borelSL
    F hF (H.map e.toMonoidHom) hU).trans
      (Matrix.PSL3.LinearThree.borelSL_le_normalizer_unipotentSL F)
  rw [← hP, ← map_equiv_normalizer_eq (P : Subgroup SL(3,F)) e] at hN
  exact (map_le_map_iff_of_injective e.injective).mp hN


/-- A compatible natural action on any quotient of L supplies the two
invariant parabolics. The kernel is unrestricted. -/
theorem exists_lifted_parabolics
    (L A : Subgroup G) (q : L →* SL(3,F)) (hq : Function.Surjective q)
    (hn : A ≤ normalizer (L : Set G)) [Group.IsSolvable A]
    (α : A →* MulAut SL(3,F))
    (heq : ∀ a l, q (L.normalizerMonoidHom (inclusion hn a) l) = α a (q l))
    (himpl : ∀ a : A, ∃ b : (Fin 3 → F) ≃+ (Fin 3 → F),
      ∀ g v, b (g.val.mulVec v) = (α a g).val.mulVec (b v))
    (hF : 4 ≤ Nat.card F) (S : Sylow 2 L)
    (hSA : (S : Subgroup L).map L.subtype ≤ A) :
    ∃ P Q : Subgroup G, P < L ∧ Q < L ∧ P ⊔ Q = L ∧
      A ≤ normalizer (P : Set G) ∧ A ≤ normalizer (Q : Set G) ∧ A ⊓ L ≤ P ⊓ Q := by
  let U : Sylow 2 SL(3,F) := S.mapSurjective hq
  have hinner (l : L) (hl : (l : G) ∈ A) : α ⟨l,hl⟩ = MulAut.conj (q l) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨k,rfl⟩ := hq x
    rw [← heq]
    change q (l * k * l⁻¹) = q l * q k * (q l)⁻¹
    simp only [map_mul, map_inv]
  let : Group.IsSolvable α.range := Group.isSolvable_of_surjective α.rangeRestrict_surjective
  have hUA : (U : Subgroup SL(3,F)).map MulAut.conj ≤ α.range := by
    rintro _ ⟨u, hu, rfl⟩
    change u ∈ (S : Subgroup L).map q at hu
    obtain ⟨l,hl,rfl⟩ := hu
    exact ⟨⟨l,hSA (mem_map_of_mem L.subtype hl)⟩,hinner l (hSA (mem_map_of_mem L.subtype hl))⟩
  have hU (a : A) : (U : Subgroup SL(3,F)).map (α a).toMonoidHom = U :=
    MulAut.sylow_map_eq_of_solvable_overgroups U (solvable_SL3_sylow_normalizer hF U)
      α.range hUA (α a) ⟨a,rfl⟩
  obtain ⟨P,Q,hP,hQ,hgen,hbase,hfix⟩ := exists_invariant_parabolic_pair U
  let P' := EquivariantLift.lift L q P
  let Q' := EquivariantLift.lift L q Q
  refine ⟨P',Q',EquivariantLift.lift_lt L q hq hP.ne_top,
    EquivariantLift.lift_lt L q hq hQ.ne_top, ?_, ?_, ?_, ?_⟩
  · rw [← EquivariantLift.lift_sup L q hq, hgen, EquivariantLift.lift_top]
  · exact EquivariantLift.normalizes_lift L q hn α heq
      (fun a => (hfix (α a) (hU a) (himpl a)).1)
  · exact EquivariantLift.normalizes_lift L q hn α heq
      (fun a => (hfix (α a) (hU a) (himpl a)).2)
  · have hb : ((A ⊓ L).subgroupOf L).map q ≤ P ⊓ Q := by
      rintro _ ⟨l,hl,rfl⟩
      apply hbase
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [← hinner l hl.1]
      exact hU ⟨l,hl.1⟩
    exact le_inf (EquivariantLift.le_lift L q inf_le_right (hb.trans inf_le_left))
      (EquivariantLift.le_lift L q inf_le_right (hb.trans inf_le_right))
theorem exists_invariant_repeated_parabolic_pair
    [Algebra (ZMod 2) F] {r : ℕ} (hr : 0 < r) (U : Sylow 2 SL(3,F)) :
    ∃ P Q : Subgroup SL(3, F), IsCoatom P ∧ IsCoatom Q ∧
      P ⊔ Q = ⊤ ∧ normalizer (U : Set SL(3, F)) ≤ P ⊓ Q ∧
      ∀ a : MulAut SL(3, F),
        (U : Subgroup SL(3, F)).map a.toMonoidHom = U →
        (∃ b : (Fin r → Fin 3 → F) ≃ₗ[ZMod 2] (Fin r → Fin 3 → F),
          ∀ g v, b (fun i => g.val.mulVec (v i)) = fun i => (a g).val.mulVec (b v i)) →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q := by
  let _ := Fintype.ofFinite F
  obtain ⟨n, _, hF⟩ := FiniteField.card F 2
  rw [← Nat.card_eq_fintype_card] at hF
  obtain ⟨c, hcU, hcB⟩ :=
    Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate F n.pos hF U
  let f : MulAut SL(3, F) := MulAut.conj c
  let P := (pointParabolicSL F).map f.toMonoidHom
  let Q := (lineParabolicSL F).map f.toMonoidHom
  refine ⟨P, Q,
    (OrderIso.isCoatom_iff f.mapSubgroup _).mpr (pointParabolicSL_isCoatom F),
    (OrderIso.isCoatom_iff f.mapSubgroup _).mpr (lineParabolicSL_isCoatom F), ?_, ?_, ?_⟩
  · change (pointParabolicSL F).map f.toMonoidHom ⊔
      (lineParabolicSL F).map f.toMonoidHom = ⊤
    rw [← Subgroup.map_sup, parabolicsSL_sup_eq_top, map_top_of_surjective _ f.surjective]
  · rw [← hcB]
    exact le_inf (map_mono inf_le_left) (map_mono inf_le_right)
  · intro a ha
    rintro ⟨b, hb⟩
    let α : MulAut SL(3, F) := f.trans (a.trans f.symm)
    have hm (R : Subgroup SL(3, F)) :
        (R.map α.toMonoidHom).map f.toMonoidHom =
          (R.map f.toMonoidHom).map a.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext g
      simp [α]
    have hα : (unipotentSL F).map α.toMonoidHom = unipotentSL F := by
      apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      rw [hm, hcU, ha]
    have hbf : ∀ g v, b (fun i => (f g).val.mulVec (v i)) =
        fun i => (f (α g)).val.mulVec (b v i) := by
      intro g v
      simpa [α] using hb (f g) v
    obtain ⟨hp, hq⟩ := SL3RepeatedNaturalFlagTypes.flags_of_intertwiner α hα f hr b hbf
    constructor
    · change ((pointParabolicSL F).map f.toMonoidHom).map a.toMonoidHom = _
      rw [← hm, hp]
    · change ((lineParabolicSL F).map f.toMonoidHom).map a.toMonoidHom = _
      rw [← hm, hq]



theorem exists_lifted_repeated_parabolics
    (L A : Subgroup G) (q : L →* SL(3,F)) (hq : Function.Surjective q)
    (hn : A ≤ normalizer (L : Set G)) [Group.IsSolvable A]
    (α : A →* MulAut SL(3,F))
    (heq : ∀ a l, q (L.normalizerMonoidHom (inclusion hn a) l) = α a (q l))
    [Algebra (ZMod 2) F] {r : ℕ} (hr : 0 < r)
    (himpl : ∀ a : A, ∃ b : (Fin r → Fin 3 → F) ≃ₗ[ZMod 2] (Fin r → Fin 3 → F),
      ∀ g v, b (fun i => g.val.mulVec (v i)) = fun i => (α a g).val.mulVec (b v i))
    (hF : 4 ≤ Nat.card F) (S : Sylow 2 L)
    (hSA : (S : Subgroup L).map L.subtype ≤ A) :
    ∃ P Q : Subgroup G, P < L ∧ Q < L ∧ P ⊔ Q = L ∧
      A ≤ normalizer (P : Set G) ∧ A ≤ normalizer (Q : Set G) ∧ A ⊓ L ≤ P ⊓ Q := by
  let U : Sylow 2 SL(3,F) := S.mapSurjective hq
  have hinner (l : L) (hl : (l : G) ∈ A) : α ⟨l,hl⟩ = MulAut.conj (q l) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨k,rfl⟩ := hq x
    rw [← heq]
    change q (l * k * l⁻¹) = q l * q k * (q l)⁻¹
    simp only [map_mul, map_inv]
  let : Group.IsSolvable α.range := Group.isSolvable_of_surjective α.rangeRestrict_surjective
  have hUA : (U : Subgroup SL(3,F)).map MulAut.conj ≤ α.range := by
    rintro _ ⟨u, hu, rfl⟩
    change u ∈ (S : Subgroup L).map q at hu
    obtain ⟨l,hl,rfl⟩ := hu
    exact ⟨⟨l,hSA (mem_map_of_mem L.subtype hl)⟩,hinner l (hSA (mem_map_of_mem L.subtype hl))⟩
  have hU (a : A) : (U : Subgroup SL(3,F)).map (α a).toMonoidHom = U :=
    MulAut.sylow_map_eq_of_solvable_overgroups U (solvable_SL3_sylow_normalizer hF U)
      α.range hUA (α a) ⟨a,rfl⟩
  obtain ⟨P,Q,hP,hQ,hgen,hbase,hfix⟩ := exists_invariant_repeated_parabolic_pair hr U
  let P' := EquivariantLift.lift L q P
  let Q' := EquivariantLift.lift L q Q
  refine ⟨P',Q',EquivariantLift.lift_lt L q hq hP.ne_top,
    EquivariantLift.lift_lt L q hq hQ.ne_top, ?_, ?_, ?_, ?_⟩
  · rw [← EquivariantLift.lift_sup L q hq, hgen, EquivariantLift.lift_top]
  · exact EquivariantLift.normalizes_lift L q hn α heq
      (fun a => (hfix (α a) (hU a) (himpl a)).1)
  · exact EquivariantLift.normalizes_lift L q hn α heq
      (fun a => (hfix (α a) (hU a) (himpl a)).2)
  · have hb : ((A ⊓ L).subgroupOf L).map q ≤ P ⊓ Q := by
      rintro _ ⟨l,hl,rfl⟩
      apply hbase
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [← hinner l hl.1]
      exact hU ⟨l,hl.1⟩
    exact le_inf (EquivariantLift.le_lift L q inf_le_right (hb.trans inf_le_left))
      (EquivariantLift.le_lift L q inf_le_right (hb.trans inf_le_right))
end Representation.SL3NaturalFlagInvariant
