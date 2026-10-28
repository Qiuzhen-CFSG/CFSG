module

public import Theory.AtlasPort.LinearGroups.G2.ProperSylowOvergroups
public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Solvable Sylow control and cubic automorphisms of G₂(4)

Proper Sylow-overgroup placement and the two solvable parabolic refinements
show that a solvable subgroup containing a full Sylow two-subgroup normalizes
that Sylow. Over the four-element field, the genuine field component of a
three-subgroup of automorphisms is trivial. Pulling back a solvable join along
faithful inner conjugation therefore shows that these cubic automorphisms
preserve its marked Sylow.

Source: the Cartan-normalization step in Aschbacher--Smith 9.3.1,
printed pp.732--733, using the intrinsic G₂ parabolic and automorphism facts.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Atlas.G2
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every solvable overgroup of a full Sylow two-subgroup normalizes it. -/
theorem solvable_sylow_overgroup_normalizes (hq : 2 < Nat.card F)
    (S : Sylow 2 (Model F)) (H : Subgroup (Model F))
    (hS : (S : Subgroup (Model F)) ≤ H) (hH : Group.IsSolvable H) :
    H ≤ normalizer (S : Set (Model F)) := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hq
  let : IsSimpleGroup (Model F) := Atlas.G2.isSimple hq
  have hp : H ≠ ⊤ := by
    intro he
    let : Group.IsSolvable (⊤ : Subgroup (Model F)) := he ▸ hH
    let : Group.IsSolvable (Model F) := Group.isSolvable_of_surjective
      (f := (⊤ : Subgroup (Model F)).subtype) topEquiv.surjective
    exact Group.IsPerfect.not_isSolvable (Model F) inferInstance
  obtain ⟨g,hg⟩ := ProperSylowOvergroups.conjugate_le_parabolic S H hS hp
  let e := MulAut.conj g
  let : Group.IsSolvable H := hH
  have hHe : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := (e.subgroupMap H).toMonoidHom) (e.subgroupMap H).surjective
  have hn := SolvableParabolic.normalizes hq
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (H.map e.toMonoidHom)
    (map_mono hS) hHe hg
  change H.map e.toMonoidHom ≤
    normalizer ((S : Subgroup (Model F)).map e.toMonoidHom : Set (Model F)) at hn
  rw [←map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

/-- A three-subgroup has trivial field component over the four-element field. -/
theorem four_cubic_automorphisms_inner (hF : Nat.card F = 4)
    (A : Subgroup (MulAut (Model F))) (hA : IsPGroup 3 A) :
    A ≤ MulAut.innerSubgroup (Model F) := by
  have hq : 2 < Nat.card F := by omega
  let f := LieAutomorphismExtensions.fieldComponent (F := F) hq
  have hp : IsPGroup 2 (F ≃+* F) := isPGroup_iff_pow_pow_eq_one.mpr fun σ =>
    ⟨1,FiniteField.ringAut_sq_of_card_prime_pow (p := 2) (n := 2)
      (by decide) (by omega) (by simpa using hF) σ⟩
  have hb : A.map f = ⊥ := disjoint_self.mp
    ((hA.map f).disjoint_of_coprime (hp.to_subgroup _) (by decide))
  intro a ha
  have he : f a = 1 := mem_bot.mp (hb ▸ mem_map_of_mem f ha)
  obtain ⟨g,hg⟩ := (LieAutomorphismExtensions.fieldComponent_eq_one_iff hq a).mp he
  exact ⟨g,hg.symm⟩

/-- A cubic automorphism group in a solvable join with the marked inner Sylow preserves it. -/
theorem four_cubic_solvable_join_preserves_sylow (hF : Nat.card F = 4)
    (S : Sylow 2 (Model F)) (A : Subgroup (MulAut (Model F))) (hA : IsPGroup 3 A)
    (hsol : Group.IsSolvable (A ⊔ (S : Subgroup (Model F)).map MulAut.conj : Subgroup (MulAut (Model F)))) :
    ∀ a ∈ A, (S : Subgroup (Model F)).map a.toMonoidHom = S := by
  have hq : 2 < Nat.card F := by omega
  let H : Subgroup (MulAut (Model F)) := A ⊔ (S : Subgroup (Model F)).map MulAut.conj
  let C := H.comap MulAut.conj
  have hi : Function.Injective (MulAut.conj : Model F →* MulAut (Model F)) :=
    conj_injective_of_center_eq_bot (LieAutomorphismExtensions.model_center_eq_bot hq)
  let : Group.IsSolvable H := hsol
  have hC : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := (MulAut.conj : Model F →* MulAut (Model F)).subgroupComap H)
    (fun x y h => Subtype.ext (hi (congrArg Subtype.val h)))
  have hSC : (S : Subgroup (Model F)) ≤ C := fun s hs =>
    (le_sup_right : (S : Subgroup (Model F)).map MulAut.conj ≤ H) (mem_map_of_mem MulAut.conj hs)
  have hn := solvable_sylow_overgroup_normalizes hq S C hSC hC
  intro a ha
  obtain ⟨g,hg⟩ := four_cubic_automorphisms_inner hF A hA ha
  have hgc : g ∈ C := by
    change MulAut.conj g ∈ H
    rw [hg]
    exact (le_sup_left : A ≤ H) ha
  rw [←hg]
  exact mem_normalizer_iff_map_conj_eq.mp (hn hgc)

end Atlas.G2
