module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalMaps

/-!
# Constructing the common cubic for the nonabelian comparison

The original point-parabolic image contains an odd permutation, forcing
the whole natural image to be S₆. The identical centralizer kernels give
the actual barred group identification. Pull back the specified duad cubic
and take a Sylow three-subgroup: its image is the whole cubic. Mapping it
back into G constructs the actor, its surjective marking and its location
in the common local group. The H-side bound is uniform in this actor.

Source: Aschbacher--Smith, 13.8.33, printed p.967.
CaseOne.SteinbergComparison applies these constructions; the original
parabolic markings and remaining 13.8.33 assembly stay with
qt-d-138-a6-endgame-source.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension
open A6Endgame.ActionAnalysis33.ChiefModels
open TransvectionQuotients.FourLocalFactors
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The actual duad parabolic contains an odd permutation, so the original
natural action, already containing A₆, is onto S₆. -/
theorem original_natural_surjective_of_parabolic
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) = H1) :
    Function.Surjective (Section07.NaturalAction.permutation (localNaturalSetup d)) := by
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  apply MonoidHom.range_eq_top.mp
  have hd : π.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using
      index_dvd_of_le (Section07.NaturalAction.alternating_le_range (localNaturalSetup d))
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact index_eq_one.mp hi
  have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
  have hm : swap45 ∈ ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map π) :=
    hpar.symm ▸ (by decide : swap45 ∈ H1)
  have hr : swap45 ∈ π.range := map_le_range _ _ hm
  rw [he] at hr
  exact ((by decide : swap45 ∉ alternatingGroup (Fin 6)) hr).elim

/-- Construct the symmetric bar-image identification from the local parabolic;
no full symmetric quotient is an additional assumption. -/
theorem exists_original_bar_equiv_of_parabolic
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) = H1) :
    Nonempty ((barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6)) := by
  let := barKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  have hk : (Section07.NaturalAction.permutation (localNaturalSetup d)).ker =
      barKernel (L ⊔ (T : Subgroup G)) V := by
    ext x
    exact Section07.permutation_eq_one_iff (localNaturalSetup d) x
  exact ⟨(barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (original_natural_surjective_of_parabolic d hpar)))⟩

/-- Lift the literal cubic actor through the actual point parabolic.
The H-side bound applies to every three-subgroup, so it needs no extra
identification with the chosen generator in H/O₂(H). -/
theorem exists_original_cubic_actor
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) = H1) :
    ∃ (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H), IsPGroup 3 A ∧
      ∃ f : A →* cubicActor, Function.Surjective f ∧
        ∀ a : A, Section07.NaturalAction.permutation (localNaturalSetup d)
          (inclusion (hAP.trans inf_le_left) a) = (cubicActorEquiv (f a) : Equiv.Perm (Fin 6)) := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := L ⊔ (T : Subgroup G)
  let P := X ⊓ H
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  let k : P →* Equiv.Perm (Fin 6) := π.comp (inclusion inf_le_left)
  let D := duadCubicActor.comap k
  let r : D →* duadCubicActor := (k.comp D.subtype).codRestrict duadCubicActor (fun x => x.property)
  have hr : Function.Surjective r := by
    intro b
    have hb : (b : Equiv.Perm (Fin 6)) ∈ H1 := (duadCubicActor_le_K.trans K_le_H1) b.property
    obtain ⟨x,hx,hxb⟩ := hpar.symm ▸ hb
    let p : P := ⟨x,hx⟩
    have hp : p ∈ D := by
      change π x ∈ duadCubicActor
      rw [hxb]
      exact b.property
    exact ⟨⟨p,hp⟩,Subtype.ext hxb⟩
  let S : Sylow 3 D := Sylow.nonempty.some
  have hS : (S : Subgroup D).map r = ⊤ :=
    ((S.mapSurjective hr).is_maximal' (duadCubicActor_isPGroup.to_subgroup ⊤) le_top).symm
  let i : D →* G := P.subtype.comp D.subtype
  let A := (S : Subgroup D).map i
  have hAP : A ≤ P := by
    rintro _ ⟨x,_,rfl⟩
    exact x.val.property
  let t : A →* duadCubicActor := (k.comp (inclusion hAP)).codRestrict duadCubicActor (by
    rintro ⟨_,x,hx,rfl⟩
    exact x.property)
  have ht : Function.Surjective t := by
    intro b
    obtain ⟨x,hx,hxb⟩ := show b ∈ (S : Subgroup D).map r from hS.symm ▸ mem_top b
    refine ⟨⟨i x,mem_map_of_mem i hx⟩,?_⟩
    exact hxb
  let f := cubicActorEquiv.symm.toMonoidHom.comp t
  refine ⟨A,hAP,S.isPGroup'.map i,f,cubicActorEquiv.symm.surjective.comp ht,?_⟩
  intro a
  change (t a : Equiv.Perm (Fin 6)) = (cubicActorEquiv (cubicActorEquiv.symm (t a)) : Equiv.Perm (Fin 6))
  rw [cubicActorEquiv.apply_symm_apply]

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
