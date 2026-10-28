module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Containment
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ElementaryImage
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.ElementaryAbelian.Quotient

/-!
# The characteristic long-root plane in a triality short-root centralizer

The center of the central unipotent radical consists exactly of its two
highest long-root coordinates. Nondegeneracy of the cubic trace pairing
kills the three short-root coordinates of every central element. The two
remaining additive fixed-field coordinates form a nontrivial elementary
abelian subgroup of order q², normalized by the full central parabolic and
centralizing the marked highest short root.

Source: the natural long-root plane in Aschbacher–Smith F.4.27(4)(ii)
and F.4.42, printed pp.288 and 295 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Triality.Standard.ShortRootCentralizer
open Parabolics RadicalCoordinates RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators
open Parabolics.CentralRootSquare Parabolics.CentralRootSquare.ElementaryImage

theorem coord_zero (P : Parameters) (hp : P.prime = 2) :
    coordinates P hp (0,0) = 1 := by
  apply Subtype.ext
  rw [coordinates_val,rootElement_factorization]
  simp [extendOrbit]

/-- The two highest long root groups with their additive parameters. -/
@[expose] def planeHom (P : Parameters) (hp : P.prime = 2) :
    Multiplicative (Fin 2 → fixedField P) →* radical P .central where
  toFun a := coordinates P hp (0,a.toAdd)
  map_one' := coord_zero P hp
  map_mul' a b := by
    rw [←coordinates_multiply]
    apply congrArg (coordinates P hp)
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [multiply,higherCoefficient,-fieldFrobenius_apply]
    · funext i
      fin_cases i <;> simp [multiply,higherCoefficient,-fieldFrobenius_apply]

theorem planeHom_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (planeHom P hp) := by
  intro a b h
  exact Multiplicative.toAdd.injective (congrArg Prod.snd ((coordinates P hp).injective h))

theorem planeHom_val (P : Parameters) (hp : P.prime = 2)
    (a : Multiplicative (Fin 2 → fixedField P)) :
    (planeHom P hp a).val = long P hp 1 (a.toAdd 0) * long P hp 2 (a.toAdd 1) := by
  change (coordinates P hp (0,a.toAdd)).val = _
  rw [coordinates_val,rootElement_factorization]
  simp [extendOrbit]

theorem planeHom_range (P : Parameters) (hp : P.prime = 2) :
    (planeHom P hp).range = center (radical P .central) := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    apply mem_center_iff.mpr
    intro r
    obtain ⟨v,rfl⟩ := (coordinates P hp).surjective r
    change coordinates P hp v * coordinates P hp (0,a.toAdd) =
      coordinates P hp (0,a.toAdd) * coordinates P hp v
    rw [←coordinates_multiply,←coordinates_multiply]
    apply congrArg (coordinates P hp)
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [multiply,higherCoefficient,-fieldFrobenius_apply]
    · funext i
      fin_cases i <;> simp [multiply,higherCoefficient,add_comm,-fieldFrobenius_apply]
  · intro r hr
    obtain ⟨v,rfl⟩ := (coordinates P hp).surjective r
    have first_zero : v.1 0 = 0 ∧ v.1 1 = 0 := by
      have hpair (a : ExtensionField P) :
          armsPairing P (v.1 0) a = 0 ∧ armsPairing P (v.1 1) a = 0 := by
        let k := coordinates P hp (![0,0,a],0)
        have hk : firstLayer P hp k = 0 := by rw [firstLayer_coordinates]; rfl
        have hc : ⁅coordinates P hp v,k⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp hr k).symm)
        rw [commutator_of_firstLayer_zero P hp _ k hk,←coord_zero P hp] at hc
        have he := (coordinates P hp).injective hc
        have h0 := congrArg (fun u : RootOrbitParameters P .central => u.2 0) he
        have h1 := congrArg (fun u : RootOrbitParameters P .central => u.2 1) he
        simpa only [k,firstLayer,thirdLayer,Equiv.symm_apply_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons, Pi.zero_apply] using And.intro h0 h1
      exact ⟨armsPairing_left_nondegenerate P hp _ (fun a => (hpair a).1),
        armsPairing_left_nondegenerate P hp _ (fun a => (hpair a).2)⟩
    have hfirst : firstLayer P hp (coordinates P hp v) = 0 := by
      rw [firstLayer_coordinates,first_zero.1,first_zero.2]; rfl
    have third_zero : v.1 2 = 0 := by
      apply armsPairing_right_nondegenerate P hp
      intro a
      let k := coordinates P hp (![a,0,0],0)
      have hc : ⁅k,coordinates P hp v⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hr k)
      rw [commutator_of_firstLayer_zero P hp _ _ hfirst,←coord_zero P hp] at hc
      have he := congrArg (fun u : RootOrbitParameters P .central => u.2 0)
        ((coordinates P hp).injective hc)
      simpa only [k,firstLayer,thirdLayer,Equiv.symm_apply_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons, Pi.zero_apply] using he
    refine ⟨Multiplicative.ofAdd v.2,?_⟩
    apply congrArg (coordinates P hp)
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [first_zero.1,first_zero.2,third_zero]
    · rfl

/-- The long-root plane is the embedded center of the central radical. -/
@[expose] def plane (P : Parameters) : Subgroup (Carrier P) :=
  (center (radical P .central)).map (radical P .central).subtype

theorem plane_eq_range (P : Parameters) (hp : P.prime = 2) :
    plane P = ((radical P .central).subtype.comp (planeHom P hp)).range := by
  rw [MonoidHom.range_comp,planeHom_range]
  rfl

theorem plane_le_radical (P : Parameters) : plane P ≤ radical P .central := map_subtype_le _

theorem plane_mem_iff (P : Parameters) (hp : P.prime = 2) (x : Carrier P) :
    x ∈ plane P ↔ ∃ a b : fixedField P, long P hp 1 a * long P hp 2 b = x := by
  rw [plane_eq_range P hp]
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨v.toAdd 0,v.toAdd 1,(planeHom_val P hp v).symm⟩
  · rintro ⟨a,b,rfl⟩
    exact ⟨Multiplicative.ofAdd ![a,b],planeHom_val P hp _⟩

theorem plane_elementary (P : Parameters) (hp : P.prime = 2) :
    IsElementaryAbelian 2 (plane P) := by
  let : CharP (fixedField P) 2 := hp ▸ inferInstanceAs (CharP (fixedField P) P.prime)
  let : IsElementaryAbelian 2 (Multiplicative (Fin 2 → fixedField P)) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro a
      apply Multiplicative.toAdd.injective
      simp only [toAdd_pow, two_nsmul, toAdd_one]
      funext i
      exact CharTwo.add_self_eq_zero _ }
  rw [plane_eq_range P hp]
  exact IsElementaryAbelian.of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem plane_card (P : Parameters) (hp : P.prime = 2) : Nat.card (plane P) = P.q^2 := by
  let f := (radical P .central).subtype.comp (planeHom P hp)
  have hf : Function.Injective f := fun a b h =>
    planeHom_injective P hp ((radical P .central).subtype_injective h)
  rw [plane_eq_range P hp,←Nat.card_congr (MonoidHom.ofInjective (f := f) hf).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin,card_fixedField]

theorem plane_ne_bot (P : Parameters) (hp : P.prime = 2) : plane P ≠ ⊥ := by
  intro he
  have hc := plane_card P hp
  rw [he,card_bot] at hc
  have hq := P.q_ge_two
  have hh : 4 ≤ P.q^2 := by nlinarith
  omega

theorem plane_normalized (P : Parameters) :
    parabolic P .central ≤ normalizer (plane P : Set (Carrier P)) :=
  ((normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P .central)).mp
    (radical_normal P .central)).trans
    (normalizer_le_normalizer_characteristic_image _ (center _))

theorem plane_le_centralizer (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) : plane P ≤ centralizer ({short P hp 2 t} : Set (Carrier P)) := by
  have ht : short P hp 2 t ∈ radical P .central :=
    descendedRootSubgroup_le_radical P hp .central (short_mem P hp .central 2 trivial t)
  rintro x ⟨z,hz,rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((mem_center_iff.mp hz ⟨_,ht⟩).symm))

end Triality.Standard.ShortRootCentralizer
