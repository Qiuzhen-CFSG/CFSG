module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Intersection.Model

/-!
# Second fixed layers on the whole six-letter cover

Conjugate a two-subgroup into the explicit sixteen-element Sylow group.
The three paired coordinate vectors lie in its second fixed layer.
An element fixing those vectors sends every augmentation vector into their
span. Thus an actor centralizing any larger layer has displacement inside
that layer. Fixed vectors lift through the natural quotient, so the same
argument retains both whole-cover orders sixteen and thirty-two.

Source: MS93 (3.6), printed p.871, the implication from centralization of
the critical plane to containment of the opposite-layer displacement.
The literal critical-plane application is in Noncentral.Source.
-/

@[expose] public noncomputable section
open Subgroup Representation BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral

private def paired (v : Fin 6 → ZMod 2) : Prop :=
  v 0 = v 1 ∧ v 2 = v 3 ∧ v 4 = v 5
private instance (v : Fin 6 → ZMod 2) : Decidable (paired v) := by
  unfold paired
  infer_instance

private def seed (i : Fin 3) : core (Fin 6) :=
  ⟨fun j => if j.val / 2 = i.val then 1 else 0, by
    rw [mem_core]
    fin_cases i <;> decide⟩

private theorem seed_paired : ∀ i : Fin 3, paired (seed i).val := by decide +kernel

private theorem paired_second_table : ∀ i j : Fin 16, ∀ v : Fin 6 → ZMod 2,
    paired v →
    representation (Fin 6) (Six.sylowWords j)
      (representation (Fin 6) (Six.sylowWords i) v-v) =
      representation (Fin 6) (Six.sylowWords i) v-v := by decide +kernel

private theorem fixed_seed_table : ∀ i : Fin 16,
    (∀ k : Fin 3, representation (Fin 6) (Six.sylowWords i) (seed k).val = (seed k).val) →
    ∀ v : Fin 6 → ZMod 2, paired (representation (Fin 6) (Six.sylowWords i) v-v) := by
  decide +kernel

/-- A vector in the second fixed layer for the indicated actor. -/
def SecondFixed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Six.Perm V) (B : Subgroup Six.Perm) (v : V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ρ b (ρ a v-v) = ρ a v-v

private theorem paired_second (v : core (Fin 6)) (hv : paired v.val) :
    SecondFixed (coreRepresentation (Fin 6)) Six.sylowCarrier v := by
  rintro a ha b hb
  obtain ⟨i,rfl⟩ := (Six.mem_sylowCarrier_iff _).mp ha
  obtain ⟨j,rfl⟩ := (Six.mem_sylowCarrier_iff _).mp hb
  exact Subtype.ext (paired_second_table i j v.val hv)

theorem core_displacement_of_second_fixed
    (B : Subgroup Six.Perm) (hp : IsPGroup 2 B)
    (P : core (Fin 6) → Prop)
    (hP : ∀ v, SecondFixed (coreRepresentation (Fin 6)) B v → P v)
    (n : Six.Perm) (hn : n ∈ B)
    (hfix : ∀ v, P v → coreRepresentation (Fin 6) n v = v)
    (v : core (Fin 6)) : P (coreRepresentation (Fin 6) n v-v) := by
  let ρ := coreRepresentation (Fin 6)
  obtain ⟨S,hBS⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Six.Perm S Six.sylow
  let c := (MulAut.conj g).toMonoidHom
  have hBc {x : Six.Perm} (hx : x ∈ B) : c x ∈ Six.sylowCarrier := by
    change (MulAut.conj g) x ∈ (Six.sylow : Subgroup Six.Perm)
    rw [←hg]
    exact mem_map_of_mem _ (hBS hx)
  have hconj (x : Six.Perm) (w : core (Fin 6)) :
      ρ (c x) (ρ g w) = ρ g (ρ x w) := by
    change ρ (g*x*g⁻¹) (ρ g w) = _
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have hback (w : core (Fin 6)) (hw : SecondFixed ρ Six.sylowCarrier w) :
      SecondFixed ρ B (ρ g⁻¹ w) := by
    intro a ha b hb
    have he := hw (c a) (hBc ha) (c b) (hBc hb)
    have hh (x : Six.Perm) (z : core (Fin 6)) :
        ρ g⁻¹ (ρ (c x) z) = ρ x (ρ g⁻¹ z) := by
      change ρ g⁻¹ (ρ (g*x*g⁻¹) z) = _
      simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left]
    have he' := congrArg (ρ g⁻¹) he
    simpa only [map_sub,hh] using he'
  obtain ⟨i,hi⟩ := (Six.mem_sylowCarrier_iff _).mp (hBc hn)
  have hs (k : Fin 3) : ρ (c n) (seed k) = seed k := by
    have hf := hfix _ (hP _ (hback _ (paired_second _ (seed_paired k))))
    have hh := congrArg (ρ g) hf
    have hinv : ρ g (ρ g⁻¹ (seed k)) = seed k := by
      simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [←hconj,hinv] at hh
    exact hh
  have hm : paired (ρ (c n) (ρ g v)-ρ g v).val := by
    rw [←hi]
    exact fixed_seed_table i (fun k => congrArg Subtype.val (hi ▸ hs k)) _
  have hh := hP _ (hback _ (paired_second _ hm))
  rw [hconj,←map_sub] at hh
  simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh

/-- Centralizing the second fixed layer forces displacement into that layer,
on either whole central cover. No elementary hypothesis on B is needed. -/
theorem cover_displacement_of_second_fixed
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Six.Perm V)
    (hm : SixCover.IsNaturalOrCore ρ (MonoidHom.id _))
    (B : Subgroup Six.Perm) (hp : IsPGroup 2 B) (P : V → Prop)
    (hP : ∀ v, SecondFixed ρ B v → P v)
    (n : Six.Perm) (hn : n ∈ B) (hfix : ∀ v, P v → ρ n v = v)
    (v : V) : P (ρ n v-v) := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩ <;> simp only [MonoidHom.id_apply] at hE
  · let f : core (Fin 6) →ₗ[ZMod 2] V := E.symm.toLinearMap.comp (coreToNatural (Fin 6))
    have hf (a : Six.Perm) (w : core (Fin 6)) :
        f (coreRepresentation (Fin 6) a w) = ρ a (f w) := by
      apply E.injective
      simp only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
        hE,coreToNatural_equivariant]
    have hpf (w : core (Fin 6)) (hw : SecondFixed (coreRepresentation (Fin 6)) B w) :
        P (f w) := by
      apply hP
      intro a ha b hb
      have hh := congrArg f (hw a ha b hb)
      simpa only [map_sub,hf] using hh
    obtain ⟨w,hw⟩ := coreToNatural_surjective (E v)
    have hfv : f w = v := by simp only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,hw,
      LinearEquiv.symm_apply_apply]
    have hh := core_displacement_of_second_fixed B hp (fun w => P (f w)) hpf n hn
      (fun w hw => by
        apply SixCover.six_core_fixed_of_natural_fixed
        have he := congrArg E (hfix (f w) hw)
        simpa only [hE,f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
          using he) w
    simpa only [map_sub,hf,hfv] using hh
  · have hf (a : Six.Perm) (w : core (Fin 6)) :
        E.symm (coreRepresentation (Fin 6) a w) = ρ a (E.symm w) := by
      apply E.injective
      simp only [hE,LinearEquiv.apply_symm_apply]
    have hp' (w : core (Fin 6)) (hw : SecondFixed (coreRepresentation (Fin 6)) B w) :
        P (E.symm w) := by
      apply hP
      intro a ha b hb
      have hh := congrArg E.symm (hw a ha b hb)
      simpa only [map_sub,hf] using hh
    have hh := core_displacement_of_second_fixed B hp (fun w => P (E.symm w)) hp' n hn
      (fun w hw => by
        have he := congrArg E (hfix (E.symm w) hw)
        simpa only [hE,LinearEquiv.apply_symm_apply] using he) (E v)
    simpa only [map_sub,hf,LinearEquiv.symm_apply_apply] using hh

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
