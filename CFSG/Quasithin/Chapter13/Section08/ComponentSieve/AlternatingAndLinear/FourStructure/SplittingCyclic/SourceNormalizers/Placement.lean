module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.Lifting
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.Point
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.Placement
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Dual

/-!
# A₁ is outside the actual irreducible source subgroup

If A₁ lies in I, its nonzero image is a point in the chosen natural-or-dual
four-space. The corresponding point parabolic is perfect, so the kernel
lifting theorem makes it normalize Vγ*. The marked plane radical forces
Vγ* to fix a plane, contrary to point-parabolic rigidity. For the dual
orientation, the same actor identification is changed by the specified
contragredient automorphism and the marked plane becomes its annihilator.

The last theorem concludes A₁ ≰ I for the ambient subgroup, using the exact
identity between its section image and the chosen subrepresentation. The
order-two and distinct-line hypotheses make the image a point; fixation
modulo V₁ is never identified with exact fixation without the lifting proof.

Source: Aschbacher–Smith 13.8.25, printed p.961 (PDF p.978).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers
open CriticalTransfer ChiefFactors ChiefFactors.Alignment BinaryLinear
local notation "Vec" => (Fin 4 → ZMod 2)

private theorem fixes_binary_point {L : Submodule (ZMod 2) Vec}
    (hL : Module.finrank (ZMod 2) L = 1) {g : BinaryLinear.GL Vec}
    (hg : g ∈ parabolic L) {v : Vec} (hv : v ∈ L) : g v = v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hL hv hv0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ (hg v).mpr hv)
  have hc0 : c ≠ 0 := by
    intro hz
    exact hv0 (g.map_eq_zero_iff.mp (by simpa [hz] using hc.symm))
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

/-- Contragredience carries the marked radical to the annihilator radical. -/
theorem dualActor_mem_radical (P : Submodule (ZMod 2) Vec)
    (g : BinaryLinear.GL Vec) (hg : g ∈ radical P) :
    dualActor g ∈ radical (dualPlane P) := by
  have hgi : g⁻¹ ∈ radical P := (radical P).inv_mem hg
  constructor
  · intro v hv
    obtain ⟨f, rfl⟩ := dualCoordinates.surjective v
    rw [dualPlane_mem, LinearEquiv.symm_apply_apply] at hv
    rw [dualActor_apply_coordinates]
    apply congrArg dualCoordinates
    apply LinearMap.ext
    intro w
    change f (g.symm w) = f w
    have hh := (Submodule.mem_dualAnnihilator _).mp hv _ (hgi.2 w)
    change f (g.symm w - w) = 0 at hh
    exact sub_eq_zero.mp (by simpa only [map_sub] using hh)
  · intro v
    obtain ⟨f, rfl⟩ := dualCoordinates.surjective v
    rw [dualActor_apply_coordinates, ← map_sub, dualPlane_mem, LinearEquiv.symm_apply_apply,
      Submodule.mem_dualAnnihilator]
    intro p hp
    change f (g.symm p) - f p = 0
    have hh : g.symm p = p := hgi.1 p hp
    rw [hh, sub_self]

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}
  (s : ConjugationSection H UH Z ρ)

/-- Placement in one natural orientation, using ambient normality and proved perfect lifting. -/
theorem not_image_le_natural
    (A Vg : Subgroup G) (hAU : A ≤ UH)
    (hA : Module.finrank (ZMod 2) (s.image A) = 1)
    (hn : normalizer (A : Set G) ≤ normalizer (Vg : Set G))
    (N : Subrepresentation ρ)
    (eH : Source.Hstar H ≃* BinaryLinear.GL Vec)
    (eI : N.toSubmodule ≃ₗ[ZMod 2] Vec)
    (heI : ∀ g v, eI (N.toRepresentation g v) = eH g (eI v))
    (hB : Source.starImage H Vg ≠ ⊥) (hBtwo : IsPGroup 2 (Source.starImage H Vg))
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2)
    (g : Source.Hstar H)
    (hrad : ((Source.starImage H Vg).map (MulAut.conj g).toMonoidHom).map
      eH.toMonoidHom ≤ radical P) : ¬ s.image A ≤ N.toSubmodule := by
  intro hAI
  let AI := (s.image A).comap N.toSubmodule.subtype
  let L := AI.map eI.toLinearMap
  have hAI_dim : Module.finrank (ZMod 2) AI = 1 := by
    rw [← Submodule.finrank_map_subtype_eq N.toSubmodule AI]
    have he : AI.map N.toSubmodule.subtype = s.image A := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hAI]
    rw [he, hA]
  have hL : Module.finrank (ZMod 2) L = 1 :=
    (LinearEquiv.finrank_map_eq eI AI).trans hAI_dim
  let R := (parabolic L).comap eH.toMonoidHom
  let eR : R ≃* parabolic L := MulEquiv.ofBijective (eH.toMonoidHom.subgroupComap _) ⟨
    fun x y h => Subtype.ext (eH.injective (congrArg Subtype.val h)),
    MonoidHom.subgroupComap_surjective_of_surjective _ _ eH.surjective⟩
  let : Group.IsPerfect (parabolic L) := Point.parabolic_isPerfect L hL
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := eR.symm.toMonoidHom) eR.symm.surjective
  have hnR := perfect_normalizes_starImage s A Vg hAU hn R (by
    intro k hk a ha
    let ai : N.toSubmodule := ⟨a, hAI ha⟩
    have hai : eI ai ∈ L := ⟨ai, ha, rfl⟩
    have hf : eH k (eI ai) = eI ai := fixes_binary_point hL hk hai
    have he : N.toRepresentation k ai = ai := eI.injective ((heI k ai).trans hf)
    exact congrArg Subtype.val he)
  let B := (Source.starImage H Vg).map eH.toMonoidHom
  have hB0 : B ≠ ⊥ := by
    intro hb
    exact hB ((Subgroup.map_eq_bot_iff_of_injective _ eH.injective).mp hb)
  have hnorm : parabolic L ≤ normalizer (B : Set (BinaryLinear.GL Vec)) := by
    have hm : R.map eH.toMonoidHom = parabolic L :=
      Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr eH.surjective]; exact le_top)
    rw [← hm]
    exact (Subgroup.map_mono hnR).trans (Subgroup.le_normalizer_map _)
  have hr := le_radical_of_conjugate eH P (Source.starImage H Vg) g hrad
  apply point_parabolic_cannot_normalize_plane_fixer L (P.map (eH g⁻¹).toLinearMap)
    hL ((LinearEquiv.finrank_map_eq _ P).trans hP) B hB0 (hBtwo.map eH.toMonoidHom) _ hnorm
  intro p hp b hb
  exact (hr hb).1 p hp

/-- Placement in one natural orientation, using ambient normality and proved perfect lifting. -/
theorem not_image_le_naturalOrDual
    (A Vg : Subgroup G) (hAU : A ≤ UH)
    (hA : Module.finrank (ZMod 2) (s.image A) = 1)
    (hn : normalizer (A : Set G) ≤ normalizer (Vg : Set G))
    (N : Subrepresentation ρ)
    (eH : Source.Hstar H ≃* BinaryLinear.GL Vec)
    (hN : IsNaturalOrDual N.toRepresentation eH)
    (hB : Source.starImage H Vg ≠ ⊥) (hBtwo : IsPGroup 2 (Source.starImage H Vg))
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2)
    (g : Source.Hstar H)
    (hrad : ((Source.starImage H Vg).map (MulAut.conj g).toMonoidHom).map
      eH.toMonoidHom ≤ radical P) : ¬ s.image A ≤ N.toSubmodule := by
  rcases hN with ⟨e, he⟩ | ⟨e, he⟩
  · exact not_image_le_natural s A Vg hAU hA hn N eH e he hB hBtwo P hP g hrad
  · obtain ⟨e', he'⟩ := dual_is_natural N.toRepresentation eH e he
    apply not_image_le_natural s A Vg hAU hA hn N (eH.trans dualActor) e' he' hB hBtwo
      (dualPlane P) (dualPlane_finrank P hP) g
    rintro x ⟨b, hb, rfl⟩
    exact dualActor_mem_radical P (eH b) (hrad (Subgroup.mem_map_of_mem _ hb))

variable [Finite G] [FiniteDimensional (ZMod 2) U]
/-- A non-kernel order-two subgroup inside the numerator has one-dimensional image. -/
theorem image_finrank_one_of_order_two (A : Subgroup G) (hAU : A ≤ UH)
    (hA : Nat.card A = 2) (hAZ : ¬ A ≤ Z) :
    Module.finrank (ZMod 2) (s.image A) = 1 := by
  have hle : Module.finrank (ZMod 2) (s.image A) ≤ 1 := by
    have hh := s.image_finrank_le A
    simpa only [hA, show Nat.log 2 2 = 1 from by decide] using hh
  have hne : s.image A ≠ ⊥ := by
    intro hz
    apply hAZ
    intro a ha
    apply (s.quotient_eq_zero_iff ⟨a, hAU ha⟩).mp
    have hm : (s.quotient ⟨a, hAU ha⟩).toAdd ∈ s.image A := ⟨⟨a, hAU ha⟩, ha, rfl⟩
    rwa [hz] at hm
  have hpos : Module.finrank (ZMod 2) (s.image A) ≠ 0 :=
    fun hzero => hne (Submodule.finrank_eq_zero.mp hzero)
  omega

/-- The placement conclusion for the actual ambient subgroup I and its compatible section. -/
theorem A1_not_le_source_irreducible
    (A Vg I : Subgroup G) (hIU : I ≤ UH)
    (hA : Nat.card A = 2) (hAZ : ¬ A ≤ Z)
    (hn : normalizer (A : Set G) ≤ normalizer (Vg : Set G))
    (N : Subrepresentation ρ) (hI : s.image I = N.toSubmodule)
    (eH : Source.Hstar H ≃* BinaryLinear.GL Vec)
    (hN : IsNaturalOrDual N.toRepresentation eH)
    (hB : Source.starImage H Vg ≠ ⊥) (hBtwo : IsPGroup 2 (Source.starImage H Vg))
    (P : Submodule (ZMod 2) Vec) (hP : Module.finrank (ZMod 2) P = 2)
    (g : Source.Hstar H)
    (hrad : ((Source.starImage H Vg).map (MulAut.conj g).toMonoidHom).map
      eH.toMonoidHom ≤ radical P) : ¬ A ≤ I := by
  intro hAI
  have hAU := hAI.trans hIU
  apply not_image_le_naturalOrDual s A Vg hAU
    (image_finrank_one_of_order_two s A hAU hA hAZ) hn N eH hN hB hBtwo P hP g hrad
  rw [← hI]
  exact s.image_mono hAI

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers
