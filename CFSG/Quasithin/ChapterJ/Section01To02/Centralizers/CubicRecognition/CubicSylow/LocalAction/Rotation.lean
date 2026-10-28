module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Actions
public import Theory.GroupTheory.PGroup.OrderTwentySevenEightAut
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The order-eight action and exponent in the cubic argument

The fourth power of a marked rotation is the original z. Its conjugation
automorphism has order eight: otherwise z would fix all 27 elements of R,
whereas its fixed subgroup is the original B of order three. The checked
order-27 automorphism theorem then gives exponent three, in both the abelian
and nonabelian branches. No exponent or noncommutativity premise is used.

Once the center of T_R is identified with <z>, the entire original action
on R is faithful. Indeed a nontrivial normal kernel in a two-group meets
the center, and hence would contain z.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The original z cannot act trivially on a Sylow three-subgroup of N_G(B). -/
theorem action_z_ne_one (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (hzT : c.z ∈ TR c R Tplus) :
    action c R Tplus ⟨c.z, hzT⟩ ≠ 1 := by
  intro he
  have hR : ambient c R ≤ c.B := by
    intro x hx
    rw [← centralizer_z_eq c hB P hP R]
    refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
    have h := congrArg (fun a : MulAut (ambient c R) => (a ⟨x, hx⟩ : G)) he
    change c.z * x * c.z⁻¹ = x at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hc := card_le_of_le hR
  rw [ambient_card c hB e R, hB] at hc
  omega

/-- The action order follows from the literal fourth-power marking. -/
theorem rotation_action_order (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (r : TR c R Tplus)
    (hr8 : (r : G) ^ 8 = 1) (hr4 : (r : G) ^ 4 = c.z) :
    orderOf (action c R Tplus r) = 8 := by
  have hzT : c.z ∈ TR c R Tplus := hr4 ▸ (TR c R Tplus).pow_mem r.property 4
  have hr4' : r ^ 4 = ⟨c.z, hzT⟩ := Subtype.ext hr4
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · change action c R Tplus r ^ 4 ≠ 1
    rw [← map_pow, hr4']
    exact action_z_ne_one c hB P hP e R Tplus hzT
  · change action c R Tplus r ^ 8 = 1
    rw [← map_pow, show r ^ 8 = 1 from Subtype.ext hr8, map_one]

/-- The fourth-power fixed points are exactly C_R(z), of order three. -/
theorem rotation_fourth_fixed_card (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (r : TR c R Tplus)
    (hr4 : (r : G) ^ 4 = c.z) :
    Nat.card {x : ambient c R // (action c R Tplus r ^ 4) x = x} = 3 := by
  have hzT : c.z ∈ TR c R Tplus := hr4 ▸ (TR c R Tplus).pow_mem r.property 4
  have hr4' : r ^ 4 = ⟨c.z, hzT⟩ := Subtype.ext hr4
  rw [← map_pow, hr4']
  exact fixed_card_z c hB P hP R Tplus hzT

/-- Exponent three is derived from the rotation, rather than included among
the hypotheses of the local geometry. -/
theorem cube_eq_one_of_rotation (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (r : TR c R Tplus)
    (hr8 : (r : G) ^ 8 = 1) (hr4 : (r : G) ^ 4 = c.z) :
    ∀ x : ambient c R, x ^ 3 = 1 :=
  OrderTwentySeven.cube_eq_one_of_eight_aut (ambient_card c hB e R)
    (action c R Tplus r) (rotation_action_order c hB P hP e R Tplus r hr8 hr4)
    (rotation_fourth_fixed_card c hB P hP R Tplus r hr4)

/-- A marked center makes the original T_R-action on R faithful. -/
theorem action_injective_of_center (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (hcenter : (center (TR c R Tplus)).map (TR c R Tplus).subtype = zpowers c.z) :
    Function.Injective (action c R Tplus) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hker
  let : Nontrivial (action c R Tplus).ker := (nontrivial_iff_ne_bot _).mpr hker
  let : Fact (IsPGroup 2 (TR c R Tplus)) := ⟨TR_isPGroup c R Tplus⟩
  obtain ⟨x, hx, hc⟩ := exists_nontrivial_center_mem_normal (p := 2) (action c R Tplus).ker
  have hmem : ((x : TR c R Tplus) : G) ∈ zpowers c.z :=
    hcenter ▸ mem_map_of_mem (TR c R Tplus).subtype hc
  rw [mem_zpowers_iff_mem_range_orderOf, hz, Finset.mem_image] at hmem
  obtain ⟨n, hn, he⟩ := hmem
  have hn' : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · apply hx
    apply Subtype.ext
    apply Subtype.ext
    change ((x : TR c R Tplus) : G) = 1
    simpa only [pow_zero] using he.symm
  · have hez : ((x : TR c R Tplus) : G) = c.z := by
      simpa only [pow_one] using he.symm
    have hzT : c.z ∈ TR c R Tplus := hez ▸ (x : TR c R Tplus).property
    have hxz : (x : TR c R Tplus) = ⟨c.z, hzT⟩ := Subtype.ext hez
    apply action_z_ne_one c hB P hP e R Tplus hzT
    rw [← hxz]
    exact x.property

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction
