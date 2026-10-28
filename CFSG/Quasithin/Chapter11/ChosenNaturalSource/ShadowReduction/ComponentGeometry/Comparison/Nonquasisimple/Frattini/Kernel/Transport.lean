module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Kernel.Elementary
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs

/-!
# Transport of the elementary-extension normalizer calculation

The actual elementary-kernel and SL₂ quotient isomorphisms supply the
intrinsic calculation. Pulling it back through a surjective two-kernel
map preserves the two-group bound. Normalizers are mapped only forwards;
no unproved normalizer lifting or splitting assertion is used.

The companion source application uses the literal quotient by O₂(Kz),
and keeps the original Sylow subgroup of the solvable radical.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Kernel
variable {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
  {p : ℕ} [Fact p.Prime]
/-- Apply the intrinsic kernel argument to the actual extension model, without
choosing a natural action or a splitting of the extension. -/
theorem radical_inf_normalizer_of_extension
    (hp : 3 < p) (hn : ¬ IsQuasisimple A)
    (hm : Chapter1.Section02.LocalModels.HasExtension A
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p))
    (P : Subgroup A) (hP : Chapter1.IsSylowIn 2 P (solvableRadical A)) :
    IsPGroup 2 (solvableRadical A ⊓ normalizer (P : Set A) : Subgroup A) := by
  classical
  obtain ⟨N,hNN,⟨v⟩,F,_,_,hF,⟨e⟩⟩ := hm
  let : N.Normal := hNN
  let : IsMulCommutative N := ⟨⟨fun x y => v.injective (by simp only [map_mul,mul_comm])⟩⟩
  let : IsElementaryAbelian p N := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro n
      apply v.injective
      rw [map_pow,map_one]
      change p • (v n).toAdd = 0
      ext i
      simp [nsmul_eq_mul]) }
  have hN : Nat.card N = p ^ 2 := by
    rw [Nat.card_congr v.toEquiv]
    simp [Nat.card_eq_fintype_card]
  let : Fintype F := Fintype.ofFinite F
  let a := (ZMod.ringEquivOfPrime F (Fact.out : p.Prime)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let e' := e.trans (Atlas.fieldEquivSL 2 a)
  obtain ⟨S,hS⟩ := hP
  rw [← hS]
  exact radical_inf_normalizer_isPGroup hp hn N hN e' S

variable {K : Type*} [Group K] [Finite K]

/-- Pull normalizer-radical two-group control back through the original
normal two-kernel. Only forward image containment of normalizers is needed. -/
theorem radical_inf_normalizer_of_two_kernel
    (q : K →* A) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hp : 3 < p) (hn : ¬ IsQuasisimple A)
    (hm : Chapter1.Section02.LocalModels.HasExtension A
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p))
    (P : Subgroup K) (hP : Chapter1.IsSylowIn 2 P (solvableRadical K)) :
    IsPGroup 2 (solvableRadical K ⊓ normalizer (P : Set K) : Subgroup K) := by
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  have hr : (solvableRadical K).map q = solvableRadical A := by
    rw [← comap_solvableRadical_eq_of_solvable_ker q hq,
      map_comap_eq_self_of_surjective hq]
  have hP' := Chapter1.Section02.IndexTwo.isSylowIn_map hP q
  rw [hr] at hP'
  have htwo := radical_inf_normalizer_of_extension hp hn hm (P.map q) hP'
  apply (htwo.comap_of_ker_isPGroup q hk).to_le
  rw [Subgroup.comap_inf]
  apply le_inf
  · exact inf_le_left.trans (map_le_iff_le_comap.mp hr.le)
  · exact inf_le_right.trans (map_le_iff_le_comap.mp (P.le_normalizer_map q))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini.Kernel
