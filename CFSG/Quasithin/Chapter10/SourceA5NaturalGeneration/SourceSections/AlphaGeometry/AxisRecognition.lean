module
public import Theory.GroupTheory.ProductCoordinateKernels
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.TorusCoordinates
public import Theory.GroupTheory.SymmetricNormalQuotients
/-!
# Cartan axes under an equivalent paired natural marking

The selected natural actor may use an equivalent product marking. Its
coordinate kernels still coincide, up to exchange, with the two original
A5 quotient kernels. A nonzero vector fixed by the actual cubic subgroup
therefore identifies one of the original torus axes.

Source: Aschbacher--Smith 10.2.3(4), printed p.746.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
local notation "A" => alternatingGroup (Fin 5)
variable {G F : Type*} [Group G] [Finite G] [Field F] [CharP F 2]
theorem source_a5_cartan_axis_of_equivalent_natural_pair
    (hcore : pCore 2 A = ⊥)
    (C P : Subgroup G) (q : C →* A × A) (hq : Function.Injective q)
    (hc : Nat.card C = 9) (hC : IsElementaryAbelian 3 C)
    (a : A ≃* SL(2,F)) (e : (A × A) ≃* (SL(2,F) × SL(2,F)))
    (hPC : P ≤ C) (hP : Nat.card P = 3)
    (v : (Fin 2 → F) × (Fin 2 → F)) (hv : v ≠ 0)
    (hfix : ∀ p : C, (p:G) ∈ P →
      ((e (q p)).1.val *ᵥ v.1,(e (q p)).2.val *ᵥ v.2) = v) :
    P = ((MonoidHom.snd A A).comp q).ker.map C.subtype ∨
      P = ((MonoidHom.fst A A).comp q).ker.map C.subtype := by
  let q₁ := (MonoidHom.fst A A).comp q
  let q₂ := (MonoidHom.snd A A).comp q
  let r₁ := (MonoidHom.fst (SL(2,F)) (SL(2,F))).comp (e.toMonoidHom.comp q)
  let r₂ := (MonoidHom.snd (SL(2,F)) (SL(2,F))).comp (e.toMonoidHom.comp q)
  have hcub : ∀ p : C, p ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hC.exponent_dvd_p
  have hline := Representation.SL2.PairedCubicAxes.le_kernel_or_le_kernel_of_cube_eq_one
    r₁ r₂ (P.subgroupOf C) (fun p _ => hcub p) v hv hfix
  have haxes := Theory.AlternatingFive.nine_torus_coordinate_kernels q hq
    (IsPGroup.of_card (n := 2) hc) hc
  have finish (K : Subgroup C) (hK : P.subgroupOf C ≤ K) (hcard : Nat.card K = 3) :
      P = K.map C.subtype := by
    apply eq_of_le_of_card_ge
    · intro p hp
      exact mem_map.mpr ⟨⟨p,hPC hp⟩,hK hp,rfl⟩
    · rw [card_map_of_injective C.subtype_injective,hcard,hP]
  let b : MulAut (A × A) := e.trans (a.prodCongr a).symm
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have hperm := Theory.GroupTheory.product_automorphism_coordinate_kernels
    (fun N _ hn => Theory.GroupTheory.simple_normal_quotient_two N hn)
    hcore (alternatingGroup.center_eq_bot (by simp)) b
  have transport (r : C →* SL(2,F)) (k : C →* A)
      (h : ∀ x : C, a.symm (r x) = 1 ↔ k x = 1) : r.ker = k.ker := by
    ext x
    change r x = 1 ↔ k x = 1
    simpa only [a.symm.map_eq_one_iff] using h x
  rcases hperm with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · have hr₁ : r₁.ker = q₁.ker := transport r₁ q₁ (fun x => h₁ (q x))
    have hr₂ : r₂.ker = q₂.ker := transport r₂ q₂ (fun x => h₂ (q x))
    rcases hline with h | h
    · exact Or.inr (finish q₁.ker (hr₁ ▸ h) haxes.1)
    · exact Or.inl (finish q₂.ker (hr₂ ▸ h) haxes.2.1)
  · have hr₁ : r₁.ker = q₂.ker := transport r₁ q₂ (fun x => h₁ (q x))
    have hr₂ : r₂.ker = q₁.ker := transport r₂ q₁ (fun x => h₂ (q x))
    rcases hline with h | h
    · exact Or.inl (finish q₂.ker (hr₁ ▸ h) haxes.2.1)
    · exact Or.inr (finish q₁.ker (hr₂ ▸ h) haxes.1)
end CFSG.Quasithin.Chapter10
