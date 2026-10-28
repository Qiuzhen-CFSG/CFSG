module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.TorusParity
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.NativeGeometry

/-!
# Marked linear Weyl pairs and their odd-order products

The two endpoint reflections and the entire split torus are transported
through the same faithful native completion. Their six successive torus
actions give the cubic action identity; scalar quotients are preserved.
When involution centralizers normalize ambient Sylow two-subgroups, the
dihedral parity argument makes the actual product odd, also over field four.

This is the parity step in Aschbacher–Smith F.4.49, printed pp.298–299.
It supplies no cube-in-middle relation by itself: centralizing the torus
must still be distinguished from belonging to the whole marked overlap.
The original source hypotheses are discharged by the Chapter6 application.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearAmbientGeometry
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G] (c : NativeCompletion F G)

def torusHom : (Fˣ × Fˣ) →* G := c.middle.comp
  ((torusMap F).codRestrict (borel F) (fun d => torus_le_borel F ⟨d,rfl⟩))

def endpointHom (i : Bool) : parabolic F i →* G :=
  match i with | false => c.left | true => c.right

omit [Finite F] [CharP F 2] in
theorem endpointHom_injective (i : Bool) : Function.Injective (c.endpointHom i) := by
  cases i
  · exact c.left_injective
  · exact c.right_injective

def weyl (i : Bool) : G := c.endpointHom i ⟨reflection F i,reflection_mem F i⟩

omit [CharP F 2] in
theorem endpointHom_torus (i : Bool) (d : Fˣ × Fˣ) :
    c.endpointHom i ⟨torusMap F d,(torus_le_borel F).trans (borel_le_parabolic F i) ⟨d,rfl⟩⟩ =
      c.torusHom d := by
  cases i
  · rfl
  · exact (DFunLike.congr_fun c.compatible ⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩).symm

omit [CharP F 2] in
theorem torusHom_eq_iff (d e : Fˣ × Fˣ) :
    c.torusHom d=c.torusHom e ↔ torusMap F d=torusMap F e := by
  constructor
  · intro hh
    exact congrArg Subtype.val (c.middle_injective hh)
  · intro hh
    exact congrArg c.middle (Subtype.ext hh)

theorem weyl_sq (i : Bool) : c.weyl i^2=1 := by
  rw [weyl,←map_pow]
  have hh : (⟨reflection F i,reflection_mem F i⟩ : parabolic F i)^2=1 :=
    Subtype.ext (reflection_sq F i)
  rw [hh,map_one]

theorem weyl_mem (i : Bool) : c.weyl i ∈ c.family i := by
  cases i <;> exact ⟨_,rfl⟩

theorem weyl_not_mem_middle (i : Bool) :
    c.weyl i ∉ c.middle.range := by
  rintro ⟨b,hb⟩
  cases i
  · have he := c.left_injective hb
    have he' : b.val=reflection F false := congrArg Subtype.val he
    exact reflection_not_mem_borel F false (he' ▸ b.property)
  · have hm : c.middle b=c.right ((GreenBook.LieModels.LinearThree.amalgam F).right b) :=
      DFunLike.congr_fun c.compatible b
    have he := c.right_injective (hm.symm.trans hb)
    have he' : b.val=reflection F true := congrArg Subtype.val he
    exact reflection_not_mem_borel F true (he' ▸ b.property)

theorem weyl_torus_conj (i : Bool) (d : Fˣ × Fˣ) :
    c.weyl i*c.torusHom d*(c.weyl i)⁻¹ =
      c.torusHom (reflectionParameters F i d) := by
  rw [←c.endpointHom_torus i d,weyl,←map_inv,←map_mul,←map_mul]
  rw [←c.endpointHom_torus i (reflectionParameters F i d)]
  congr 1
  exact Subtype.ext (reflection_torus_conj F i d)

theorem weyl_normalizes_torus (i : Bool) :
    c.weyl i ∈ normalizer (c.torusHom.range : Set G) := by
  have hconj (x : G) (hx : x∈c.torusHom.range) :
      c.weyl i*x*(c.weyl i)⁻¹ ∈ c.torusHom.range := by
    obtain ⟨d,rfl⟩ := hx
    exact ⟨reflectionParameters F i d,(c.weyl_torus_conj i d).symm⟩
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hconj x,fun hx => ?_⟩
  have hh := hconj _ hx
  have he : c.weyl i*(c.weyl i*x*(c.weyl i)⁻¹)*(c.weyl i)⁻¹=x := by
    calc
      _ = (c.weyl i)^2*x*((c.weyl i)^2)⁻¹ := by simp only [pow_succ,pow_zero]; group
      _ = x := by rw [c.weyl_sq]; simp
  rwa [he] at hh

theorem weyl_not_centralizes_torus (hq : 2<Nat.card F) (i : Bool) :
    c.weyl i ∉ centralizer (c.torusHom.range : Set G) := by
  intro hc
  apply reflection_not_centralizes_torus F hq i
  rintro x ⟨d,rfl⟩
  have he : c.torusHom (reflectionParameters F i d)=c.torusHom d := by
    rw [←c.weyl_torus_conj,←hc _ ⟨d,rfl⟩,mul_inv_cancel_right]
  have he' := (c.torusHom_eq_iff _ _).mp he
  rw [←reflection_torus_conj] at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- The cube acts trivially on the same marked torus. This is an action
identity; it does not assert cube membership in the torus or middle. -/
theorem weyl_product_cube_centralizes (i : Bool) :
    (c.weyl i*c.weyl (!i))^3 ∈ centralizer (c.torusHom.range : Set G) := by
  have hstep (d : Fˣ × Fˣ) :
      (c.weyl i*c.weyl (!i))*c.torusHom d*(c.weyl i*c.weyl (!i))⁻¹ =
        c.torusHom (reflectionParameters F i (reflectionParameters F (!i) d)) := by
    calc
      _ = c.weyl i*(c.weyl (!i)*c.torusHom d*(c.weyl (!i))⁻¹)*(c.weyl i)⁻¹ := by group
      _ = _ := by rw [c.weyl_torus_conj,c.weyl_torus_conj]
  rintro _ ⟨d,rfl⟩
  have he : (c.weyl i*c.weyl (!i))^3*c.torusHom d*((c.weyl i*c.weyl (!i))^3)⁻¹ = c.torusHom d := by
    calc
      _ = (c.weyl i*c.weyl (!i))*((c.weyl i*c.weyl (!i))*
        ((c.weyl i*c.weyl (!i))*c.torusHom d*(c.weyl i*c.weyl (!i))⁻¹)*
          (c.weyl i*c.weyl (!i))⁻¹)*(c.weyl i*c.weyl (!i))⁻¹ := by simp only [pow_succ,pow_zero]; group
      _ = _ := by
        rw [hstep,hstep,hstep]
        congr 1
        cases i <;> ext <;> simp [reflectionParameters,mul_comm]
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

omit [CharP F 2] in
theorem torusHom_odd {n : ℕ} (hF : Nat.card F=2^n) :
    Odd (Nat.card c.torusHom.range) := by
  apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd c.torusHom)
  rw [Nat.card_prod]
  exact (BorelQuotient.units_odd F hF).mul (BorelQuotient.units_odd F hF)

variable [Finite G]
/-- The original involution-centralizer condition rules out even Weyl
products in every marked native completion, including field four. -/
theorem weyl_product_odd {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (hC : ∀ z : G, orderOf z=2 → ∃ P : Sylow 2 G,
      centralizer ({z} : Set G) ≤ normalizer (P : Set G)) (i : Bool) :
    Odd (orderOf (c.weyl i*c.weyl (!i))) := by
  have hq : 2<Nat.card F := hF ▸ Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hn
  exact odd_weyl_product hC _ (c.torusHom_odd hF) _ _
    (c.weyl_sq i) (c.weyl_sq (!i)) (c.weyl_normalizes_torus i)
    (c.weyl_not_centralizes_torus hq i) (c.weyl_product_cube_centralizes i)

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.NativeCompletion
