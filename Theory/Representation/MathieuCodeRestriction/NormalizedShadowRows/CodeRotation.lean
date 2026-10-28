module
public import Theory.Representation.HexacodeAction.Field
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.CyclicFixedRank
public import Mathlib.LinearAlgebra.Pi

/-!
# Fixed-point-free quintic actions on the multiplicity plane

A faithful action on an F₄-plane has no fixed vectors under an element
of order five: its binary displacement is a positive multiple of four.
The pure-tensor action formula then transfers this fact to a sum of
copies of any finite-dimensional binary F₄-module. The proof uses
surjectivity of the multiplicity displacement and the coordinate summands.

Source application: Aschbacher--Smith 8.2.8(5--6), printed p.719,
refs/quasithin.pdf. The field and hexacode constructions are the existing
ATLAS port, attributed in Theory.Representation.HexacodeAction.Field and
LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace MathieuCode.NormalizedShadowRows.CodeRotation

theorem quintic_plane_fixedFree {Q : Type*} [Group Q]
    (μ : Representation Hexacode.F Q (Fin 2 → Hexacode.F))
    (hμ : Function.Injective μ.asGroupHom) (x : Q) (hx : orderOf x = 5) :
    ∀ c, μ x c = c → c = 0 := by
  let ρ : Representation (ZMod 2) Q (Fin 2 → Hexacode.F) := {
    toFun g := (μ g).restrictScalars (ZMod 2)
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun μ.map_one v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (μ.map_mul g h) v }
  have hd : Module.finrank (ZMod 2) (Fin 2 → Hexacode.F) = 4 := by
    rw [Module.finrank_pi_fintype]
    simp [show Module.finrank (ZMod 2) Hexacode.F = 2 from
      QuadraticAlgebra.finrank_eq_two _ _]
  have hdiv := four_dvd_fixedCodim_of_order_five ρ x hx
  have hn := fixedCodim_add_finrank ρ (zpowers x)
  rw [hd] at hn
  have hne : fixedCodim ρ (zpowers x) ≠ 0 := by
    intro hz
    have htop : fixedSpace ρ (zpowers x) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by omega)
    have he : μ.asGroupHom x = μ.asGroupHom 1 := by
      apply Units.ext
      apply LinearMap.ext
      intro v
      rw [map_one]
      exact (mem_fixedSpace_zpowers_iff ρ x v).mp (by rw [htop]; trivial)
    have hx1 := hμ he
    simp only [hx1,orderOf_one] at hx
    omega
  have hlo := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv
  have hbot : fixedSpace ρ (zpowers x) = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  intro c hc
  have hm : c ∈ fixedSpace ρ (zpowers x) := (mem_fixedSpace_zpowers_iff ρ x c).mpr hc
  simpa only [hbot,Submodule.mem_bot] using hm

theorem pure_tensor_fixedFree {Q E : Type*} [Group Q] [AddCommGroup E]
    [Module Hexacode.F E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) Q (Fin 2 → E))
    (μ : Representation Hexacode.F Q (Fin 2 → Hexacode.F))
    (he : ∀ a c v, ρ a (fun j => c j • v) = fun j => μ a c j • v)
    (a : Q) (ha : ∀ c, μ a c = c → c = 0) :
    ∀ w, ρ a w = w → w = 0 := by
  have hk : LinearMap.ker (μ a - 1) = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    exact ha c (sub_eq_zero.mp hc)
  have hs : Function.Surjective (⇑(μ a - 1)) :=
    LinearMap.range_eq_top.mp (LinearMap.ker_eq_bot_iff_range_eq_top.mp hk)
  have hr : LinearMap.range (ρ a - 1) = ⊤ := by
    apply top_unique
    intro w _
    have hexp : w = ∑ j : Fin 2, Pi.single j (w j) := by ext j; simp
    rw [hexp]
    apply Submodule.sum_mem
    intro j _
    obtain ⟨c,hc⟩ := hs (Pi.single j 1)
    refine ⟨fun k => c k • w j,?_⟩
    change ρ a (fun k => c k • w j) - (fun k => c k • w j) = Pi.single j (w j)
    rw [he]
    funext k
    have hck := congrFun hc k
    change μ a c k - c k = (Pi.single j (1 : Hexacode.F) : Fin 2 → Hexacode.F) k at hck
    change μ a c k • w j - c k • w j = (Pi.single j (w j) : Fin 2 → E) k
    rw [←sub_smul,hck]
    by_cases hj : j = k
    · subst k; simp
    · simp [Ne.symm hj]
  intro w hw
  have hh : w ∈ LinearMap.ker (ρ a - 1) := sub_eq_zero.mpr hw
  rw [LinearMap.ker_eq_bot_iff_range_eq_top.mpr hr] at hh
  exact hh

end MathieuCode.NormalizedShadowRows.CodeRotation
