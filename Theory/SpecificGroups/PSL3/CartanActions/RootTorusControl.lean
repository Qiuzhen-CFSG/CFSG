module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OrdinaryComplement
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.QuotientActions
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation


/-!
# A compatible root torus for the PSL₃ Borel calculation

The one-parameter torus `diag(a,1,a⁻¹)` is fixed by the opposition graph
and complements the centralizer of the highest-root group in characteristic
two. A standard automorphism preserving the upper unipotent subgroup takes
its elements to unipotent multiples of field-conjugate torus elements.
The quotient formula retains the cubic scalar kernel of the projective group.
If such a displacement centralizes the highest-root group, its torus factor
is trivial, so the displacement lies in the unipotent two-core.

Binary root orientation and coefficient reconstruction supply the actual
automorphism coverage, including the small fields; no coverage premise is
left in `displacement_mem_unipotent`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3b)
and the factor-count paragraph of E.6.25, printed pp.249–250,255;
GLS3, Theorem 2.5.12 and §2.7 for the standard matrix automorphisms.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.BorelQuotient Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.CartanActions.RootTorusControl
variable (F : Type*) [Field F]

def rootTorus : Fˣ →* PSL(3,F) := (torusMap F).comp
  { toFun := fun a => (a,a⁻¹)
    map_one' := by simp
    map_mul' := by intros; simp [mul_comm] }

theorem rootTorus_apply (a : Fˣ) : rootTorus F a = torusMap F (a,a⁻¹) := rfl

theorem graph_rootTorus (a : Fˣ) : oppositionGraph F (rootTorus F a) = rootTorus F a := by
  simp only [rootTorus_apply, oppositionGraph_torusMap, inv_inv]

theorem field_rootTorus (σ : F ≃+* F) (a : Fˣ) :
    fieldAction F σ (rootTorus F a) = rootTorus F (Units.map σ.toMonoidHom a) := by
  simp only [rootTorus_apply, field_torusMap, map_inv]

variable [Finite F] [CharP F 2]

theorem rootTorus_eq_one_of_centralizes (a : Fˣ)
    (h : rootTorus F a ∈ centralizer (projectiveCenter F : Set PSL(3,F))) : a = 1 := by
  have he := ((mem_centralizer_projectiveCenter_iff F (torusSL F (a,a⁻¹))).mp h).2
  have ha : (a : F) = ((a⁻¹ : Fˣ) : F) := he
  apply Units.ext
  apply frobenius_inj F 2
  change (a : F)^2 = (1 : F)^2
  calc
    (a : F)^2 = (a : F) * ((a⁻¹ : Fˣ) : F) := by rw [pow_two]; exact congrArg ((a : F) * ·) ha
    _ = 1^2 := by simp

theorem rootTorus_injective : Function.Injective (rootTorus F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  apply mem_bot.mpr
  apply rootTorus_eq_one_of_centralizes F a
  change rootTorus F a = 1 at ha
  rw [ha]
  exact one_mem _

omit [CharP F 2] in
theorem rootTorus_le_borel : (rootTorus F).range ≤ borel F := by
  rintro _ ⟨a,rfl⟩
  exact torus_le_borel F ⟨(a,a⁻¹),rfl⟩

theorem rootTorus_disjoint :
    centralizer (projectiveCenter F : Set PSL(3,F)) ⊓ (rootTorus F).range = ⊥ := by
  apply bot_unique
  rintro _ ⟨hc,a,rfl⟩
  rw [rootTorus_eq_one_of_centralizes F a hc, map_one]
  exact one_mem _

omit [Finite F] [CharP F 2] in
private theorem unipotent_centralizes :
    unipotent F ≤ centralizer (projectiveCenter F : Set PSL(3,F)) := by
  intro u hu
  apply mem_centralizer_iff.mpr
  rintro z hz
  rw [projectiveCenter_eq_mapped_center] at hz
  obtain ⟨z,hz,rfl⟩ := hz
  exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨u,hu⟩)).symm

theorem rootTorus_complement :
    centralizer (projectiveCenter F : Set PSL(3,F)) ⊔ (rootTorus F).range = borel F := by
  apply le_antisymm
  · apply sup_le
    · exact le_sup_left.trans (centralizer_sup_complementTorus F).le
    · exact rootTorus_le_borel F
  · intro g hg
    obtain ⟨d,u,hu,rfl⟩ := borel_factorization F g hg
    have hinj : Function.Injective (fun a : Fˣ => a^2) := by
      intro a b hab
      apply Units.ext
      exact frobenius_inj F 2 (congrArg Units.val hab)
    obtain ⟨a,ha⟩ := (Finite.injective_iff_surjective.mp hinj) (d.1 * d.2⁻¹)
    change a^2 = d.1 * d.2⁻¹ at ha
    have he : d.1 * a⁻¹ = d.2 * a := by
      calc
        d.1 * a⁻¹ = (d.1 * d.2⁻¹) * d.2 * a⁻¹ := by group
        _ = a^2 * d.2 * a⁻¹ := by rw [ha]
        _ = d.2 * a := by simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
    have hc : torusMap F (d * (a,a⁻¹)⁻¹) ∈
        centralizer (projectiveCenter F : Set PSL(3,F)) := by
      change projection F (torusSL F _) ∈ _
      rw [mem_centralizer_projectiveCenter_iff]
      refine ⟨torusSL_mem_borel F _, ?_⟩
      change ((d.1 * a⁻¹ : Fˣ) : F) = ((d.2 * (a⁻¹)⁻¹ : Fˣ) : F)
      simpa only [inv_inv] using congrArg Units.val he
    have ht : torusMap F d = torusMap F (d * (a,a⁻¹)⁻¹) * rootTorus F a := by
      rw [rootTorus_apply, map_mul, map_inv, inv_mul_cancel_right]
    rw [ht]
    exact mul_mem (mem_sup_left (unipotent_centralizes F hu))
      (mul_mem (mem_sup_left hc) (mem_sup_right ⟨a,rfl⟩))

/-- A standard actor preserving U takes each root torus element to a
unipotent multiple of a root torus element, even with a graph factor. -/
theorem actor_rootTorus_factor (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (h : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (a : Fˣ) : ∃ u ∈ unipotent F,
      projectiveActor F m σ ε (rootTorus F a) =
        u * rootTorus F (Units.map σ.toMonoidHom a) := by
  have hm := linear_part_unipotent F m σ ε h
  obtain ⟨u,hu,he⟩ := linearConjSL_torus_factor F m hm
    (Units.map σ.toMonoidHom a,(Units.map σ.toMonoidHom a)⁻¹)
  refine ⟨projection F u,mem_map_of_mem _ hu,?_⟩
  have ha : projectiveActor F m σ ε (rootTorus F a) =
      linearConj F m (rootTorus F (Units.map σ.toMonoidHom a)) := by
    cases ε <;> simp [projectiveActor, MulAut.mul_apply, graph_rootTorus, field_rootTorus]
  rw [ha,rootTorus_apply]
  change projection F (linearConjSL F m (torusSL F _)) = _
  rw [he,map_mul]
  rfl

/-- Centralizing the highest-root group forces the displacement into U.
The proof retains the actual projective matrix and hence its scalar kernel. -/
theorem displacement_mem_unipotent_of_standard
    (α : MulAut PSL(3,F)) (hα : α ∈ standard F)
    (hU : (unipotent F).map α.toMonoidHom = unipotent F)
    (a : Fˣ)
    (hc : α (rootTorus F a) * (rootTorus F a)⁻¹ ∈
      centralizer (projectiveCenter F : Set PSL(3,F))) :
    α (rootTorus F a) * (rootTorus F a)⁻¹ ∈ unipotent F := by
  obtain ⟨m,σ,h | h⟩ := ResidualLinear.standard_opposition_factorization α hα
  all_goals
    have hactor : ∃ ε, α = projectiveActor F m σ ε := by
      first
      | exact ⟨false, by simpa [projectiveActor] using h⟩
      | exact ⟨true,h⟩
    obtain ⟨ε,rfl⟩ := hactor
    obtain ⟨u,hu,he⟩ := actor_rootTorus_factor F m σ ε hU a
    have hc' : rootTorus F (Units.map σ.toMonoidHom a * a⁻¹) ∈
        centralizer (projectiveCenter F : Set PSL(3,F)) := by
      have hh := (centralizer (projectiveCenter F : Set PSL(3,F))).mul_mem
        ((centralizer _).inv_mem (unipotent_centralizes F hu)) hc
      simpa only [he, map_mul, map_inv, ← mul_assoc, inv_mul_cancel, one_mul] using hh
    have ha := rootTorus_eq_one_of_centralizes F _ hc'
    have hs : Units.map σ.toMonoidHom a = a := mul_inv_eq_one.mp ha
    simpa only [he,hs,mul_inv_cancel_right] using hu

theorem displacement_mem_unipotent {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (α : MulAut PSL(3,F))
    (hU : (unipotent F).map α.toMonoidHom = unipotent F)
    (a : Fˣ)
    (hc : α (rootTorus F a) * (rootTorus F a)⁻¹ ∈
      centralizer (projectiveCenter F : Set PSL(3,F))) :
    α (rootTorus F a) * (rootTorus F a)⁻¹ ∈ unipotent F := by
  have hcover := PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation F hn hF
    (PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F)
  exact displacement_mem_unipotent_of_standard F α (hcover.symm ▸ mem_top α) hU a hc

end Matrix.PSL3.CartanActions.RootTorusControl

namespace Matrix.PSL3.CartanActions.RootTorusControl
variable (F : Type*) [Field F] [Finite F]

theorem borel_core_eq {n : ℕ} (hF : Nat.card F = 2^n) :
    (borel F).pCoreIn 2 = unipotent F := by
  rw [pCoreIn, twoCore_eq F hF, map_subgroupOf_eq_of_le (unipotent_le_borel F)]

variable [CharP F 2]

/-- The actual quotient formula, with the cubic scalar subgroup retained. -/
theorem actor_rootTorus_quotient {n : ℕ} (hF : Nat.card F = 2^n)
    (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (a : Fˣ) (hb : projectiveActor F m σ ε (rootTorus F a) ∈ borel F) :
    quotientTorusEquiv F hF
      (QuotientGroup.mk (⟨projectiveActor F m σ ε (rootTorus F a),hb⟩ : borel F)) =
      QuotientGroup.mk (Units.map σ.toMonoidHom a,(Units.map σ.toMonoidHom a)⁻¹) := by
  obtain ⟨u,hu,he⟩ := actor_rootTorus_factor F m σ ε hU a
  have he' : (⟨projectiveActor F m σ ε (rootTorus F a),hb⟩ : borel F) =
      ⟨u,unipotent_le_borel F hu⟩ *
        ⟨rootTorus F (Units.map σ.toMonoidHom a),rootTorus_le_borel F ⟨_,rfl⟩⟩ :=
    Subtype.ext he
  have hu' : (QuotientGroup.mk (⟨u,unipotent_le_borel F hu⟩ : borel F) :
      borel F ⧸ pCore 2 (borel F)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [twoCore_eq F hF]
    exact hu
  rw [he',QuotientGroup.mk_mul,hu',one_mul]
  exact quotientTorusEquiv_mk_torus F hF _

end Matrix.PSL3.CartanActions.RootTorusControl
