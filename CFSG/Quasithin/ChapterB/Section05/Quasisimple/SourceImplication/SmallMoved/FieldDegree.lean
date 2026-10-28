module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions.Displacement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.G2

/-!
# The original plane bound limits the defining field to F₂ or F₄

A nontrivial element of the actual offender acts nontrivially on the faithful
central quotient. Its displacement is linear over the model's defining field,
so restriction of scalars gives binary rank at least the field degree. That
range lies in the offender's whole moved space, of dimension at most two.
This handles the linear and symplectic field rows of 13.7.15(1).
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved

private theorem field_degree_le_displacement (F : BinaryField)
    {D W : Type*} [Group D] [AddCommGroup W]
    [Module F.Carrier W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F.Carrier W]
    [FiniteDimensional F.Carrier W]
    (τ : Representation F.Carrier D W) (a : D) (hne : τ a ≠ 1) :
    F.degree ≤ Module.finrank (ZMod 2)
      (LinearMap.range ((restrictScalars (k := ZMod 2) τ) a - LinearMap.id)) := by
  have hd : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq] at h
    exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm
  let T := τ a - 1
  have hn : LinearMap.range T ≠ ⊥ := by
    intro he
    exact hne (sub_eq_zero.mp (LinearMap.range_eq_bot.mp he))
  have hp : 0 < Module.finrank F.Carrier (LinearMap.range T) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hn)
  have he : (restrictScalars (k := ZMod 2) τ) a - LinearMap.id =
      T.restrictScalars (ZMod 2) := rfl
  rw [he,LinearMap.range_restrictScalars]
  change F.degree ≤ Module.finrank (ZMod 2) (LinearMap.range T)
  rw [← Module.finrank_mul_finrank (ZMod 2) F.Carrier,hd]
  exact Nat.le_mul_of_pos_right _ hp

/-- A faithful model containing a nontrivial plane-bounded actor has field degree at most two. -/
theorem model_field_degree_le_two (F : BinaryField)
    {G D V W : Type*} [Group G] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module F.Carrier W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) F.Carrier W] [FiniteDimensional F.Carrier W]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {A H : Subgroup G} (hne : A ≠ ⊥) (hAH : A ≤ H)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (τ : Representation F.Carrier D W)
    (e : ActionEquiv (ρ.comp H.subtype) (restrictScalars (k := ZMod 2) τ)) :
    F.degree ≤ 2 := by
  let : FiniteDimensional (ZMod 2) W := Module.Finite.equiv e.linearEquiv
  obtain ⟨a,ha,han⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hane : a ≠ 1 := fun he => han (Subgroup.mem_bot.mpr he)
  let aH : H := ⟨a,hAH ha⟩
  have hτ : τ (e.groupEquiv aH) ≠ 1 := by
    intro he
    apply hane
    apply hf
    apply LinearMap.ext
    intro v
    apply e.linearEquiv.injective
    have hi := e.intertwines aH v
    change e.linearEquiv (ρ a v) = τ (e.groupEquiv aH) (e.linearEquiv v) at hi
    simpa only [he,Module.End.one_apply,map_one] using hi
  have hr := field_degree_le_displacement F τ (e.groupEquiv aH) hτ
  rw [← e.displacement_rank aH] at hr
  have hle : LinearMap.range (ρ a - LinearMap.id) ≤ moved ρ A := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩
  exact hr.trans ((Submodule.finrank_mono hle).trans hd)

/-- The bound applies to the literal original quotient action and offender. -/
theorem quotient_field_degree_le_two (F : BinaryField)
    {G D V W : Type*} [Group G] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module F.Carrier W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) F.Carrier W] [FiniteDimensional F.Carrier W]
    (ρ : Representation (ZMod 2) G V) {A L H : Subgroup G}
    (hne : A ≠ ⊥) (hAH : A ≤ H)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (s : MovedSection ρ L) (hf : Function.Injective s.central.quotientRepresentation)
    (τ : Representation F.Carrier D W)
    (e : ActionEquiv (s.central.quotientRepresentation.comp H.subtype)
      (restrictScalars (k := ZMod 2) τ)) : F.degree ≤ 2 := by
  exact model_field_degree_le_two F s.central.quotientRepresentation hf hne hAH
    ((moved_finrank_quotient_le s.space.toRepresentation s.central A).trans
      ((moved_finrank_subrepresentation_le ρ s.space A).trans hd)) τ e

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
