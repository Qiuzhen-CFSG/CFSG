module

public import Theory.SpecificGroups.FifteenPointSubgroups.AlternatingSeven
public import Theory.SpecificGroups.Alternating.SevenThreeSection
public import Theory.GroupAction.TwoTransitiveFactorization

/-!
# Small suborbits and the fifteen-point action of A₇

Let B be an actual subgroup of A₇ isomorphic to PSL₃(2). A B-fixed point
in any A₇-set is globally fixed if every B-orbit has fewer than fourteen
points. Otherwise its stabilizer is B, its A₇-orbit has fifteen points,
and two-transitivity makes the other fourteen points a single B-orbit.

For an action on a finite group W, a common displacement subgroup of
order at most eight bounds every B-orbit by eight. This formulation uses
the supplied action and subgroup, without assuming faithfulness or a
particular representation dimension.

Source: the fifteen-point action in Aschbacher--Smith B.4.12(2), printed
p.97, applied to the actual invariant section in the setting of 15.3.23.
-/

public noncomputable section
open Subgroup MulAction
open scoped MatrixGroups
namespace Theory.GroupAction

/-- A PSL₃(2)-fixed point is A₇-fixed when all PSL₃(2)-suborbits are small. -/
theorem alternatingSeven_fixed_of_small_suborbits
    {Ω : Type*} [Finite Ω] [MulAction (alternatingGroup (Fin 7)) Ω]
    (B : Subgroup (alternatingGroup (Fin 7))) (e : B ≃* PSL(3,ZMod 2))
    (hsmall : ∀ y : Ω, Nat.card (orbit B y) < 14)
    (x : Ω) (hfix : ∀ b : B, b • x = x) :
    ∀ g : alternatingGroup (Fin 7), g • x = x := by
  intro g
  by_contra hg
  have hB : Nat.card B = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hBS : B ≤ stabilizer (alternatingGroup (Fin 7)) x :=
    fun b hb => hfix ⟨b,hb⟩
  have hs : stabilizer (alternatingGroup (Fin 7)) x = B :=
    alternatingGroup.SevenThreeSection.eq_of_le_of_card B _ hB hBS (by
      intro ht
      exact hg (show g ∈ stabilizer (alternatingGroup (Fin 7)) x from ht ▸ mem_top g))
  have hi : B.index = 15 := by
    have hh := B.card_mul_index
    rw [hB,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hc : Nat.card (orbit (alternatingGroup (Fin 7)) x) = 15 := by
    change (orbit (alternatingGroup (Fin 7)) x).ncard = 15
    rw [←index_stabilizer,hs,hi]
  have hgB : g ∉ B := fun hh => hg (hfix ⟨g,hh⟩)
  have hxnot : x ∉ orbit B (g • x) := by
    rintro ⟨b,hb⟩
    change b • (g • x) = x at hb
    apply hg
    calc
      g • x = b⁻¹ • (b • (g • x)) := (inv_smul_smul b (g • x)).symm
      _ = b⁻¹ • x := by rw [hb]
      _ = x := hfix b⁻¹
  have ho : orbit (alternatingGroup (Fin 7)) x = insert x (orbit B (g • x)) := by
    ext y
    constructor
    · rintro ⟨k,rfl⟩
      change k • x ∈ insert x (orbit B (g • x))
      by_cases hk : k ∈ B
      · rw [show k • x = x from hfix ⟨k,hk⟩]
        exact Set.mem_insert x _
      · obtain ⟨b,hb,c,hc,hbc⟩ := B.two_pretransitive_factorization
          (FifteenPointSubgroups.alternating7_two_pretransitive B ⟨e⟩) hgB hk
        apply Set.mem_insert_of_mem
        refine ⟨⟨b,hb⟩,?_⟩
        change b • (g • x) = k • x
        rw [←hbc,mul_smul,mul_smul,show c • x = x from hfix ⟨c,hc⟩]
    · rintro (hy | ⟨b,hb⟩)
      · rw [hy]
        exact mem_orbit_self x
      · exact ⟨(b : alternatingGroup (Fin 7))*g,(mul_smul _ _ _).trans hb⟩
  change (orbit (alternatingGroup (Fin 7)) x).ncard = 15 at hc
  rw [ho,Set.ncard_insert_of_notMem hxnot] at hc
  have hh := hsmall (g • x)
  change (orbit B (g • x)).ncard < 14 at hh
  omega

/-- Small common displacement forces every B-fixed group element to be A₇-fixed. -/
theorem alternatingSeven_fixed_of_displacement_card_le_eight
    {W : Type*} [Group W] [Finite W]
    (ρ : alternatingGroup (Fin 7) →* MulAut W)
    (B : Subgroup (alternatingGroup (Fin 7))) (e : B ≃* PSL(3,ZMod 2))
    (D : Subgroup W) (hD : Nat.card D ≤ 8)
    (hdisp : ∀ (b : B) (w : W), ρ b w * w⁻¹ ∈ D)
    (x : W) (hfix : ∀ b : B, ρ b x = x) :
    ∀ g : alternatingGroup (Fin 7), ρ g x = x := by
  let : MulAction (alternatingGroup (Fin 7)) W := MulAction.compHom W ρ
  apply alternatingSeven_fixed_of_small_suborbits B e ?_ x hfix
  intro w
  let f : orbit B w → D := fun y => ⟨y.val*w⁻¹,by
    obtain ⟨b,hb⟩ := y.property
    rw [←hb]
    exact hdisp b w⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val he)
  have hh := (Nat.card_le_card_of_injective f hf).trans hD
  omega

end Theory.GroupAction
