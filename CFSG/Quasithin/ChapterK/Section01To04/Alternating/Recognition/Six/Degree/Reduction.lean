module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Inputs
public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension
public import Theory.Representation.BinaryOffender.CubicConjugateBound

/-!
# The ambient A₆ degree estimate from elementary-actor generation

The cubic-ratio bound supplies an actual elementary subgroup A of G with
fixed codimension at most twice its binary rank. If n conjugates of A generate
over the component and n times its rank is at most six, the fixed-space
intersection estimate gives degree at most twelve. No restriction of the
cubic-ratio bound to the component is made.

The remaining group input is isolated below: generation in a finite group
whose actual generalized Fitting subgroup is A₆. It has no representation or
dimension hypothesis. Its proof, and the independent G.5.1 degree gap, are
still required for the unconditional degree-four theorem.

Source: Aschbacher–Smith K.1–K.1.1, printed p.452 (PDF p.463), invoking
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction
universe u v

/-- The finite group calculation needed for the cubic degree bound. All
conjugates are taken in the actual ambient group, including outer actors. -/
def ActorGeneration : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (L : Subgroup G),
    L = generalizedFitting G → (L ≃* alternatingGroup (Fin 6)) →
      ∀ A : Subgroup G, IsElementaryTwo A →
        ∃ (n : ℕ) (g : Fin n → G), n * rank A ≤ 6 ∧
          L ≤ ⨆ i, A.map (MulAut.conj (g i)).toMonoidHom

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}

/-- The original Chapter K input has degree at most twelve once the pure
group generation calculation is supplied. -/
theorem finrank_le_twelve_of_actorGeneration (hgen : ActorGeneration.{u})
    (h : Input ρ K L) (e : L ≃* alternatingGroup (Fin 6)) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_bound
  obtain ⟨n, g, hn, hg⟩ := hgen L h.fitting e A hA
  let : IsSimpleGroup (L ⧸ center L) := h.quasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hd := finrank_le_card_mul_fixedCodim_of_subgroup_conjugates ρ L A
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible) g hg
  simp only [Fintype.card_fin] at hd
  calc
    Module.finrank (ZMod 2) V ≤ n * fixedCodim ρ A := hd
    _ ≤ n * (2 * rank A) := Nat.mul_le_mul_left n hsmall
    _ = 2 * (n * rank A) := by ac_rfl
    _ ≤ 12 := by omega

end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction
