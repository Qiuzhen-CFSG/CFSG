module

public import Theory.Representation.BinaryOffender.InvolutionFixedKernel
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.LocalData

/-!
# The equality case of the Tits displacement estimate

The five-local weight calculations give displacement at least ten for every
involution and at least twelve for the distinguished five-inverter. If an
elementary actor of rank at most five had codimension at most twice its rank,
its fixed space would equal that of any nonidentity element. The actor then
lies in the elementary normal kernel on this fixed space. That kernel avoids
the five-inverter class, so the finite centralizer calculation bounds its
order by sixteen, a contradiction.

The local group geometry and the two five-weight estimates remain explicit
inputs. This proves their implication for the literal Parrott action; it
does not claim the source exclusion before those inputs are constructed.
Source: GM04, Lemmas 2.3 and 8.8, internal pp.6 and 57.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem codim_mono (ρ : Representation (ZMod 2) G V)
    {A B : Subgroup G} (h : A ≤ B) : fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hi : fixedSpace ρ B ≤ fixedSpace ρ A := fun _ hv a => hv ⟨a, h a.property⟩
  have hdim := Submodule.finrank_mono hi
  have ha := fixedCodim_add_finrank ρ A
  have hb := fixedCodim_add_finrank ρ B
  omega

private theorem conjugate_codim (ρ : Representation (ZMod 2) G V)
    {a b : G} (h : IsConj a b) :
    fixedCodim ρ (zpowers a) = fixedCodim ρ (zpowers b) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (fixedCodim_zpowers_conj ρ a g).symm

/-- The two concrete five-weight estimates suffice on the original group.
Neither irreducibility nor cubicity is needed for this internal calculation. -/
theorem internal_displacement_of_local_calculations
    (d : LocalGeometry) (σ : Representation (ZMod 2) Tits.ParrottGroup V)
    (hf : Function.Injective σ)
    (hfive : ∀ k ∈ Tits.fiveKernel, k ≠ 1 → 20 ≤ fixedCodim σ (zpowers k))
    (hinverter : 12 ≤ fixedCodim σ (zpowers fiveInverter))
    (A : Subgroup Tits.ParrottGroup) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim σ A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hten (t : Tits.ParrottGroup) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
      10 ≤ fixedCodim σ (zpowers t) := by
    obtain ⟨x, k, hk, hk1, hc⟩ := d.five_commutator t ht ht2
    have h := hfive k hk hk1
    rw [conjugate_codim σ hc] at h
    have hb := fixedCodim_commutator_le_twice σ t x
    omega
  have hcard := (primeRank_le_iff_elementary_card_le Tits.ParrottGroup).mp
    d.elementary_rank A hA.2
  have hrank : rank A ≤ 5 := by
    have hh := Nat.log_mono_right (b := 2) hcard
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  by_contra! hbad
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hlow := hten t ht1 ht2
  have hle := codim_mono σ (zpowers_le.mpr ht)
  have hcodim : fixedCodim σ (zpowers t) = 10 := by omega
  have hfix : fixedSpace σ A = fixedSpace σ (zpowers t) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact fun _ hv a => hv ⟨a, (zpowers_le.mpr ht) a.property⟩
    · have h₁ := fixedCodim_add_finrank σ A
      have h₂ := fixedCodim_add_finrank σ (zpowers t)
      omega
  let K := involutionFixedKernel σ t
  have hAK : A ≤ K := by
    intro a ha
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨t, ht⟩)
    · intro v hv
      exact (hfix.symm ▸ hv) ⟨a, ha⟩
  have hK : Nat.card K ≤ 16 := by
    apply d.normal_elementary t ht1 ht2 K (subspaceKernel_le σ _ _)
      (involutionFixedKernel_elementary σ hf t ht2) (involutionFixedKernel_normal σ t)
    intro k hk hc
    have hi : fixedSpace σ (zpowers t) ≤ fixedSpace σ (zpowers k) := by
      intro v hv
      exact (mem_fixedSpace_zpowers_iff σ k v).mpr (hk.2 v hv)
    have hd := Submodule.finrank_mono hi
    have h₁ := fixedCodim_add_finrank σ (zpowers t)
    have h₂ := fixedCodim_add_finrank σ (zpowers k)
    have hhigh := hinverter
    rw [conjugate_codim σ hc] at hhigh
    omega
  have hsmall : rank A ≤ 4 := by
    have hh := Nat.log_mono_right (b := 2)
      ((Nat.card_le_card_of_injective (Subgroup.inclusion hAK)
        (Subgroup.inclusion_injective hAK)).trans hK)
    norm_num [rank] at hh ⊢
    exact hh
  omega

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
