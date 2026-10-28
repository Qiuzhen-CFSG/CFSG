module

public import CFSG.Quasithin.ChapterK.Section01To04.Preliminaries
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The literal root-intersection obstruction in K.4.5

An ambient root group centralizing the involution centralizer meets the
embedded J₂ subgroup in its central involution group. If a rank-two actor
had fixed codimension at most four, its fixed space would equal that of
one of its 2-central involutions. The actual ambient pointwise fixer then
places the actor in that cyclic root intersection, a contradiction.

These lemmas keep the injection, equivariant map, centralizers, and root
subgroup literal. The G₂ fixed-space theorem and J₂ local center calculation
are separate inputs; no assertion about hypothetical actor placement is
assumed. Source: Aschbacher–Smith, K.4.5, printed p.460.
-/

public section
namespace CFSG.Quasithin.ChapterK.JankoTwo
open Subgroup Representation Representation.BinaryOffender

variable {H M V U : Type*} [Group H] [Group M]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup U] [Module (ZMod 2) U]

/-- Pulling back a group that centralizes the ambient involution centralizer
lands in the center of the literal smaller centralizer. -/
theorem root_comap_le_centralizer_center (f : H →* M) (hf : Function.Injective f)
    (z : H) (R : Subgroup M)
    (hR : R ≤ centralizer (centralizer ({f z} : Set M) : Set M)) :
    R.comap f ≤ (center (centralizer ({z} : Set H))).map
      (centralizer ({z} : Set H)).subtype := by
  intro x hx
  have hcomm (y : H) (hy : y ∈ centralizer ({z} : Set H)) : y * x = x * y := by
    apply hf
    simp only [map_mul]
    apply (mem_centralizer_iff.mp (hR hx))
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hy)
  have hxz : x ∈ centralizer ({z} : Set H) := by
    apply mem_centralizer_singleton_iff.mpr
    exact (hcomm z (mem_centralizer_singleton_iff.mpr rfl)).symm
  refine ⟨⟨x, hxz⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  exact Subtype.ext (hcomm y y.property)

/-- The source center identity forces the actual root intersection to be cyclic. -/
theorem root_comap_le_zpowers (f : H →* M) (hf : Function.Injective f)
    (z : H) (R : Subgroup M)
    (hR : R ≤ centralizer (centralizer ({f z} : Set M) : Set M))
    (hcenter : (center (centralizer ({z} : Set H))).map
      (centralizer ({z} : Set H)).subtype ≤ zpowers z) :
    R.comap f ≤ zpowers z :=
  (root_comap_le_centralizer_center f hf z R hR).trans hcenter

/-- If the root contains the marked involution, the literal intersection is
exactly its cyclic group. -/
theorem root_comap_eq_zpowers (f : H →* M) (hf : Function.Injective f)
    (z : H) (R : Subgroup M)
    (hR : R ≤ centralizer (centralizer ({f z} : Set M) : Set M))
    (hcenter : (center (centralizer ({z} : Set H))).map
      (centralizer ({z} : Set H)).subtype ≤ zpowers z) (hzR : f z ∈ R) :
    R.comap f = zpowers z :=
  le_antisymm (root_comap_le_zpowers f hf z R hR hcenter) (zpowers_le.mpr hzR)

/-- Equality of fixed spaces places the actor in the preimage of the actual
ambient pointwise fixer. -/
theorem actor_le_root_comap (ρ : Representation (ZMod 2) H V)
    (σ : Representation (ZMod 2) M U) (f : H →* M) (E : V ≃ₗ[ZMod 2] U)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (A : Subgroup H) (z : H) (R : Subgroup M)
    (hfix : fixedSpace ρ A = fixedSpace ρ (zpowers z))
    (hroot : subspaceKernel σ (fixedSpace σ (zpowers (f z))) ⊤ = R) :
    A ≤ R.comap f := by
  have hfixed := fixedSpace_map_equivariant ρ σ f E hE (zpowers z)
  rw [MonoidHom.map_zpowers] at hfixed
  intro a ha
  change f a ∈ R
  rw [← hroot]
  refine ⟨mem_top _, ?_⟩
  intro u hu
  rw [← hfixed] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  rw [← hfix] at hv
  exact (hE a v).symm.trans (congrArg E (hv ⟨a, ha⟩))

/-- The root-intersection step excludes a rank-two small actor containing
an involution of displacement four. -/
theorem rank_two_exclusion [Finite H] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (σ : Representation (ZMod 2) M U)
    (f : H →* M) (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] U)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (A : Subgroup H) (hA : rank A = 2) (z : H) (hzA : z ∈ A)
    (hz : orderOf z = 2) (hzdim : fixedCodim ρ (zpowers z) = 4)
    (R : Subgroup M)
    (hroot : subspaceKernel σ (fixedSpace σ (zpowers (f z))) ⊤ = R)
    (hR : R ≤ centralizer (centralizer ({f z} : Set M) : Set M))
    (hcenter : (center (centralizer ({z} : Set H))).map
      (centralizer ({z} : Set H)).subtype ≤ zpowers z) :
    2 * rank A < fixedCodim ρ A := by
  by_contra! hsmall
  have hzle : zpowers z ≤ A := zpowers_le.mpr hzA
  have hmono := ChapterE.fixedCodim_mono ρ hzle
  have hcodim : fixedCodim ρ A = fixedCodim ρ (zpowers z) := by omega
  have hfix := fixedSpace_eq_of_fixedCodim_eq ρ hzle hcodim
  have hle : A ≤ zpowers z :=
    (actor_le_root_comap ρ σ f E hE A z R hfix hroot).trans
      (root_comap_le_zpowers f hf z R hR hcenter)
  have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  rw [Nat.card_zpowers, hz] at hcard
  have hrank := Nat.log_mono_right hcard (b := 2)
  have ht : Nat.log 2 2 = 1 := by decide
  rw [ht] at hrank
  unfold rank at hA
  omega

end CFSG.Quasithin.ChapterK.JankoTwo
