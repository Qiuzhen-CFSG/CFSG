module
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Centralizer

/-!
# The full relative-normalizer commutator bound

The actual natural A₆ coordinates extend to M_V=N_M(V), since this group
normalizes both L and V. Its action preserves the symplectic form. Fixing
V₃=V₁-perpendicular therefore forces displacement of V into V₁. This
strengthens the earlier LT-only calculation to the full source actor.
The last lemma transports plane noncentrality through the original flag.
Source: Aschbacher–Smith, 13.5.4(4–5), printed p.916.
-/

@[expose] public noncomputable section
open Subgroup BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.AmbientSource
open Section08.SourceCompletion Section07.NaturalAction
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

include d
/-- The full relative normalizer, not merely LT, preserves the source
symplectic form. A pointwise fixer of V₃ therefore moves V into V₁. -/
theorem local_seed_centralizer_displacement :
    ⁅V, (M ⊓ normalizer (V : Set G)) ⊓ centralizer (U : Set G)⁆ ≤ P := by
  let := d.chosen.elementary
  let B := M ⊓ normalizer (V : Set G)
  have hLB : L ≤ B := le_inf (by rw [d.local_normalizer]; exact L.le_normalizer)
    (le_sup_left.trans d.normalizes_V)
  have hBL : B ≤ normalizer (L : Set G) := by rw [← d.local_normalizer]; exact inf_le_left
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)
  have hα : Function.Surjective α :=
    d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f,_,hf,_⟩ := natural_extension B L V hLB hBL inf_le_right α hα
    (linearCoordinate d) (fun l v => d.conjugation l v.toMul)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg v hv
  let x : B := ⟨g,hg.1⟩
  let w : V := ⟨v,hv⟩
  let c := V.normalizerMonoidHom ⟨g,hg.1.2⟩ w * w⁻¹
  have hfix : ∀ y ∈ image d U, naturalRepresentation (Fin 6) (f x) y = y := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := (mem_image d U _).mp hy
    have he := hf x (Additive.ofMul a)
    change (d.coordinate (V.normalizerMonoidHom ⟨g,hg.1.2⟩ a)).toAdd =
      naturalRepresentation (Fin 6) (f x) (d.coordinate a).toAdd at he
    rw [← he]
    apply congrArg (fun b : V => (d.coordinate b).toAdd)
    apply Subtype.ext
    change g * a.val * g⁻¹ = a.val
    rw [← mem_centralizer_iff.mp hg.2 a.val ha,mul_inv_cancel_right]
  have hc : (d.coordinate c).toAdd ∈ image d P := by
    have horth : (d.coordinate c).toAdd ∈ form.orthogonal (image d U) := by
      intro y hy
      have hp := form_invariant (f x) y (d.coordinate w).toAdd
      rw [hfix y hy] at hp
      change form y (d.coordinate c).toAdd = 0
      have he := hf x (Additive.ofMul w)
      change (d.coordinate (V.normalizerMonoidHom ⟨g,hg.1.2⟩ w)).toAdd =
        naturalRepresentation (Fin 6) (f x) (d.coordinate w).toAdd at he
      change form y (d.coordinate (V.normalizerMonoidHom _ w * w⁻¹)).toAdd = 0
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,← sub_eq_add_neg,he,map_sub,hp,sub_self]
    rwa [seed_perpendicular d,LinearMap.BilinForm.orthogonal_orthogonal
      form_nondegenerate form_alt.isRefl] at horth
  obtain ⟨a,ha,he⟩ := (mem_image d P _).mp hc
  have he' : a = c := d.coordinate.injective he
  have hcv : c.val ∈ P := he' ▸ ha
  exact hcv

/-- The final commutator clause of 13.5.4(4), once its ambient containment
has been supplied by the preceding source theorem. -/
theorem source_seed_centralizer_displacement
    (hc : centralizer (U : Set G) ≤ M ⊓ normalizer (V : Set G)) :
    ⁅V, centralizer (U : Set G)⁆ ≤ P := by
  have he : (M ⊓ normalizer (V : Set G)) ⊓ centralizer (U : Set G) =
      centralizer (U : Set G) := inf_eq_right.mpr hc
  simpa only [he] using local_seed_centralizer_displacement d

/-- Source 13.5.4(5) implies the exact seed noncentrality used in 13.5.12,
with the original ambient two-core and flag retained. -/
theorem source_seed_noncentral_of_plane_noncentral
    (hm : ⁅(normalizer (P : Set G)).pCoreIn 2, E⁆ ≠ ⊥) :
    ⁅U, H.pCoreIn 2⁆ ≠ ⊥ := by
  intro hz
  apply hm
  apply le_bot_iff.mp
  rw [d.first_normalizer,commutator_comm] at hz
  exact (commutator_mono le_rfl d.plane_le_seed).trans hz.le

end CFSG.Quasithin.Chapter13.Section05.AmbientSource
