module
public import Glauberman.PushingUpOmegaAction
public import Glauberman.PushingUpNaturalActionImage
public import Theory.Representation.SL2FourQuadraticRecognition.Consequences
/-!
# Natural coordinates on the original omega action

Natural coordinates on the original global-fixed quotient give the uniform
fixed-index lower bound four for all subgroups of S outside O₂(H). Every
supplement L of O₂(H) has fixed index sixteen, and its actual moved subgroup
[V,L] has the same ambient centralizer as V. Generating conjugate Sylows
then produce the literal conjugate actor required by Niles7.6.

The independent inputs are the actual centralizer quotient marking and
its natural fixed-quotient coordinates. All original group transport and
source7.4/7.6 index and centralizer conclusions are proved here, retaining
arbitrary global fixed attachments and the original PSL₂(4) quotient kernel.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas2.9 and7.4–7.6,
printed pp.33,60–62.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL2FourQuadraticRecognition
open scoped IsMulCommutative
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- The actual natural quotient forces the uniform source lower bound for
all subgroups of S outside O₂(H), not just the maximum abelian subgroups. -/
theorem original_omega_fixedIndex_lower_of_natural_quotient
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (q : H →* SL2FourNatural.SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H))
    (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤)
      ≃ₗ[ZMod 2] SL2FourNatural.V)
    (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) =
      specialLinearNatural 2 (q h) (E v))
    (A : Subgroup H) (hAS : A ≤ (S : Subgroup H)) (hAQ : ¬ A ≤ pCore 2 H) :
    4 ≤ (omegaCenterIn (pCore 2 H) ⊓ centralizer (A : Set H)).relIndex
      (omegaCenterIn (pCore 2 H)) := by
  have hCQ := original_omega_sylow_centralizer_eq hF S hu K e q hq hk
  have hA := image_ne_bot_of_outside_sylow_centralizer hCQ q hk hAS hAQ
  have hd := fixedCodim_lower_of_natural_quotient (omegaAction H) q E hE A hA
  rw [omegaAction_fixed_index]
  exact (show 2 ^ 2 ≤ 2 ^ fixedCodim (omegaAction H) A from
    Nat.pow_le_pow_right (by decide) hd)

/-- The actual supplement actor has fixed index16 and the same moved-group
centralizer as the original omega layer, retaining every fixed attachment. -/
theorem original_omega_supplement_natural_data
    (q : H →* SL2FourNatural.SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H))
    (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤)
      ≃ₗ[ZMod 2] SL2FourNatural.V)
    (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) =
      specialLinearNatural 2 (q h) (E v))
    (L : Subgroup H) (hLQ : L ⊔ pCore 2 H = ⊤) :
    (omegaCenterIn (pCore 2 H) ⊓ centralizer (L : Set H)).relIndex
        (omegaCenterIn (pCore 2 H)) = 16 ∧
      centralizer ((⁅omegaCenterIn (pCore 2 H),L⁆ : Subgroup H) : Set H) =
        centralizer (omegaCenterIn (pCore 2 H) : Set H) := by
  have hQC : pCore 2 H ≤ centralizer (omegaCenterIn (pCore 2 H) : Set H) :=
    le_centralizer_iff.mp (fun _ hv => ((mem_omegaCenterIn_iff _ _).mp hv).2.1)
  have hL := image_eq_top_of_centralizing_supplement (pCore 2 H)
    (omegaCenterIn (pCore 2 H)) L hQC q hq hk hLQ
  have hkρ : q.ker ≤ (omegaAction H).ker := by rw [omegaAction_kernel]; exact hk.le
  constructor
  · rw [omegaAction_fixed_index,
      fixedCodim_eq_four_of_natural_quotient (omegaAction H) q hkρ E L hL]
    norm_num
  · ext h
    rw [omegaAction_moved_centralizer,
      fixes_moved_iff_of_natural_quotient (omegaAction H) q hkρ E hE L hL,
      omegaAction_kernel]

/-- The literal actor required by source7.6, constructed from the selected
abelian supplement and its generating conjugate. -/
theorem original_exists_natural_conjugate_actor
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (q : H →* SL2FourNatural.SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (omegaCenterIn (pCore 2 H) : Set H))
    (E : (Additive (omegaCenterIn (pCore 2 H)) ⧸ fixedSpace (omegaAction H) ⊤)
      ≃ₗ[ZMod 2] SL2FourNatural.V)
    (hE : ∀ h v, E (fixedQuotient (omegaAction H) ⊤ h v) =
      specialLinearNatural 2 (q h) (E v))
    (A : Subgroup H) (hAQ : A ⊔ pCore 2 H = (S : Subgroup H)) :
    ∃ g : H, let L := A ⊔ A.map (MulAut.conj g).toMonoidHom
      L ⊔ pCore 2 H = ⊤ ∧
      16 ≤ (centralizer (L : Set H)).relIndex (omegaCenterIn (pCore 2 H)) ∧
      (S : Subgroup H) ⊓
        centralizer ((⁅omegaCenterIn (pCore 2 H),L⁆ : Subgroup H) : Set H) = pCore 2 H := by
  obtain ⟨g,hg⟩ := original_exists_conjugate_abelian_supplement_generating hF S hu K e A hAQ
  obtain ⟨hi,hC⟩ := original_omega_supplement_natural_data q hq hk E hE _ hg
  refine ⟨g,hg,?_,?_⟩
  · rw [inf_relIndex_left] at hi
    exact hi.ge
  · rw [hC]
    exact original_omega_sylow_centralizer_eq hF S hu K e q hq hk
end Glauberman
