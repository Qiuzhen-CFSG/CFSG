module
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Split.Lifting
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Recognition
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Split.Exclusion

/-!
# Lifting the two outer involution orbits through the original cubic kernel

Every quotient involution has an involution lift, obtained by cubing a lift.
For involutions outside the centralizer image the lift inverts B. Conjugacy
by the marked M10 subgroup then lifts to conjugacy by the original C_G(B):
the remaining cubic displacement is removed by conjugation by its square.
These formulas retain the actual quotient and the ambient conjugating element.

Source: Aschbacher–Smith J.2.7(4,7), printed p.436 (PDF p.447).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

public theorem lift_normalizer_involution_source (x : c.NormalizerQuotient) (hx : orderOf x = 2) :
    ∃ y : c.NB, orderOf y = 2 ∧ c.normalizerQuotientMap y = x :=
  c.normalizer_involution_lift x hx

public theorem lift_outer_normalizer_involution_source (x : c.NormalizerQuotient)
    (hx : orderOf x = 2) (hxM : x ∉ c.centralizerImage) :
    ∃ y : c.NB, orderOf y = 2 ∧ c.normalizerQuotientMap y = x ∧ c.InvertsB (y : G) := by
  obtain ⟨y,hy,he⟩ := c.lift_normalizer_involution_source x hx
  refine ⟨y,hy,he,?_⟩
  rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one c.B
    (by rw [SourceCompletion.B_card c]; decide) (y:G)
    (congrArg Subtype.val (hy ▸ pow_orderOf_eq_one y)) y.property with hc | hi
  · exact (hxM (he ▸ mem_map_of_mem c.normalizerQuotientMap
      (show y ∈ c.GB.subgroupOf c.NB from fun b hb => (hc b hb).symm))).elim
  · exact hi

public theorem inverter_conjugacy_lift_source (u v : c.NB)
    (hu : c.InvertsB (u:G))
    (h : ∃ a ∈ c.centralizerImage,
      a * c.normalizerQuotientMap u * a⁻¹ = c.normalizerQuotientMap v) :
    ∃ g∈c.GB, g*(u:G)*g⁻¹=(v:G) := by
  obtain ⟨a,⟨g,hg,rfl⟩,he⟩ := h
  let w : c.NB := g*u*g⁻¹
  have hw : c.normalizerQuotientMap w = c.normalizerQuotientMap v := by
    simpa only [w,map_mul,map_inv] using he
  let b := v*w⁻¹
  have hb : (b:G)∈c.B := by
    have hk : b ∈ c.normalizerQuotientMap.ker := by
      change c.normalizerQuotientMap (v*w⁻¹)=1
      rw [map_mul,map_inv,hw,mul_inv_cancel]
    rw [c.normalizerQuotientMap_ker] at hk
    exact hk
  have hwi : c.InvertsB (w:G) := by
    intro x hx
    have hgx : Commute x (g:G) := hg x hx
    have hgxi : Commute x⁻¹ (g:G) := hg _ (c.B.inv_mem hx)
    change (g:G)*u*(g:G)⁻¹*x*((g:G)*u*(g:G)⁻¹)⁻¹=x⁻¹
    calc
      _ = (g:G)*((u:G)*((g:G)⁻¹*x*g)*(u:G)⁻¹)*(g:G)⁻¹ := by group
      _ = (g:G)*((u:G)*x*(u:G)⁻¹)*(g:G)⁻¹ := by
        rw [show (g:G)⁻¹*x*g=x from by simpa only [inv_inv] using hgx.symm.inv_left.mul_inv_cancel]
      _ = (g:G)*x⁻¹*(g:G)⁻¹ := by rw [hu x hx]
      _ = x⁻¹ := hgxi.symm.mul_inv_cancel
  refine ⟨(b:G)^2*g,c.GB.mul_mem
    (c.GB.pow_mem ((c.B_le_GB_of_card (SourceCompletion.B_card c)) hb) 2) hg,?_⟩
  calc
    _ = (b:G)^2*(w:G)*((b:G)^2)⁻¹ := by dsimp [w]; group
    _ = (b:G)*(w:G) := c.cubic_conjugate_inverter (w:G) hwi (b:G) hb
    _ = (v:G) := by dsimp [b]; simp

public theorem inverter_model_conjugacy_lift_source
    (e : c.NormalizerQuotient ≃* AlternatingSix.ShadowLocal.AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (u v : c.NB) (hu : c.InvertsB (u:G))
    (h : ∃ a∈AlternatingSix.M10.extension,
      a*e (c.normalizerQuotientMap u)*a⁻¹=e (c.normalizerQuotientMap v)) :
    ∃ g∈c.GB, g*(u:G)*g⁻¹=(v:G) := by
  apply c.inverter_conjugacy_lift_source u v hu
  obtain ⟨a,ha,he⟩ := h
  rw [←hM] at ha
  obtain ⟨a,ha,rfl⟩ := ha
  change e a * e (c.normalizerQuotientMap u) * (e a)⁻¹ = e (c.normalizerQuotientMap v) at he
  exact ⟨a,ha,e.injective (by simpa only [map_mul,map_inv] using he)⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
