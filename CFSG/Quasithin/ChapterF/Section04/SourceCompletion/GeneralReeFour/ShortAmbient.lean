module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortCentralizer
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Extremality

/-!
# Extremal rechoice in the same full Ree extension

Conjugation by a full endpoint element acts on the native carrier by its
actual automorphism. Native involution exhaustion and the centralizer
three-divisibility distinction preserve the short class. The entire
extension centralizer stays in the left endpoint, so native centralizer
placement puts the new representative in the same linear radical.

These are the transports for the extremal choice in F.4.40–42, printed
pp.294–295 (`refs/quasithin.pdf`). Ambient containment is not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {m : ℕ} (E : GeneralReeExtension.SourceExtension m)

theorem baseHom_conjugation (a : E.carrier) (t : Model m) :
    E.baseHom (a.val t) = a * E.baseHom t * a⁻¹ := by
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  change a.val t * x * (a.val t)⁻¹ = a.val (t * (a.val⁻¹ x) * t⁻¹)
  simp only [map_mul,map_inv,MulAut.apply_inv_self]

/-- Conjugating in the full left endpoint preserves the native short marker,
its radical placement, and containment of the entire extension centralizer. -/
theorem extension_short_conjugate (hm : 0 < m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    {t : Model m} (ht : IsShortRootInvolution t)
    (hC : centralizer ({E.baseHom t} : Set E.carrier) ≤ E.left.subgroupOf E.carrier)
    (a : E.carrier) (ha : a ∈ E.left.subgroupOf E.carrier) :
    IsShortRootInvolution (a.val t) ∧ a.val t ∈ radical m .linear ∧
      centralizer ({E.baseHom (a.val t)} : Set E.carrier) ≤ E.left.subgroupOf E.carrier := by
  have ht' := ReeF4.SourceCompletion.ShortCentralizerGeometry.automorphism_preserves_short
    hm hexhaust a.val ht
  have hC' : centralizer ({E.baseHom (a.val t)} : Set E.carrier) ≤
      E.left.subgroupOf E.carrier := by
    rw [baseHom_conjugation E a t,←MulAut.conj_apply,
      ←CentralizerSmallKernelTransport.map_centralizer]
    rintro _ ⟨x,hx,rfl⟩
    exact (E.left.subgroupOf E.carrier).mul_mem
      ((E.left.subgroupOf E.carrier).mul_mem ha (hC hx))
      ((E.left.subgroupOf E.carrier).inv_mem ha)
  have hn : centralizer ({a.val t} : Set (Model m)) ≤ parabolic m .linear := by
    intro x hx
    apply (E.baseHom_mem_family_iff (ReeF4.SmallCompletion.conj_injective m hm) false x).mp
    apply hC'
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute x (a.val t) from mem_centralizer_singleton_iff.mp hx).map E.baseHom).eq
  exact ⟨ht',ReeF4.SourceCompletion.short_mem_radical_of_centralizer_le hm ht' hn,hC'⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient
