module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ThirdSpaceCoordinates
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Source

/-!
# The original line centralizer acts as the full A₄ Borel

The module action sends C_L(V₁) onto the point stabilizer of the fifth
coordinate. Its two-residual has the same image because A₄ is generated
by elements of odd order. All maps below have the literal source residual
as domain; they apply to the marking constructed from the original flag.

Source: Aschbacher–Smith, 13.5.7(b), 13.5.14.
-/
@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.ThirdSpace
open Subgroup Section06.CentralizerReduction Section06.TerminalContradiction.Ratio
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open A5Module BinaryPermutation.AlternatingFiveFlag
variable {G : Type*} [Group G] {L V V₁ : Subgroup G}
    (s : Marking L V) (hz : (zpowers (Multiplicative.ofAdd z)).map s.map=V₁)

include hz in
private theorem center_line_iff (l : L) :
    (l : G) ∈ centralizer (V₁ : Set G) ↔ (s.action l).val 4=4 := by
  have hze : zpowers (markedZ s)=V₁ := by simpa only [MonoidHom.map_zpowers,markedZ] using hz
  have he : (l : G) ∈ centralizer (V₁ : Set G) ↔
      MulAut.conj (l : G) (markedZ s)=markedZ s := by
    constructor
    · intro hc
      have hh := (mem_centralizer_iff.mp hc) (markedZ s) (hze ▸ mem_zpowers _)
      exact mul_inv_eq_iff_eq_mul.mpr hh.symm
    · intro hc
      have hh : markedZ s ∈ centralizer ({(l : G)} : Set G) :=
        mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc).symm
      have hh' : V₁ ≤ centralizer ({(l : G)} : Set G) := hze ▸ zpowers_le.mpr hh
      intro x hx
      exact (mem_centralizer_singleton_iff.mp (hh' hx))
  rw [he]
  have heq := s.equivariant l z
  change MulAut.conj (l : G) (markedZ s)=s.map (Multiplicative.ofAdd (rho (s.action l).val z)) at heq
  rw [heq]
  change s.map (Multiplicative.ofAdd (rho (s.action l).val z))=s.map (Multiplicative.ofAdd z) ↔ _
  rw [s.injective.eq_iff]
  exact fixes_z_iff _

def centralizerAction : (L ⊓ centralizer (V₁ : Set G) : Subgroup G) →*
    AlternatingFiveBorel.B :=
  (s.action.comp (inclusion inf_le_left)).codRestrict _ (by
    intro l
    exact (center_line_iff s hz (inclusion inf_le_left l)).mp l.property.2)

theorem centralizerAction_surjective : Function.Surjective (centralizerAction s hz) := by
  intro g
  obtain ⟨l,hl⟩ := s.onto g.val
  have hc : (l : G) ∈ centralizer (V₁ : Set G) :=
    (center_line_iff s hz l).mpr (hl ▸ g.property)
  exact ⟨⟨l,l.property,hc⟩,Subtype.ext hl⟩

theorem residual_le_centralizer : residualCentralizer L V₁ ≤ L ⊓ centralizer (V₁ : Set G) :=
  map_subtype_le _

noncomputable def residualAction : residualCentralizer L V₁ →* AlternatingFiveBorel.B :=
  (centralizerAction s hz).comp (inclusion (residual_le_centralizer (L:=L) (V₁:=V₁)))

@[simp] theorem residualAction_val (l : residualCentralizer L V₁) :
    (residualAction s hz l).val = s.action ⟨l,(residual_le_centralizer l.property).1⟩ := rfl

theorem residualAction_surjective [Finite G] : Function.Surjective (residualAction s hz) := by
  intro g
  have hm : g ∈ (pResidual 2 (L ⊓ centralizer (V₁ : Set G) : Subgroup G)).map
      (centralizerAction s hz) := by
    rw [map_pResidual_of_surjective 2 _ (centralizerAction_surjective s hz),borel_twoResidual]
    exact mem_top _
  obtain ⟨c,hc,he⟩ := hm
  exact ⟨⟨c,⟨c,hc,rfl⟩⟩,he⟩

theorem equivariant (l : residualCentralizer L V₁) (x : Space) :
    MulAut.conj (l : G) (s.map (Multiplicative.ofAdd x)) =
      s.map (Multiplicative.ofAdd (rho (residualAction s hz l).val.val x)) :=
  s.equivariant ⟨l,(residual_le_centralizer l.property).1⟩ x

end CFSG.Quasithin.Chapter13.Section05.A5Source.ThirdSpace
