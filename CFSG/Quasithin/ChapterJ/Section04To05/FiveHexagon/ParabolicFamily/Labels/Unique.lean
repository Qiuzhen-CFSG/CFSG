module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Colors.Source
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.NoSameColor

/-!
# The unique colored parabolic containing an original five

Conjugate one color member back to the original endpoint. The common
central label puts the other conjugator in H. Their common subgroup of
order five then gives the same literal quotient pentagon, so the two
original parabolics agree. This does not identify different five lifts.
Source: the parabolic incidence argument of J.4.10, printed p.444.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)
  (c : Choices d) (e : first ≃* p.F₁ B5)
include s hi

/-- A literal five belongs to at most one parabolic of a specified color. -/
theorem color_members_eq_of_five {v : G} {E F B : Subgroup G}
    (hE : E ∈ colorFamily p B5 c.z (sourceU e) v)
    (hF : F ∈ colorFamily p B5 c.z (sourceU e) v)
    (hB : Nat.card B=5) (hBE : B≤E) (hBF : B≤F) : E=F := by
  obtain ⟨g,rfl,hg,_⟩ := hE
  obtain ⟨h,rfl,hh,_⟩ := hF
  have hk : g⁻¹*h ∈ d.toTypeRuSetup.H := by
    rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (g⁻¹*h)*c.z*(g⁻¹*h)⁻¹ = g⁻¹*(h*c.z*h⁻¹)*g := by group
      _ = g⁻¹*(g*c.z*g⁻¹)*g := by rw [hh,hg]
      _ = c.z := by group
  let A := B.conjBy g⁻¹
  have hA : Nat.card A=5 :=
    (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hB
  have hA0 : A≤p.F₁ B5 := by
    have ht := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hBE
    change A≤((p.F₁ B5).conjBy g).conjBy g⁻¹ at ht
    rwa [conjBy_inv] at ht
  have hAk : A≤(p.F₁ B5).conjBy (g⁻¹*h) := by
    have ht := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hBF
    change A≤((p.F₁ B5).conjBy h).conjBy g⁻¹ at ht
    rwa [conjBy_conjBy] at ht
  let : IsCyclic A := isCyclic_of_prime_card hA
  have he := conjugate_parabolics_eq_of_commuting_fives p s B5 hi
    (p.F₁ B5) ((p.F₁ B5).conjBy (g⁻¹*h))
    ⟨1,conjBy_one _⟩ ⟨⟨g⁻¹*h,hk⟩,rfl⟩ A A hA0 hAk hA hA
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have ht := congrArg (fun H : Subgroup G => H.conjBy g) he
  simpa only [conjBy_conjBy,mul_inv_cancel_left] using ht

/-- Existence of a member containing a literal five is automatically unique. -/
theorem existsUnique_color_member {v : G} {B : Subgroup G} (hB : Nat.card B=5)
    (hex : ∃ E ∈ colorFamily p B5 c.z (sourceU e) v, B≤E) :
    ∃! E : Subgroup G, E ∈ colorFamily p B5 c.z (sourceU e) v ∧ B≤E := by
  obtain ⟨E,hE,hBE⟩ := hex
  exact ⟨E,⟨hE,hBE⟩,fun F hF => color_members_eq_of_five p s B5 hi c e hF.1 hE hB hF.2 hBE⟩

omit s hi in
/-- The canonical original member carrying an existing literal five label. -/
def fiveLabel (v : G) (B : Subgroup G)
    (hex : ∃ E ∈ colorFamily p B5 c.z (sourceU e) v, B≤E) : Subgroup G :=
  Classical.choose hex

omit s hi in
theorem fiveLabel_spec (v : G) (B : Subgroup G)
    (hex : ∃ E ∈ colorFamily p B5 c.z (sourceU e) v, B≤E) :
    fiveLabel p B5 c e v B hex ∈ colorFamily p B5 c.z (sourceU e) v ∧
      B≤fiveLabel p B5 c e v B hex := Classical.choose_spec hex

/-- The label is independent of the existence witness or the chosen member. -/
theorem fiveLabel_eq (v : G) (B : Subgroup G) (hB : Nat.card B=5)
    (hex : ∃ E ∈ colorFamily p B5 c.z (sourceU e) v, B≤E)
    (E : Subgroup G) (hE : E ∈ colorFamily p B5 c.z (sourceU e) v) (hBE : B≤E) :
    fiveLabel p B5 c e v B hex=E := by
  obtain ⟨hF,hBF⟩ := fiveLabel_spec p B5 c e v B hex
  exact color_members_eq_of_five p s B5 hi c e hF hE hB hBF hBE

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
