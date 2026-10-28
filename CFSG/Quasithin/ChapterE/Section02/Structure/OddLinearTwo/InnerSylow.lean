module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.ElementaryPlacement
public import Theory.SpecificGroups.PSL2.DihedralNonsquare
/-!
# Non-involutory elements in the original odd component Sylows

The source centralizer geometry supplies eight-divisibility in the prime
row. The explicit order 168 supplies it at the prime-seven boundary.
The marked dihedral Sylow theorem then produces a non-involution in every
Sylow of the original component, independently of the chosen ambient Sylow.
Source: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
private theorem marked_sylow_nonsquare
    {X : Type*} [Group X] [Finite X]
    {F : Type*} [Field F] [Finite F]
    (e : X ≃* PSL2MatrixGroup F)
    (hodd : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h8 : 8 ∣ Nat.card X) (Q : Sylow 2 X) :
    ∃ s : X, s ∈ (Q : Subgroup X) ∧ s ^ 2 ≠ 1 := by
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have h8' : 8 ∣ Nat.card (PSL2MatrixGroup F) := by rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨s, hs, hs2⟩ := Theory.PSL2.exists_sylow_nonsquare_of_eight_dvd hodd h8' Q'
  refine ⟨e.symm s, ?_, ?_⟩
  · change s ∈ (Q : Subgroup X).map e.toMonoidHom at hs
    exact mem_map_equiv.mp hs
  · intro he
    apply hs2
    simpa only [map_pow, map_one, e.apply_symm_apply] using congrArg e he

/-- Every Sylow of the original prime-field component contains a non-involution. -/
theorem prime_linear_source_inner_sylow_nonsquare
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F) (Q : Sylow 2 K) :
    ∃ s : K, s ∈ (Q : Subgroup K) ∧ s ^ 2 ≠ 1 := by
  obtain ⟨S, _, _, _, _, _, h8⟩ := prime_linear_source_sylow_center T hP K hgen ho hF hp eK
  exact marked_sylow_nonsquare eK ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩
    (h8.trans (S : Subgroup K).card_subgroup_dvd_card) Q

/-- Every Sylow of an actual PSL₂(7) component contains a non-involution. -/
theorem prime_seven_inner_sylow_nonsquare
    {X : Type*} [Group X] [Finite X]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7)
    (e : X ≃* PSL2MatrixGroup F) (Q : Sylow 2 X) :
    ∃ s : X, s ∈ (Q : Subgroup X) ∧ s ^ 2 ≠ 1 := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by decide, by decide, by decide, by simpa using hF⟩
  have h8 : 8 ∣ Nat.card X := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F hodd, hF]
    norm_num
  exact marked_sylow_nonsquare e hodd h8 Q
end CFSG.Quasithin.ChapterE.Structure
