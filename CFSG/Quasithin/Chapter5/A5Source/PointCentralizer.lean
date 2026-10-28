module
public import CFSG.Quasithin.Chapter5.A5Source.Crossing
public import CFSG.Quasithin.Chapter4.Defs

/-!
# The point-centralizer consequence of source uniqueness over L

For a nonidentity two-element x centralizing L, the cyclic subgroup generated
by x is a nontrivial two-group normalized by L. Uniqueness over L therefore
places its whole normalizer, and hence C_G(x), in N_G(L). Apply this to the
literal centralizing factor C_{Baum(T)}(L) in the crossing argument to obtain
the escaping conjugate core and the elementary structure of O₂(L Baum(T)).

The genuine earlier premise is uniqueness over L, the conclusion of 4.3.2.
Uniqueness over LT, which the original A₅ context already supplies, does not
replace that premise here.

Source: Aschbacher–Smith, Theorem 4.3.2, printed p.613, and its use in the
proof of Lemma 5.1.7(1), printed p.633 (`refs/quasithin.pdf`).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Source 4.3.2 controls every nonidentity point in the local Sylow centralizer. -/
theorem point_centralizer_of_source_uniqueness
    (hu : Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)))
    {x : G} (hxT : x ∈ (T : Subgroup G))
    (hxL : x ∈ centralizer (L : Set G)) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  have hp : IsPGroup 2 (zpowers x) := T.isPGroup'.to_le (zpowers_le.mpr hxT)
  have hNZ : normalizer (zpowers x : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal hu.2.2 hp
      (fun he => hne (zpowers_eq_bot.mp he))
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure, centralizer_closure]
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hxL l hl)
  rw [← centralizer_closure, ← zpowers_eq_closure]
  exact (Subgroup.centralizer_le_normalizer _).trans hNZ

/-- The actual 5.1.7 crossing consumer with the genuine earlier 4.3.2 input. -/
theorem exists_baumann_elementary_conjugate_core_of_source_uniqueness
    (d : Context T L V V₁ V₂ V₃)
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hu : Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ g ∈ normalizer (baumann (T : Subgroup G) : Set G),
      g ∉ normalizer (L : Set G) ∧
      ¬V.map (MulAut.conj g⁻¹).toMonoidHom ≤ (L ⊔ baumann (T : Subgroup G)).pCoreIn 2 ∧
      baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
        ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom ∧
      IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2) := by
  apply exists_baumann_elementary_conjugate_core d hout
  intro x hx hne
  exact point_centralizer_of_source_uniqueness hu hx.1.1 hx.2 hne

end CFSG.Quasithin.Chapter5.A5Source
