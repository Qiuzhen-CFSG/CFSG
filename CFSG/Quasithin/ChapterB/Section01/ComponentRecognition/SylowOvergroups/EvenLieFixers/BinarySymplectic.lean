module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Transport
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ReflectionOrbit
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The small derived symplectic endpoint

The inner image of a Sylow subgroup of A₆ is the intersection of Inn(A₆)
with any Sylow subgroup of Aut(A₆) containing that image. The full
centralizer of this intersection lies in the latter Sylow subgroup. Every
pointwise fixer centralizes the inner image, so the whole fixer is a
two-group. In particular no assumption that its automorphisms are inner is
made. The actual polar-representation equivalence transfers this result to
the commutator subgroup of the projective group PSp₄(2).

The final application is the small derived branch of Aschbacher–Smith,
B.1.13, printed pp.73–74 of `refs/quasithin.pdf`. The imported marked
Aut(A₆) geometry is developed on printed pp.568–570.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
open AlternatingSix.ShadowLocal

/-- The entire A₆ Sylow fixer is a two-group, including its possible outer actors. -/
theorem alternatingSix_fixer : SylowFixerIsTwoGroup (alternatingGroup (Fin 6)) := by
  intro S
  let D := (S : Subgroup A6).map (MulAut.conj : A6 →* AutA6)
  obtain ⟨Q, hDQ⟩ := (S.isPGroup'.map (MulAut.conj : A6 →* AutA6)).exists_le_sylow
  have hDinner : D ≤ AlternatingSix.ShadowLocal.inner := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hDcard : Nat.card (D.subgroupOf Q) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv,
      card_map_of_injective inner_injective]
    exact alternatingSylow_card S
  have he : D.subgroupOf Q = sylowInner Q :=
    Subgroup.eq_of_le_of_card_ge (fun x hx => hDinner hx)
      (by rw [sylowInner_card, hDcard])
  have hmap : D = (Q : Subgroup AutA6) ⊓ AlternatingSix.ShadowLocal.inner := by
    apply le_antisymm (le_inf hDQ hDinner)
    intro x hx
    have hh : (⟨x, hx.1⟩ : Q) ∈ sylowInner Q := hx.2
    rw [← he] at hh
    exact hh
  apply Q.isPGroup'.to_le
  intro a ha
  apply inner_centralizer_le_sylow Q
  rw [← hmap]
  apply mem_centralizer_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hax : a x = x := (mem_fixingSubgroup_iff _).mp ha x hx
  ext y
  simp [hax]

/-- The literal commutator of PSp₄(2), using the checked six-letter polar action. -/
theorem binarySymplecticDerived_fixer :
    SylowFixerIsTwoGroup (commutator (ClassicalGroup.PSp 2 (ZMod 2))) :=
  fixer_of_equiv
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    alternatingSix_fixer

/-- The derived binary symplectic case discharges the source's actual fixer premise. -/
theorem binarySymplecticDerived_le_component {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (e : L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN e
    binarySymplecticDerived_fixer hd

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
