module
public import Theory.GroupTheory.TwoPerfectCubicKernel
public import Theory.GroupTheory.PerfectSylowPreservingAction
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Sylow normalizers outside a two-perfect cubic subgroup

Let A be two-perfect with |A/O₂(A)| = 3, and let S normalize A.
If a normal subgroup C does not contain A, the restriction of the
quotient map G → G/C to A has two-group kernel. The normal supplement
A in AS extends this to the full kernel, giving AS ∩ C = S ∩ C.
Thus AS normalizes the Sylow intersection and its intrinsic normalizer
in C. The latter is solvable by the Sylow-normalizer theorem.

Source application: the L₁ outside K branch of Aschbacher–Smith
14.7.40–41, printed p.1061, refs/quasithin.pdf. Normality here is in the
chosen local group; no ambient normality in the original group is used.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- The full normal-subgroup intersection of AS is its Sylow intersection. -/
theorem cubic_supplement_inf_normal (A C : Subgroup G) [C.Normal]
    (S : Sylow 2 G) (hp : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) (hne : ¬ A ≤ C) :
    (A ⊔ (S : Subgroup G)) ⊓ C = (S : Subgroup G) ⊓ C := by
  let E := A ⊔ (S : Subgroup G)
  let A₀ := A.subgroupOf E
  let S₀ := S.subtype (show (S : Subgroup G) ≤ E from le_sup_right)
  let f := (QuotientGroup.mk' C).comp E.subtype
  have hAE : A ≤ E := le_sup_left
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  let e := subgroupOfEquivOfLe hAE
  have hp₀ : IsPPerfect 2 A₀ := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hc₀ : Nat.card (A₀ ⧸ pCore 2 A₀) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact hc
  have hf : f.comp A₀.subtype ≠ 1 := by
    intro he
    apply hne
    intro a ha
    have hh := congrArg (fun k => k (⟨⟨a,hAE ha⟩,ha⟩ : A₀)) he
    exact (QuotientGroup.eq_one_iff (N := C) a).mp hh
  have hgen : A₀ ⊔ (S₀ : Subgroup E) = ⊤ := by
    rw [Sylow.coe_subtype, ←subgroupOf_sup hAE
      (show (S : Subgroup G) ≤ E from le_sup_right)]
    exact subgroupOf_self E
  have hk := f.kernel_isPGroup_of_normal_supplement A₀ (S₀ : Subgroup E)
    S₀.isPGroup' hgen ((f.comp A₀.subtype).kernel_isTwoGroup_of_twoPerfect_cubic hp₀ hc₀ hf)
  have hker : f.ker ≤ (S₀ : Subgroup E) := hk.le_sylow_of_normal S₀
  apply le_antisymm
  · intro x hx
    exact ⟨hker (show (⟨x,hx.1⟩ : E) ∈ f.ker from
      (QuotientGroup.eq_one_iff (N := C) x).mpr hx.2),hx.2⟩
  · exact inf_le_inf le_sup_right le_rfl

/-- The original cubic subgroup preserves the actual Sylow intersection. -/
theorem cubic_supplement_normalizes_sylow_inf (A C : Subgroup G) [C.Normal]
    (S : Sylow 2 G) (hp : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) (hne : ¬ A ≤ C) :
    A ⊔ (S : Subgroup G) ≤ normalizer ((S : Subgroup G) ⊓ C : Set G) := by
  change A ⊔ (S : Subgroup G) ≤ normalizer (↑((S : Subgroup G) ⊓ C) : Set G)
  rw [←cubic_supplement_inf_normal A C S hp hc hn hne]
  exact (le_inf (A ⊔ (S : Subgroup G)).le_normalizer le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf

/-- The same actor preserves the intrinsic Sylow normalizer in C. -/
theorem cubic_supplement_normalizes_sylow_normalizer (A C : Subgroup G) [C.Normal]
    (S : Sylow 2 G) (hp : IsPPerfect 2 A)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hn : (S : Subgroup G) ≤ normalizer (A : Set G)) (hne : ¬ A ≤ C) :
    A ⊔ (S : Subgroup G) ≤
      normalizer (C ⊓ normalizer ((S : Subgroup G) ⊓ C : Set G) : Set G) := by
  exact (le_inf le_normalizer_of_normal
    ((cubic_supplement_normalizes_sylow_inf A C S hp hc hn hne).trans
      (normalizer ((S : Subgroup G) ⊓ C : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- The intrinsic normalizer of this actual Sylow intersection is solvable. -/
theorem normal_sylow_normalizer_solvable [Finite G] (C : Subgroup G) [C.Normal]
    (S : Sylow 2 G) :
    Group.IsSolvable (C ⊓ normalizer ((S : Subgroup G) ⊓ C : Set G) : Subgroup G) := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let : Group.IsSolvable (normalizer (P : Set C)) := P.normalizer_isSolvable_two
  have he : (normalizer (P : Set C)).map C.subtype =
      C ⊓ normalizer ((S : Subgroup G) ⊓ C : Set G) := by
    change (normalizer (↑(P : Subgroup C) : Set C)).map C.subtype =
      C ⊓ normalizer (↑((S : Subgroup G) ⊓ C) : Set G)
    have hi : ((S : Subgroup G) ⊓ C).subgroupOf C = (S : Subgroup G).subgroupOf C := by
      ext x
      exact and_iff_left x.property
    rw [hP, ←hi, ←subgroupOf_normalizer_eq (show (S : Subgroup G) ⊓ C ≤ C from inf_le_right),
      subgroupOf_map_subtype,inf_comm]
  rw [←he]
  exact Group.isSolvable_of_surjective (f := C.subtype.subgroupMap _)
    (C.subtype.subgroupMap_surjective _)

end Subgroup
