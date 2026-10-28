module
public import Theory.GroupTheory.PCoreSurjective

/-!
# Orders of p-core-free sections

A p-core-free quotient of a subgroup of A has order dividing |A/O_p(A)|.
The intersection with O_p(A) maps to a normal p-subgroup of the quotient,
so is killed. The first isomorphism theorem gives the divisibility.

The native Janko parabolic exclusions use this to retain the original
small two-core quotient when passing through a different local projection.
-/

public noncomputable section
open Subgroup
namespace MonoidHom

/-- A p-core-free section preserves the ambient p-core quotient order bound. -/
theorem card_corefree_quotient_dvd_of_embedding
    {A B X : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (j : B →* A) (hj : Function.Injective j)
    (f : B →* X) (hf : Function.Surjective f) (hX : pCore p X = ⊥) :
    Nat.card X ∣ Nat.card (A ⧸ pCore p A) := by
  let g := (QuotientGroup.mk' (pCore p A)).comp j
  have hp : IsPGroup p g.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective j hj
  have hn : (g.ker.map f).Normal := Normal.map inferInstance f hf
  have hmap : g.ker.map f ≤ pCore p X := le_sSup ⟨hn, hp.map f⟩
  have hgf : g.ker ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp (bot_unique (hmap.trans_eq hX))
  let r : (B ⧸ g.ker) →* X := QuotientGroup.lift g.ker f (fun x hx => hgf hx)
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨b, rfl⟩ := hf x
    exact ⟨QuotientGroup.mk' g.ker b, rfl⟩
  have hd := card_dvd_of_surjective r hr
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
  exact hd.trans g.range.card_subgroup_dvd_card

end MonoidHom
