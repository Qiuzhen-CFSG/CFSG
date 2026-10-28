module

public import Theory.GroupTheory.PCoreSurjective

/-!
# A core join above a prime-order quotient core

If a surjection has p-group kernel and its target p-core has prime order,
every normal p-subgroup either lies in the kernel or generates the source
p-core with it. This is the reducible local branch of I.5.7(1).
-/

public section
namespace MonoidHom
open Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem pCore_eq_sup_or_le_ker {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    (hc : (Nat.card (pCore p H)).Prime)
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q) :
    pCore p G = Q ⊔ f.ker ∨ Q ≤ f.ker := by
  have hn : (Q.map f).Normal := Normal.map inferInstance f hf
  have hle : Q.map f ≤ pCore p H := le_sSup ⟨hn, hQ.map f⟩
  have hd := card_dvd_of_le hle
  rcases hc.eq_one_or_self_of_dvd _ hd with hb | he
  · exact Or.inr ((map_eq_bot_iff Q).mp (card_eq_one.mp hb))
  · have hm : Q.map f = pCore p H := eq_of_le_of_card_ge hle he.ge
    have hh := f.comap_pCore_of_ker_isPGroup hf hk
    rw [← hm, comap_map_eq] at hh
    exact Or.inl hh.symm

end MonoidHom
