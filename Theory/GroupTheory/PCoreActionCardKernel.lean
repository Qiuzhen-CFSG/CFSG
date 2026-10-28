module
public import Theory.GroupTheory.PCoreImage

/-!
# Detecting a prime-group action kernel by its component image

If K is normal with a p-group quotient, and its action image has the order
of K/O_p(K), then the full action kernel is a p-group. Kernel-image counting
first determines the kernel on K; restricting G → G/K to the full kernel
then proves the assertion by closure of p-groups under extensions.
No identification of the kernel with a centralizer or a core is assumed.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
13.6.23 and the following orthogonal-module argument, printed p.933.
-/

public section
namespace MonoidHom
open Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- A faithful-sized component image and a prime-group outer quotient
force the entire action kernel to be a prime group. -/
theorem isPGroup_ker_of_card_image_eq_core_quotient
    {p : ℕ} [Fact p.Prime] (f : G →* H) (K : Subgroup G) [K.Normal]
    (hquot : IsPGroup p (G ⧸ K))
    (hcard : Nat.card (K.map f) = Nat.card (K ⧸ pCore p K)) :
    IsPGroup p f.ker := by
  let q := f.subgroupMap K
  have hqcard : Nat.card q.ker = Nat.card (pCore p K) := by
    have hq := q.ker.card_mul_index
    rw [index_ker, q.range_eq_top_of_surjective (f.subgroupMap_surjective K),
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (K.map f)) ≃* K.map f).toEquiv] at hq
    have hc := (pCore p K).card_mul_index
    change Nat.card (pCore p K) * Nat.card (K ⧸ pCore p K) = Nat.card K at hc
    rw [hcard] at hq
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hq.trans hc.symm)
  have hqP : IsPGroup p q.ker := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := K)).exists_card_eq
    exact IsPGroup.of_card (hqcard.trans hn)
  let r : f.ker →* G ⧸ K := (QuotientGroup.mk' K).comp f.ker.subtype
  have hrP : IsPGroup p r.ker := by
    let i : r.ker →* q.ker :=
      { toFun := fun x => ⟨⟨x, (QuotientGroup.eq_one_iff _).mp x.property⟩,
          by
            apply Subtype.ext
            exact x.val.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hqP.of_injective i (fun x y he => Subtype.ext (Subtype.ext
      (congrArg (fun z : q.ker => ((z : K) : G)) he)))
  have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup r hrP
  rw [comap_top] at hh
  exact hh.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup f.ker) ≃* f.ker)

end MonoidHom
