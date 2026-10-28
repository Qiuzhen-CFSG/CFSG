module
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Theory.GroupTheory.Commutator.CentralDihedralSylow

/-!
# Comparison of central two-covers

Let E and a perfect group L surject onto the same finite group B with
central two-group kernels. Assume the kernel for L has order two, the
kernel for E meets its derived subgroup nontrivially, and the Sylow
two-subgroups of B are dihedral. Then the derived subgroup of E is
isomorphic to L. Neither E nor its derived subgroup is assumed perfect.

Form the fiber product W of the two actual surjections. Its central kernel
embeds into the product of the original two-kernels. The dihedral Sylow
bound gives at most two elements in the derived part of this kernel.
The derived subgroup of W maps onto both the derived subgroup of E and L;
finite kernel-cardinality comparisons force both maps to be bijective.

This supplies the comparison step in the two-primary Schur-cover argument
used in Alperin--Brauer--Gorenstein, Chapter II, Section 3, Proposition 2
(article page 22). It requires no full multiplier classification, so the
exceptional odd multiplier at field order nine is not excluded. Its SL2
application uses perfectness of the canonical cover only for field order
larger than three; field order three is treated separately.
-/

namespace CentralExtension
open Subgroup

private theorem card_eq_of_surjective
    {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) :
    Nat.card X = Nat.card Y * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

universe u v w

/-- A central two-cover with nontrivial derived kernel has the same derived
subgroup as a perfect double cover of the same dihedral-Sylow quotient. -/
public theorem commutator_mulEquiv_of_central_two_covers
    {E : Type u} {L : Type v} {B : Type w}
    [Group E] [Group L] [Group B] [Finite E] [Finite L] [Finite B]
    [Group.IsPerfect L]
    (f : E →* B) (g : L →* B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfcentral : f.ker ≤ center E) (hgcentral : g.ker ≤ center L)
    (hf2 : IsPGroup 2 f.ker) (hg2 : IsPGroup 2 g.ker)
    (hfn : f.ker ⊓ commutator E ≠ ⊥) (hgcard : Nat.card g.ker = 2)
    (hdihedral : ∀ T : Sylow 2 B, ∃ n : ℕ,
      0 < n ∧ Nonempty (T ≃* DihedralGroup n)) :
    Nonempty (commutator E ≃* L) := by
  classical
  let W : Subgroup (E × L) :=
    (f.comp (MonoidHom.fst E L)).eqLocus (g.comp (MonoidHom.snd E L))
  let a : W →* E := (MonoidHom.fst E L).comp W.subtype
  let b : W →* L := (MonoidHom.snd E L).comp W.subtype
  have hab (x : W) : f (a x) = g (b x) := x.property
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨y, hy⟩ := hg (f x)
    exact ⟨⟨(x, y), hy.symm⟩, rfl⟩
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨x, hx⟩ := hf (g y)
    exact ⟨⟨(x, y), hx⟩, rfl⟩
  let q : W →* B := f.comp a
  have hq : Function.Surjective q := hf.comp ha
  have hqcentral : q.ker ≤ center W := by
    intro x hx
    have hxE : a x ∈ f.ker := hx
    have hxL : b x ∈ g.ker := by
      change g (b x) = 1
      rw [← hab]
      exact hx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact Prod.ext (mem_center_iff.mp (hfcentral hxE) (a y))
      (mem_center_iff.mp (hgcentral hxL) (b y))
  let k : q.ker →* f.ker × g.ker :=
    { toFun := fun x =>
        (⟨a x.1, x.2⟩, ⟨b x.1, by
          change g (b x.1) = 1
          rw [← hab]
          exact x.2⟩)
      map_one' := by ext <;> rfl
      map_mul' := by intros; ext <;> rfl }
  have hk : Function.Injective k := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : f.ker × g.ker => (z.1 : E)) hxy)
      (congrArg (fun z : f.ker × g.ker => (z.2 : L)) hxy)
  have hq2 : IsPGroup 2 q.ker := by
    obtain ⟨m, hm⟩ := hf2.exists_card_eq
    obtain ⟨n, hn⟩ := hg2.exists_card_eq
    have hp : IsPGroup 2 (f.ker × g.ker) :=
      IsPGroup.of_card (n := m + n) (by rw [Nat.card_prod, hm, hn, pow_add])
    exact hp.of_injective k hk
  let S : Sylow 2 W := Classical.choice inferInstance
  obtain ⟨n, hn, ⟨eS⟩⟩ := hdihedral (Sylow.mapSurjective hq S)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hsmall := card_ker_inf_commutator_le_two_of_dihedral_sylow
    q hq hqcentral hq2 S eS
  let C := commutator W
  have hmapa : C.map a = commutator E := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr ha]
    rfl
  let aC : C →* commutator E := (a.comp C.subtype).codRestrict (commutator E)
    (fun x => hmapa ▸ mem_map_of_mem a x.property)
  have haC : Function.Surjective aC := by
    intro y
    have hy : (y : E) ∈ C.map a := by rw [hmapa]; exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let bC : C →* L := b.comp C.subtype
  have hbC : Function.Surjective bC := by
    have hmapb : C.map b = ⊤ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hb]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ C.map b := by rw [hmapb]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  let qC : C →* B := q.comp C.subtype
  have hqC : Function.Surjective qC := by
    intro z
    obtain ⟨y, hy⟩ := hg z
    obtain ⟨x, hx⟩ := hbC y
    refine ⟨x, ?_⟩
    change f (a x.1) = z
    rw [hab]
    exact (congrArg g hx).trans hy
  let eker : qC.ker ≃ (q.ker ⊓ C : Subgroup W) :=
    { toFun := fun x => ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hqCsmall : Nat.card qC.ker ≤ 2 := (Nat.card_congr eker).trans_le hsmall
  have hCcard : Nat.card C ≤ Nat.card B * 2 := by
    rw [card_eq_of_surjective qC hqC]
    exact Nat.mul_le_mul_left _ hqCsmall
  have hLcard : Nat.card L = Nat.card B * 2 := by
    rw [card_eq_of_surjective g hg, hgcard]
  have hbCbij := hbC.bijective_of_nat_card_le (hCcard.trans_eq hLcard.symm)
  let fD : commutator E →* B := f.comp (commutator E).subtype
  have hfD : Function.Surjective fD := by
    intro z
    obtain ⟨x, hx⟩ := hqC z
    exact ⟨aC x, hx⟩
  let efker : fD.ker ≃ (f.ker ⊓ commutator E : Subgroup E) :=
    { toFun := fun x => ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hlarge : 2 ≤ Nat.card fD.ker := by
    rw [Nat.card_congr efker]
    let : Nontrivial (f.ker ⊓ commutator E : Subgroup E) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hfn
    exact Finite.one_lt_card
  have hDcard : Nat.card B * 2 ≤ Nat.card (commutator E) := by
    rw [card_eq_of_surjective fD hfD]
    exact Nat.mul_le_mul_left _ hlarge
  have haCbij := haC.bijective_of_nat_card_le (hCcard.trans hDcard)
  exact ⟨(MulEquiv.ofBijective aC haCbij).symm.trans (MulEquiv.ofBijective bC hbCbij)⟩

end CentralExtension

