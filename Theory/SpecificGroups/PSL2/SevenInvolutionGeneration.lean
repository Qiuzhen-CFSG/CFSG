module
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.GroupAction.DihedralInnerInvolutions
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupAction.AutomorphismFixedSubgroup
import Mathlib.Tactic
open Subgroup
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms


/-!
# Dihedral involution fixed-subgroup generation in PSL₂(7)

A central square in a faithful dihedral actor is an inner involution because
Out(PSL₂(7)) has order two. Transport to SL₃(2) and involution conjugacy mark
this involution as the upper transvection E₁₃. Its fixed subgroup contains the
upper triangular Sylow subgroup. The two proper parabolic overgroups are the
only possibilities for a proper subgroup containing that Sylow subgroup.

Every automorphism fixing E₁₃ is one of sixteen upper-triangular inner maps
or their graph translates. Explicit fixed matrices show that the involutions
whose fixed subgroups lie inside either parabolic commute pairwise.
The two noncommuting reflections of the original actor exclude both cases.
All finite certificates use kernel reduction at the repository defaults.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.21, printed p.566, the PSL₂(7) case of the
involution-centralizer generation step for a nonquaternion core.
-/

open scoped MatrixGroups
namespace Theory.PSL2.SevenInvolutionGeneration

private def model (b : Bool) (i : Fin 8) : MulAut SL :=
  if b then MulAut.conj (Bruhat.upper i) * diagram else MulAut.conj (Bruhat.upper i)

private def pointWitness (b : Bool) (i : Fin 8) : SL :=
  if b then
    ![Bruhat.perm 5, 1,
      ⟨!![0,1,0;1,0,0;1,1,1], by decide⟩, 1, 1,
      ⟨!![0,0,1;1,1,0;1,0,1], by decide⟩, 1,
      ⟨!![0,1,1;0,1,0;1,1,0], by decide⟩] i
  else
    ![Bruhat.perm 5, 1, 1, 1,
      ⟨!![1,0,0;1,1,0;0,0,1], by decide⟩, 1, Bruhat.perm 2, 1] i

private def lineWitness (b : Bool) (i : Fin 8) : SL :=
  if b then pointWitness b i
  else
    ![Bruhat.perm 5,
      ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩, 1, Bruhat.perm 1, 1, 1, 1, 1] i

private theorem point_test : ∀ b : Bool, ∀ i : Fin 8,
    model b i (model b i (Bruhat.perm 5)) = Bruhat.perm 5 →
    (b = false ∧ (i = 1 ∨ i = 2 ∨ i = 3)) ∨
      (model b i (pointWitness b i) = pointWitness b i ∧
        pointWitness b i ∉ pointParabolicSL) := by decide +kernel

private theorem line_test : ∀ b : Bool, ∀ i : Fin 8,
    model b i (model b i (Bruhat.perm 5)) = Bruhat.perm 5 →
    (b = false ∧ (i = 2 ∨ i = 4 ∨ i = 6)) ∨
      (model b i (lineWitness b i) = lineWitness b i ∧
        lineWitness b i ∉ lineParabolicSL) := by decide +kernel

private theorem centralizer_table : ∀ g : SL,
    g * Bruhat.upper 2 = Bruhat.upper 2 * g → ∃ i : Fin 8, g = Bruhat.upper i := by
  decide +kernel

private theorem borel_fixed : ∀ g : SL, g ∈ borelSL →
    (MulAut.conj (Bruhat.upper 2)) g = g := by decide +kernel


private theorem model_of_fixed (α : MulAut SL) (ht : α (Bruhat.upper 2) = Bruhat.upper 2) :
    ∃ b : Bool, ∃ i : Fin 8, α = model b i := by
  have hd : diagram (Bruhat.upper 2) = Bruhat.upper 2 := by decide +kernel
  obtain ⟨g, hg | hg⟩ := inner_or_graph α
  · have hc : g * Bruhat.upper 2 = Bruhat.upper 2 * g := by
      apply (mul_inv_eq_iff_eq_mul).mp
      simpa only [hg, MulAut.conj_apply] using ht
    obtain ⟨i, rfl⟩ := centralizer_table g hc
    exact ⟨false, i, hg⟩
  · have hc : g * Bruhat.upper 2 = Bruhat.upper 2 * g := by
      apply (mul_inv_eq_iff_eq_mul).mp
      simpa only [hg, MulAut.mul_apply, MulAut.conj_apply, hd] using ht
    obtain ⟨i, rfl⟩ := centralizer_table g hc
    exact ⟨true, i, hg⟩

private theorem point_actors (α : MulAut SL) (hα : α ^ 2 = 1)
    (ht : α (Bruhat.upper 2) = Bruhat.upper 2)
    (hfix : α.fixedSubgroup ≤ pointParabolicSL) :
    ∃ i : Fin 8, (i = 1 ∨ i = 2 ∨ i = 3) ∧ α = MulAut.conj (Bruhat.upper i) := by
  obtain ⟨b, i, rfl⟩ := model_of_fixed α ht
  have hs : model b i (model b i (Bruhat.perm 5)) = Bruhat.perm 5 :=
    congrArg (fun a : MulAut SL => a (Bruhat.perm 5)) hα
  rcases point_test b i hs with ⟨rfl, hi⟩ | ⟨hw, hn⟩
  · exact ⟨i, hi, rfl⟩
  · exact (hn (hfix ((MulAut.mem_fixedSubgroup _ _).mpr hw))).elim

private theorem line_actors (α : MulAut SL) (hα : α ^ 2 = 1)
    (ht : α (Bruhat.upper 2) = Bruhat.upper 2)
    (hfix : α.fixedSubgroup ≤ lineParabolicSL) :
    ∃ i : Fin 8, (i = 2 ∨ i = 4 ∨ i = 6) ∧ α = MulAut.conj (Bruhat.upper i) := by
  obtain ⟨b, i, rfl⟩ := model_of_fixed α ht
  have hs : model b i (model b i (Bruhat.perm 5)) = Bruhat.perm 5 :=
    congrArg (fun a : MulAut SL => a (Bruhat.perm 5)) hα
  rcases line_test b i hs with ⟨rfl, hi⟩ | ⟨hw, hn⟩
  · exact ⟨i, hi, rfl⟩
  · exact (hn (hfix ((MulAut.mem_fixedSubgroup _ _).mpr hw))).elim

private theorem marked_generation (α β : MulAut SL) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1)
    (hab : α * β ≠ β * α)
    (ha : α (Bruhat.upper 2) = Bruhat.upper 2) (hb : β (Bruhat.upper 2) = Bruhat.upper 2)
    (N : Subgroup SL) (hzN : (MulAut.conj (Bruhat.upper 2)).fixedSubgroup ≤ N)
    (haN : α.fixedSubgroup ≤ N) (hbN : β.fixedSubgroup ≤ N) : N = ⊤ := by
  have hBN : borelSL ≤ N := fun g hg => hzN ((MulAut.mem_fixedSubgroup _ _).mpr
    (borel_fixed g hg))
  by_contra hn
  apply hab
  rcases overgroup_borelSL N hBN hn with hp | hl
  · obtain ⟨i, hi, rfl⟩ := point_actors α hα ha (haN.trans hp)
    obtain ⟨j, hj, rfl⟩ := point_actors β hβ hb (hbN.trans hp)
    have hcomm : ∀ i j : Fin 8, (i = 1 ∨ i = 2 ∨ i = 3) →
        (j = 1 ∨ j = 2 ∨ j = 3) → Bruhat.upper i * Bruhat.upper j =
          Bruhat.upper j * Bruhat.upper i := by decide +kernel
    rw [← map_mul, hcomm i j hi hj, map_mul]
  · obtain ⟨i, hi, rfl⟩ := line_actors α hα ha (haN.trans hl)
    obtain ⟨j, hj, rfl⟩ := line_actors β hβ hb (hbN.trans hl)
    have hcomm : ∀ i j : Fin 8, (i = 2 ∨ i = 4 ∨ i = 6) →
        (j = 2 ∨ j = 4 ∨ j = 6) → Bruhat.upper i * Bruhat.upper j =
          Bruhat.upper j * Bruhat.upper i := by decide +kernel
    rw [← map_mul, hcomm i j hi hj, map_mul]

private theorem fixed_map_le {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (α : MulAut G) (N : Subgroup G) (h : α.fixedSubgroup ≤ N) :
    (MulAut.congr e α).fixedSubgroup ≤ N.map e.toMonoidHom := by
  intro x hx
  refine ⟨e.symm x, h ?_, e.apply_symm_apply x⟩
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  apply e.injective
  have he := (MulAut.mem_fixedSubgroup _ _).mp hx
  simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using he

private theorem generation_of_marking {G : Type*} [Group G] (e : G ≃* SL)
    (t : G) (ht : e t = Bruhat.upper 2)
    (α β : MulAut G) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1)
    (hab : α * β ≠ β * α) (ha : α t = t) (hb : β t = t)
    (N : Subgroup G) (hzN : (MulAut.conj t).fixedSubgroup ≤ N)
    (haN : α.fixedSubgroup ≤ N) (hbN : β.fixedSubgroup ≤ N) : N = ⊤ := by
  have hconj : MulAut.congr e (MulAut.conj t) = MulAut.conj (Bruhat.upper 2) := by
    apply MulEquiv.ext
    intro x
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply, ht]
  have ht' : e.symm (Bruhat.upper 2) = t := by rw [← ht, e.symm_apply_apply]
  have hN := marked_generation (MulAut.congr e α) (MulAut.congr e β)
    (by rw [← map_pow, hα, map_one]) (by rw [← map_pow, hβ, map_one])
    (fun he => hab ((MulAut.congr e).injective (by simpa only [map_mul] using he)))
    (by simp only [MulAut.congr_apply, MulEquiv.trans_apply, ht', ha, ht])
    (by simp only [MulAut.congr_apply, MulEquiv.trans_apply, ht', hb, ht])
    (N.map e.toMonoidHom)
    (hconj ▸ fixed_map_le e (MulAut.conj t) N hzN)
    (fixed_map_le e α N haN) (fixed_map_le e β N hbN)
  apply top_unique
  intro x _
  have hx : e x ∈ N.map e.toMonoidHom := hN ▸ mem_top (e x)
  obtain ⟨y, hy, he⟩ := hx
  exact e.injective he ▸ hy

private theorem fixed_generation_of_central_inner (t : SL) (ht : orderOf t = 2)
    (α β : MulAut SL) (hα : α ^ 2 = 1) (hβ : β ^ 2 = 1)
    (hab : α * β ≠ β * α) (ha : α t = t) (hb : β t = t)
    (N : Subgroup SL) (hzN : (MulAut.conj t).fixedSubgroup ≤ N)
    (haN : α.fixedSubgroup ≤ N) (hbN : β.fixedSubgroup ≤ N) : N = ⊤ := by
  have ho : orderOf (Bruhat.upper 2) = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  obtain ⟨g, hg⟩ := involutions_conjugate (equiv t) (equiv (Bruhat.upper 2))
    ((equiv.orderOf_eq t).trans ht) ((equiv.orderOf_eq _).trans ho)
  let e : MulAut SL := MulAut.conj (equiv.symm g)
  have he : e t = Bruhat.upper 2 := by
    apply equiv.injective
    simpa only [e, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] using hg
  exact generation_of_marking e t he α β hα hβ hab ha hb N hzN haN hbN



/-- Fixed subgroups of all involutions in a faithful nonabelian dihedral
 two-group action generate the actual group PSL₂(7). -/
public theorem fixed_generation_of_dihedral {P : Type*} [Group P] [Finite P]
    {k : ℕ} (hk : 2 ≤ k) (e : P ≃* DihedralGroup (2 ^ k))
    (f : P →* MulAut PSL(2, ZMod 7)) (hf : Function.Injective f)
    (N : Subgroup PSL(2, ZMod 7))
    (hfixed : ∀ i : P, orderOf i = 2 → (f i).fixedSubgroup ≤ N) : N = ⊤ := by
  let c : PSL(2, ZMod 7) ≃* SL :=
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.trans equiv.symm
  let q : P →* MulAut SL := (MulAut.congr c).toMonoidHom.comp f
  have hq : Function.Injective q := (MulAut.congr c).injective.comp hf
  have hi : (MulAut.innerSubgroup SL).index = 2 := Automorphisms.card_outer_sl
  obtain ⟨z, j, t, _, hz, _, _, ht, hzt, hfix⟩ :=
    MulAut.dihedral_inner_involutions q hq hk e center_eq_bot hi
  obtain ⟨a, b, ha, hb, hab⟩ := DihedralGroup.exists_noncommuting_involutions hk e
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hN := fixed_generation_of_central_inner t ht (q a) (q b)
    (by rw [← map_pow, ha2, map_one])
    (by rw [← map_pow, hb2, map_one])
    (fun he => hab (hq (by simpa only [map_mul] using he))) (hfix a) (hfix b)
    (N.map c.toMonoidHom)
    (hzt ▸ fixed_map_le c (f z) N (hfixed z hz))
    (fixed_map_le c (f a) N (hfixed a ha)) (fixed_map_le c (f b) N (hfixed b hb))
  apply top_unique
  intro x _
  have hx : c x ∈ N.map c.toMonoidHom := hN ▸ mem_top (c x)
  obtain ⟨y, hy, he⟩ := hx
  exact c.injective he ▸ hy

end Theory.PSL2.SevenInvolutionGeneration
