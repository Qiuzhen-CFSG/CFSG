module
public import ABG.ChapterII.Section3.LinearModelPGLProjection
public import ABG.ChapterII.Section2.LinearModelExterior
public import GorensteinWalter.CyclicSquareExtensionComparison
public import GorensteinWalter.PGL2HomRigidity
public import Theory.SpecificGroups.SL2.NoIndexTwo

/-!
# Recognizing the full linear determinant model from its central layer

Let a finite group surject onto PGL2(F) with a nontrivial central two-kernel
and a supplied normal SL2(F) core with its canonical projective map. Suppose
the actual kernel/core join is identified with the predecessor determinant
level, preserving the prescribed SL2 matrix map. At the full two-part m of
|F|-1, the source exterior involution (m=1) or exterior square-center generator
(m at least two) extends this identification to the actual full determinant
level. The full equivalence preserves both the original SL2 matrix equation
and the entire source projective projection.

Construct the target PGL projection and actual exterior matrix in the full
determinant group. The normal SL2 image has trivial centralizer in PGL2;
thus the core matrix equation determines projective compatibility on the
central join. The cyclic-square comparison aligns target squares and
projective conjugation and extends the given equivalence. Apply the same
normal-core rigidity again to preserve the full projection. No matching
square or conjugation-action premise is imposed, and q=3 remains included.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp26--27.
The input Sylow model is supplied by the actual semidihedral or wreathed
matrix construction; the output uses the original determinant-defined group.
This is the full linear branch of the source matrix recognition, before
lifting the odd field-automorphism complement.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem exists_linear_full_model_equiv
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (f : G →* PGL2 F) (hf : Function.Surjective f)
    (hfc : f.ker ≤ Subgroup.center G) (hfp : IsPGroup 2 f.ker) (hfn : f.ker ≠ ⊥)
    (L0 : Subgroup G) [L0.Normal]
    (e0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hf0 : ∀ l : L0, f l = Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection F (e0 l)))
    (m : ℕ) (hm : 1 ≤ m) (hd : 2 ^ m ∣ Nat.card F - 1)
    (ho : Odd ((Nat.card F - 1) / 2 ^ m))
    (eB : (f.ker ⊔ L0 : Subgroup G) ≃* determinantTwoPower F (m - 1))
    (heB : ∀ l : L0,
      (eB ⟨l.val, (show L0 ≤ f.ker ⊔ L0 from le_sup_right) l.property⟩).val =
        Matrix.SpecialLinearGroup.toGL (e0 l))
    (a : G) (ha : a ∉ f.ker ⊔ L0)
    (hasq : (m = 1 ∧ a ^ 2 = 1) ∨ (2 ≤ m ∧ Subgroup.zpowers (a ^ 2) = f.ker))
    (S : Sylow 2 (determinantTwoPower F m))
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hcenter : (Subgroup.center S).map
      ((determinantTwoPower F m).subtype.comp (S : Subgroup _).subtype) ≤
        Subgroup.center (GL (Fin 2) F)) :
    ∃ (g : determinantTwoPower F m →* PGL2 F) (e : G ≃* determinantTwoPower F m),
      Function.Surjective g ∧ g.ker = Subgroup.center (determinantTwoPower F m) ∧
      IsPGroup 2 g.ker ∧ (∀ x : G, g (e x) = f x) ∧
      (∀ l : L0, (e l).val = Matrix.SpecialLinearGroup.toGL (e0 l)) ∧
      (∀ x : determinantTwoPower F 0,
        g ⟨x.val, determinantTwoPower_mono (Nat.zero_le m) x.property⟩ =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (sl2ProjectiveProjection F (determinantTwoPowerZeroEquivSL F x))) := by
  let B := f.ker ⊔ L0
  let D := determinantTwoPower F m
  let B' := (determinantTwoPower F (m - 1)).subgroupOf D
  have hBD : determinantTwoPower F (m - 1) ≤ D := determinantTwoPower_mono (Nat.sub_le m 1)
  let eN : B ≃* B' := eB.trans (Subgroup.subgroupOfEquivOfLe hBD).symm
  obtain ⟨g, hg, hgker, hgp, hg0, hgpre⟩ :=
    exists_top_determinant_pgl_projection F hF m hm hd ho S hS hcenter
  let J := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) |>.range
  have hL0map : L0.map f = J := by
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨sl2ProjectiveProjection F (e0 ⟨l, hl⟩), (hf0 ⟨l, hl⟩).symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨l, hl⟩ := (sl2ProjectiveProjection_surjective F).comp e0.surjective x
      exact ⟨l, l.property, (hf0 l).trans (congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hl)⟩
  have hBpre : B = J.comap f := by
    rw [← hL0map, Subgroup.comap_map_eq, sup_comm]
  let fB := f.comp B.subtype
  let gB := g.comp (B'.subtype.comp eN.toMonoidHom)
  have h0B : L0 ≤ B := le_sup_right
  let L0B := L0.subgroupOf B
  have hmapB : L0B.map fB = J := by
    change L0B.map (f.comp B.subtype) = _
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h0B, hL0map]
  have hagree (l : L0B) : fB l = gB l := by
    let l0 : L0 := ⟨l.val.val, l.property⟩
    let x := (determinantTwoPowerZeroEquivSL F).symm (e0 l0)
    have hx : x.val = Matrix.SpecialLinearGroup.toGL (e0 l0) := by
      have h := determinantTwoPowerZeroEquivSL_toGL F x
      simpa only [x, MulEquiv.apply_symm_apply] using h.symm
    have he : (eN l.val : D) = ⟨x.val, determinantTwoPower_mono (Nat.zero_le m) x.property⟩ := by
      apply Subtype.ext
      exact (heB l0).trans hx.symm
    change f l0 = g (eN l.val)
    rw [he, hg0, show determinantTwoPowerZeroEquivSL F x = e0 l0 from
      (determinantTwoPowerZeroEquivSL F).apply_symm_apply (e0 l0)]
    exact hf0 l0
  have hmaps : fB = gB := pgl2_hom_eq_of_agree_on_normal_psl2 hF fB gB L0B hagree hmapB
  have heN (b : B) : g (eN b) = f b := (DFunLike.congr_fun hmaps b).symm
  have hgn : g.ker ≠ ⊥ := by
    intro hbot
    apply hfn
    apply le_antisymm ?_ bot_le
    intro x hx
    let b : B := ⟨x, (show f.ker ≤ B from le_sup_left) hx⟩
    have hb : (eN b : D) ∈ g.ker := by
      change g (eN b) = 1
      rw [heN]
      exact hx
    have hb1 : eN b = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ hb))
    have hb0 : b = 1 := eN.injective (hb1.trans eN.map_one.symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hb0)
  have hno : ∀ M : Subgroup L0, M.Normal → M.index ≠ 2 := by
    intro M _
    have hodd : Odd (Nat.card F) := by
      obtain ⟨p, n, _, hp, _, he⟩ := hF
      rw [he]
      exact hp.pow
    have h := Matrix.SpecialLinearGroup.index_ne_two
      (two_ne_zero_of_odd_card F hodd) (M.map e0.toMonoidHom)
    exact fun hi => h ((M.index_map_equiv e0).trans hi)
  obtain ⟨b, hb, hbsq⟩ := exists_linear_model_exterior F m hm hd ho
  have hsq : (a ^ 2 = 1 ∧ b ^ 2 = 1) ∨
      (g.ker ≠ ⊥ ∧ Subgroup.zpowers (a ^ 2) = f.ker ∧ Subgroup.zpowers (b ^ 2) = g.ker) := by
    rcases hasq with ⟨hm1, ha1⟩ | ⟨hm2, ha2⟩ <;>
      rcases hbsq with ⟨hm1', hb1⟩ | ⟨hm2', hb2⟩
    · exact Or.inl ⟨ha1, hb1⟩
    · omega
    · omega
    · exact Or.inr ⟨hgn, ha2, hgker ▸ hb2⟩
  obtain ⟨e, he⟩ := exists_mulEquiv_cyclic_square_extensions hF f g hf hg hfc hfp
    (hgker ▸ le_rfl) hgp B B' hBpre hgpre.symm eN heN L0 hno rfl a b ha hb hsq
  have hcore (l : L0) : (e l).val = Matrix.SpecialLinearGroup.toGL (e0 l) := by
    have h := congrArg Subtype.val (he ⟨l.val, h0B l.property⟩)
    exact h.trans (heB l)
  have heproject : f = g.comp e.toMonoidHom := by
    apply pgl2_hom_eq_of_agree_on_normal_psl2 hF f (g.comp e.toMonoidHom) L0 ?_ hL0map
    intro l
    change f l = g (e l)
    rw [he ⟨l.val, h0B l.property⟩, heN]
  exact ⟨g, e, hg, hgker, hgp, fun x => (DFunLike.congr_fun heproject x).symm, hcore, hg0⟩

end ABG
