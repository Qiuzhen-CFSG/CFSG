module
public import ABG.ChapterII.Section3.UnitaryModelPGLProjection
public import ABG.ChapterII.Section2.UnitaryModelExterior
public import GorensteinWalter.CyclicSquareExtensionComparison
public import GorensteinWalter.PGL2HomRigidity
public import Theory.SpecificGroups.SL2.NoIndexTwo

/-!
# Full unitary model comparison with prescribed core and projection

Suppose a finite group G has a prescribed surjection to PGL2(GF(p^n)),
with nontrivial central two-group kernel and a normal SL2 core on which
the map is the canonical projective map. Let 2^m be the exact two-part
of p^n+1, with p odd, n nonzero, and m at least one. A supplied equivalence
from the kernel--core join to the actual predecessor SU2Level(m-1),
preserving the original core matrix through the chosen equivalence eSU,
extends to an equivalence G ≃ SU2Level m under the source exterior-square
alternative and the actual matrix Sylow geometry. The resulting equivalence
preserves the whole given projective map and the original core matrix;
the target projection retains the supplied eSU in its level-zero formula.

First construct the actual target PGL map. Its prescribed formula and the
central-layer matrix equation give agreement on the normal SL2 core.
Triviality of the centralizer of the canonical PSL2 range upgrades this
to agreement on the entire central layer. The actual unitary exterior has
square one at level one and a square generating the center at higher
levels. SL2 has no normal subgroup of index two, so the proved cyclic-square
extension comparison matches the exteriors and extends the layer map.
A second use of projective rigidity proves compatibility on the full group.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pages 26-27,
the comparison of L with the actual model L*. This result retains all odd
fields and uses the original identity-Gram Hermitian unitary group over
GF(p^(2n)); no agreement of exterior actions or exact squares is assumed.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

public theorem exists_unitary_full_model_equiv
    {G : Type*} [Group G] [Finite G]
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (f : G →* PGL2 (GaloisField p n)) (hf : Function.Surjective f)
    (hfc : f.ker ≤ Subgroup.center G) (hfp : IsPGroup 2 f.ker) (hfn : f.ker ≠ ⊥)
    (L0 : Subgroup G) [L0.Normal]
    (e0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))
    (eSU : (unitaryForm 2 p n hn).specialSubgroup ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))
    (hf0 : ∀ l : L0, f l = Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2ProjectiveProjection (GaloisField p n) (e0 l)))
    (m : ℕ) (hm : 1 ≤ m) (hd : 2 ^ m ∣ p ^ n + 1)
    (ho : Odd ((p ^ n + 1) / 2 ^ m))
    (eB : (f.ker ⊔ L0 : Subgroup G) ≃* SU2Level p n hn (m - 1))
    (heB : ∀ l : L0,
      (eB ⟨l.val, (show L0 ≤ f.ker ⊔ L0 from le_sup_right) l.property⟩).val.val =
        (eSU.symm (e0 l)).val)
    (a : G) (ha : a ∉ f.ker ⊔ L0)
    (hasq : (m = 1 ∧ a ^ 2 = 1) ∨ (2 ≤ m ∧ Subgroup.zpowers (a ^ 2) = f.ker))
    (S : Sylow 2 (SU2Level p n hn m))
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hcenter : (Subgroup.center S).map
      ((SU2Level p n hn m).subtype.comp (S : Subgroup _).subtype) ≤
        Subgroup.center (GU2 p n hn)) :
    ∃ (g : SU2Level p n hn m →* PGL2 (GaloisField p n)) (e : G ≃* SU2Level p n hn m),
      Function.Surjective g ∧ g.ker = Subgroup.center (SU2Level p n hn m) ∧
      IsPGroup 2 g.ker ∧ (∀ x : G, g (e x) = f x) ∧
      (∀ l : L0, (e l).val.val = (eSU.symm (e0 l)).val) ∧
      (∀ x : SU2Level p n hn 0,
        g ⟨x.val, SU2Level_mono p n hn (Nat.zero_le m) x.property⟩ =
          Matrix.ProjectiveSpecialLinearGroup.toPGL
            (sl2ProjectiveProjection (GaloisField p n) (eSU (SU2LevelZeroEquivSpecial p n hn x)))) := by
  let F := GaloisField p n
  have hF : IsOddPrimePower (Nat.card F) :=
    ⟨p, n, Fact.out, hp, Nat.pos_of_ne_zero hn, GaloisField.card p n hn⟩
  let B := f.ker ⊔ L0
  let D := SU2Level p n hn m
  let B' := (SU2Level p n hn (m - 1)).subgroupOf D
  have hBD : SU2Level p n hn (m - 1) ≤ D := SU2Level_mono p n hn (Nat.sub_le m 1)
  let eN : B ≃* B' := eB.trans (Subgroup.subgroupOfEquivOfLe hBD).symm
  obtain ⟨g, hg, hgker, hgp, hg0, hgpre⟩ :=
    exists_top_unitary_determinant_pgl_projection p n hp hn m hm hd ho eSU S hS hcenter
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
    let x := (SU2LevelZeroEquivSpecial p n hn).symm (eSU.symm (e0 l0))
    have hx : x.val.val = (eSU.symm (e0 l0)).val :=
      SU2LevelZeroEquivSpecial_symm_val p n hn (eSU.symm (e0 l0))
    have he : (eN l.val : D) = ⟨x.val, SU2Level_mono p n hn (Nat.zero_le m) x.property⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact (heB l0).trans hx.symm
    change f l0 = g (eN l.val)
    have hx0 : eSU (SU2LevelZeroEquivSpecial p n hn x) = e0 l0 := by
      simp only [x, MulEquiv.apply_symm_apply]
    rw [he, hg0, hx0]
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
  obtain ⟨b, hb, hbsq⟩ := exists_unitary_model_exterior p n hp hn m hm hd ho
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
  have hcore (l : L0) : (e l).val.val = (eSU.symm (e0 l)).val := by
    have h := congrArg (fun z : D => z.val.val) (he ⟨l.val, h0B l.property⟩)
    exact h.trans (heB l)
  have heproject : f = g.comp e.toMonoidHom := by
    apply pgl2_hom_eq_of_agree_on_normal_psl2 hF f (g.comp e.toMonoidHom) L0 ?_ hL0map
    intro l
    change f l = g (e l)
    rw [he ⟨l.val, h0B l.property⟩, heN]
  exact ⟨g, e, hg, hgker, hgp, fun x => (DFunLike.congr_fun heproject x).symm, hcore, hg0⟩

end ABG
