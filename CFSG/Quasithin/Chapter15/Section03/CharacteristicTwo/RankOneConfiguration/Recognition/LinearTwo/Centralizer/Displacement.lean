module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.BlockAction
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Eliminating the natural-block automorphism displacement

Let L be a perfect short group whose actual module U(L)/C_U(L) and actor
L/O₂(L) are identified with the natural SL₂-module over the four-element field.
An automorphism fixing U(L) and O^{3′}(B) pointwise is the identity, where B is
the full preimage of the standard matrix Borel.

The reduction in `BlockAction` puts its displacement in U(L). Modulo C_U(L),
this is a crossed homomorphism. Since O₂(L)/U(L) is central and the natural
module has no nonzero fixed vectors, it descends to SL₂. The Borel residual
surjects onto the matrix Borel. Vanishing there, the diagonal/Weyl relation
forces vanishing at the coordinate swap; upper and lower transvections then
force vanishing everywhere. Finally the displacement is central, so uniqueness
of maps from a perfect group into a central extension kills it.

This is the conditional intrinsic step in Aschbacher–Smith 15.3.30, printed
pp.1131–1132. The block and central quotient conventions are C.1.7–13,
pp.123–125; the related cohomology and covering-module discussion is I.1.5–6
and I.2.3, pp.408–413. The pointwise fixation of U(L) remains an input for the
parent centralizer argument. No splitting or Schur multiplier assertion is used.
-/

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped Matrix commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo
variable {L F : Type*} [Group L] [Field F] [Group.IsPerfect L]
variable (model : ChapterC.BlockModuleModel L (Matrix.SL2.naturalAction F))
variable (a : MulAut L) (hfixU : ∀ u : ChapterC.blockU L, a u = u)

private noncomputable def delta (l : L) : ChapterC.blockU L :=
  ⟨a l * l⁻¹, displacement_mem_blockU_of_blockU_fixed model a hfixU l⟩

private theorem delta_mul (l m : L) :
    delta model a hfixU (l * m) = delta model a hfixU l *
      ChapterC.blockConjugate L l (delta model a hfixU m) := by
  apply Subtype.ext
  change a (l * m) * (l * m)⁻¹ =
    (a l * l⁻¹) * (l * (a m * m⁻¹) * l⁻¹)
  rw [map_mul]
  group

private theorem delta_eq_of_quotient_eq {l m : L}
    (h : QuotientGroup.mk' (ChapterC.blockU L) l =
      QuotientGroup.mk' (ChapterC.blockU L) m) :
    delta model a hfixU l = delta model a hfixU m := by
  have hu : l⁻¹ * m ∈ ChapterC.blockU L := (QuotientGroup.eq.mp h)
  have he := hfixU ⟨l⁻¹ * m, hu⟩
  change a (l⁻¹ * m) = l⁻¹ * m at he
  rw [map_mul, map_inv] at he
  apply Subtype.ext
  change a l * l⁻¹ = a m * m⁻¹
  have hh := congrArg (fun x : L => a l * x * m⁻¹) he
  simpa [mul_assoc] using hh.symm

private noncomputable def vector (l : L) : Fin 2 → F :=
  Multiplicative.toAdd (model.moduleIso
    (QuotientGroup.mk' (ChapterC.blockFixed L) (delta model a hfixU l)))

private theorem vector_mul (l m : L) :
    vector model a hfixU (l * m) =
      (blockLinearMap model l).val *ᵥ vector model a hfixU m + vector model a hfixU l := by
  unfold vector
  rw [delta_mul, map_mul, map_mul, model.intertwining]
  exact add_comm _ _

private theorem vector_eq_of_quotient_eq {l m : L}
    (h : QuotientGroup.mk' (ChapterC.blockU L) l =
      QuotientGroup.mk' (ChapterC.blockU L) m) :
    vector model a hfixU l = vector model a hfixU m := by
  unfold vector
  rw [delta_eq_of_quotient_eq model a hfixU h]

/-- The central core quotient forces the projected displacement to be invariant,
and the two root groups have no common nonzero fixed vector. -/
private theorem vector_core (n : L) (hn : n ∈ pCore 2 L) : vector model a hfixU n = 0 := by
  have hn1 : blockLinearMap model n = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [blockLinearMap_ker]
  have hinv (g : Matrix.SpecialLinearGroup (Fin 2) F) :
      g.val *ᵥ vector model a hfixU n = vector model a hfixU n := by
    obtain ⟨l, rfl⟩ := blockLinearMap_surjective model g
    have hc := mem_center_iff.mp (ChapterC.blockU_core_image_le_center
      (mem_map_of_mem (QuotientGroup.mk' (ChapterC.blockU L)) hn))
      (QuotientGroup.mk' (ChapterC.blockU L) l)
    have he : vector model a hfixU (l * n) = vector model a hfixU (n * l) :=
      vector_eq_of_quotient_eq model a hfixU (by simpa only [map_mul] using hc)
    rw [vector_mul, vector_mul] at he
    have hone : (blockLinearMap model n).val *ᵥ vector model a hfixU l =
        vector model a hfixU l := by
      rw [hn1]
      exact Matrix.one_mulVec _
    rw [hone] at he
    exact add_right_cancel (he.trans (add_comm _ _))
  have h0 := congrFun (hinv (Matrix.SpecialLinearGroup.transvection zero_ne_one (1 : F))) 0
  have h1 := congrFun (hinv (Matrix.SpecialLinearGroup.transvection one_ne_zero (1 : F))) 1
  simp [transvection_coe, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  ext i
  fin_cases i
  · exact h1
  · exact h0

private theorem vector_eq_of_linear_eq {l m : L}
    (h : blockLinearMap model l = blockLinearMap model m) :
    vector model a hfixU l = vector model a hfixU m := by
  have hn : l⁻¹ * m ∈ pCore 2 L := by
    rw [← blockLinearMap_ker model]
    exact MonoidHom.mem_ker.mpr (by simp [h])
  have he := vector_mul model a hfixU l (l⁻¹ * m)
  rw [mul_inv_cancel_left, vector_core model a hfixU _ hn, mulVec_zero, zero_add] at he
  exact he.symm

omit [Group.IsPerfect L] in
private theorem residual_index_coprime {H : Type*} [Group H] [Finite H] :
    Nat.Coprime 3 (primeToResidual 3 H).index := by
  let P : Sylow 3 H := Classical.choice inferInstance
  have hP : (P : Subgroup H) ≤ primeToResidual 3 H := by
    intro x hx
    obtain ⟨n, hn⟩ := P.2 ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  exact (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).coprime_dvd_right
    (index_dvd_of_le hP)

omit [Group.IsPerfect L] in
/-- The torus has order three, and its normal closure contains every upper
transvection, so the prime-to-three residual is the entire matrix Borel. -/
private theorem borel_residual [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    primeToResidual 3 (rankOneBorel F) = ⊤ := by
  classical
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, hb⟩ := exists_ne (1 : Fˣ)
  have hb1 : (b : F) ≠ 1 := by simpa using hb
  have hbsq : (b : F) ^ 2 ≠ 1 := by
    intro he
    exact hb1 (CharTwo.sq_injective (by simpa using he))
  let N := primeToResidual 3 (rankOneBorel F)
  have hdiag (c : Fˣ) : borelDiagonalHom c ∈ N := by
    apply mem_primeToResidual_of_pow (n := 1)
    have hc : c ^ 3 = 1 := hcard ▸ pow_card_eq_one'
    simpa using congrArg (borelDiagonalHom (F := F)) hc
  have hu (t : F) : (⟨Matrix.SpecialLinearGroup.transvection zero_ne_one t, upper_mem_rankOneBorel t⟩ :
      rankOneBorel F) ∈ N := by
    let v : rankOneBorel F :=
      ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one (t / ((b : F)^2 - 1)), upper_mem_rankOneBorel _⟩
    have hc : ⁅borelDiagonalHom b, v⁆ ∈ N := by
      simpa only [commutatorElement_def, mul_assoc] using
        N.mul_mem (hdiag b) ((inferInstance : N.Normal).conj_mem _ (N.inv_mem (hdiag b)) v)
    have he : ⁅borelDiagonalHom b, v⁆ =
        ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one t, upper_mem_rankOneBorel t⟩ := by
      apply Subtype.ext
      exact commutator_diag2_transvection (b : F) b.ne_zero _ t
        (div_mul_cancel₀ t (sub_ne_zero_of_ne hbsq)).symm
    exact he ▸ hc
  apply top_unique
  intro g _
  obtain ⟨t, c, hc, he⟩ := rankOneBorel_factor g
  have hg : g = ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one t, upper_mem_rankOneBorel t⟩ *
      borelDiagonalHom (Units.mk0 c hc) := Subtype.ext he
  rw [hg]
  exact N.mul_mem (hu t) (hdiag _)

omit [Group.IsPerfect L] in
private theorem residual_borel_lift [Finite L] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (g : rankOneBorel F) :
    ∃ l ∈ blockBorelResidual model, blockLinearMap model l = g := by
  let f : blockBorel model →* rankOneBorel F :=
    { toFun l := ⟨blockLinearMap model l, l.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' l m := Subtype.ext (map_mul (blockLinearMap model) (l : L) (m : L)) }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨l, hl⟩ := blockLinearMap_surjective model g
    exact ⟨⟨l, show blockLinearMap model l ∈ rankOneBorel F from hl.symm ▸ g.property⟩,
      Subtype.ext hl⟩
  let N := (primeToResidual 3 (blockBorel model)).map f
  have : N.Normal := Subgroup.Normal.map inferInstance f hf
  have hN : primeToResidual 3 (rankOneBorel F) ≤ N :=
    primeToResidual_le N (residual_index_coprime.coprime_dvd_right
      ((primeToResidual 3 (blockBorel model)).index_map_dvd hf))
  have hg : g ∈ N := hN (by rw [borel_residual hF]; trivial)
  obtain ⟨l, hl, he⟩ := hg
  exact ⟨l, mem_map_of_mem _ hl, congrArg Subtype.val he⟩

omit [Group.IsPerfect L] in
/-- A direct restriction argument for the natural cocycle: the nontrivial
diagonal has no fixed vector, and the Weyl element conjugates the root groups. -/
private theorem natural_zero_of_borel_zero [CharP F 2] [Finite F] (hF : Nat.card F = 4)
    (f : Matrix.SpecialLinearGroup (Fin 2) F → (Fin 2 → F))
    (hmul : ∀ g h, f (g * h) = g.val *ᵥ f h + f g)
    (hB : ∀ g ∈ rankOneBorel F, f g = 0) : ∀ g, f g = 0 := by
  classical
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, hb⟩ := exists_ne (1 : Fˣ)
  have hb1 : (b : F) ≠ 1 := by simpa using hb
  let w : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩
  have hw : f w = 0 := by
    have he : diag2 (b : F) b.ne_zero * w =
        w * diag2 (b : F)⁻¹ (inv_ne_zero b.ne_zero) := by
      apply Subtype.ext
      change (diag2 (b : F) b.ne_zero).val * !![0, 1; 1, 0] =
        !![0, 1; 1, 0] * (diag2 (b : F)⁻¹ (inv_ne_zero b.ne_zero)).val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diag2_coe', Matrix.mul_apply, Fin.sum_univ_two]
    have hh := congrArg f he
    rw [hmul, hmul, hB _ (diag_mem_rankOneBorel _ _),
      hB _ (diag_mem_rankOneBorel _ _), mulVec_zero, add_zero, zero_add] at hh
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    simp [diag2_coe', mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hv0 : f w 0 = 0 := by
      have hz : ((b : F) - 1) * f w 0 = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h0
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hb1)
    have hv1 : f w 1 = 0 := by
      have hz : ((b : F)⁻¹ - 1) * f w 1 = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h1
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (inv_ne_one.mpr hb1))
    ext i
    fin_cases i <;> assumption
  have hlower (x : F) : f (Matrix.SpecialLinearGroup.transvection one_ne_zero x) = 0 := by
    have he : w * Matrix.SpecialLinearGroup.transvection zero_ne_one x = Matrix.SpecialLinearGroup.transvection one_ne_zero x * w := by
      apply Subtype.ext
      change !![0, 1; 1, 0] * (Matrix.SpecialLinearGroup.transvection zero_ne_one x).val =
        (Matrix.SpecialLinearGroup.transvection one_ne_zero x).val * !![0, 1; 1, 0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [transvection_coe, Matrix.mul_apply, Fin.sum_univ_two]
    have hh := congrArg f he
    simpa only [hmul, hB _ (upper_mem_rankOneBorel x), hw, mulVec_zero,
      add_zero, zero_add] using hh.symm
  intro g
  apply Matrix.SL2.transvection_induction (fun g => f g = 0) ?_ ?_ g
  · intro i j hij x
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hB _ (upper_mem_rankOneBorel x)
    · exact hlower x
    · exact (hij rfl).elim
  · intro g h hg hh
    rw [hmul, hg, hh, mulVec_zero, add_zero]

private theorem vector_zero [Finite L] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (hfixB : ∀ x ∈ blockBorelResidual model, a x = x) (l : L) :
    vector model a hfixU l = 0 := by
  let s := Function.surjInv (blockLinearMap_surjective model)
  let f := fun g => vector model a hfixU (s g)
  have hs (g) : blockLinearMap model (s g) = g := Function.surjInv_eq _ g
  have hval (g) (x : L) (hx : blockLinearMap model x = g) :
      f g = vector model a hfixU x :=
    vector_eq_of_linear_eq model a hfixU ((hs g).trans hx.symm)
  have hf (g h) : f (g * h) = g.val *ᵥ f h + f g := by
    rw [hval (g * h) (s g * s h) (by rw [map_mul, hs, hs]), vector_mul]
    rw [hs]
  have hB (g) (hg : g ∈ rankOneBorel F) : f g = 0 := by
    obtain ⟨x, hx, he⟩ := residual_borel_lift model hF ⟨g, hg⟩
    rw [hval g x he]
    have hd : delta model a hfixU x = 1 := by
      apply Subtype.ext
      exact mul_inv_eq_one.mpr (hfixB x hx)
    simp [vector, hd]
  rw [← hval (blockLinearMap model l) l rfl]
  exact natural_zero_of_borel_zero hF f hf hB _

include hfixU in
/-- Pointwise fixation of the elementary layer and the Borel residual kills
every automorphism of the marked natural block. -/
public theorem automorphism_eq_one_of_blockU_and_borelResidual_fixed
    [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (hshort : ChapterC.IsShort L)
    (hfixB : ∀ x ∈ blockBorelResidual model, a x = x) : a = 1 := by
  let := hshort.finite
  have hc (l : L) : a l * l⁻¹ ∈ center L := by
    have hv := vector_zero model a hfixU hF hfixB l
    have hm : model.moduleIso
        (QuotientGroup.mk' (ChapterC.blockFixed L) (delta model a hfixU l)) = 1 :=
      Multiplicative.toAdd.injective hv
    have hq : QuotientGroup.mk' (ChapterC.blockFixed L) (delta model a hfixU l) = 1 :=
      model.moduleIso.injective (hm.trans model.moduleIso.map_one.symm)
    have hmem : delta model a hfixU l ∈ ChapterC.blockFixed L :=
      (QuotientGroup.eq_one_iff _).mp hq
    exact hmem
  let q := QuotientGroup.mk' (center L)
  have he := PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    q (by rw [QuotientGroup.ker_mk']) a.toMonoidHom (MonoidHom.id L)
    (by
      ext l
      change q (a l) = q l
      apply QuotientGroup.eq_iff_div_mem.mpr
      simpa only [div_eq_mul_inv] using hc l)
  ext l
  exact congrArg (fun f : L →* L => f l) he
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo
