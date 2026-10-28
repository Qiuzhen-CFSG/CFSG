module

public import Theory.SpecificGroups.BinaryLinear.PointStabilizerPerfect
public import Theory.SpecificGroups.BinaryLinear.LineRadical
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Orders
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Point-parabolic sections in small binary linear groups

The full point stabilizer has trivial centralizer in dimension at least
three. Its line radical is self-centralizing, and conjugacy of its nonidentity
transvections excludes a nonidentity element centralizing the whole stabilizer.

In GL₄(2) and GL₅(2), a proper Sylow overgroup whose order is divisible by
the point-parabolic order has at most that order. The flag-overgroup theorem
reduces this to subspace stabilizers; the middle four-space stabilizer has
order 576, and a factor five in dimension five forces an endpoint.
Consequently a Sylow-normalized subgroup surjecting onto the full point
parabolic contains that Sylow and the surjection is injective. The final
kernel comparison retains the given homomorphisms.

Source: Aschbacher--Smith, 12.9.6, printed pp.861--862. The original
natural-module application is LocalControl/MatchingBinary.lean.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.PointParabolicSection
open OuterCyclic SmallParabolicLevi SylowFlagOvergroups InvariantNodeActions

/-- The full point parabolic has trivial ambient centralizer. -/
theorem point_centralizer_eq_bot {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (hd : 3 ≤ Module.finrank (ZMod 2) E)
    (W : Submodule (ZMod 2) E) (hW : Module.finrank (ZMod 2) W = 1) :
    centralizer (parabolic W : Set (BinaryLinear.GL E)) = ⊥ := by
  classical
  have hW0 : W ≠ ⊥ := by intro he; rw [he] at hW; simp at hW
  have hWt : W ≠ ⊤ := by intro he; rw [he,finrank_top] at hW; omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have he : W = Submodule.span (ZMod 2) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hW hv hv0
  apply eq_bot_iff.mpr
  intro g hg
  by_contra hg1
  have hgR : g ∈ radical W :=
    centralizer_radical_le hW0 hWt ((centralizer_le (radical_le_parabolic W)) hg)
  obtain ⟨f,hf,hfv,hgf⟩ := exists_transvection_of_mem_line_radical hv0 (he ▸ hgR) hg1
  have hge : g = transvection v f hfv := LinearEquiv.ext hgf
  have hR : radical W ≤ zpowers g := by
    intro t ht
    by_cases ht1 : t = 1
    · exact ht1 ▸ one_mem _
    obtain ⟨c,hcv,hct⟩ := LineRadical.conjugate_fixing_center v hv0 f hf hfv (he ▸ ht) ht1
    have hc : c ∈ parabolic W := by
      rw [he]
      intro x
      constructor
      · intro hx
        obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx
        exact Submodule.mem_span_singleton.mpr ⟨a,c.injective (by simpa [hcv] using ha)⟩
      · intro hx
        obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
        simpa [map_smul,hcv] using Submodule.smul_mem
          (Submodule.span (ZMod 2) {v}) a (Submodule.mem_span_singleton_self v)
    have ht : t = g := by
      rw [← hct,← hge, hg c hc,mul_inv_cancel_right]
    exact ht ▸ mem_zpowers g
  have hc := card_dvd_of_le hR
  rw [he,LineRadical.card v hv0,Nat.card_zpowers] at hc
  have hg2 : g ^ 2 = 1 := by
    let := LineRadical.elementary v
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (radical (Submodule.span (ZMod 2) {v}))) ⟨g,he ▸ hgR⟩
    exact congrArg Subtype.val hh
  have hdvd : 2 ^ (Module.finrank (ZMod 2) E - 1) ∣ 2 :=
    hc.trans (orderOf_dvd_of_pow_eq_one hg2)
  have hlo : 4 ≤ 2 ^ (Module.finrank (ZMod 2) E - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ Module.finrank (ZMod 2) E - 1)
  have := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  omega

private theorem linear_card (d : ℕ) :
    Nat.card (LinearGroup d) = ∏ i : Fin d, (2^d - 2^i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear d).toEquiv, Matrix.card_GL_field]
  simp

/-- The hyperplane stabilizer has the same order as the point stabilizer. -/
theorem hyperplane_card {d : ℕ} (hd : d = 4 ∨ d = 5)
    (W : Submodule (ZMod 2) (Space d)) (hW : Module.finrank (ZMod 2) W = d-1) :
    Nat.card (parabolic W) = 2^(d-1) * Nat.card (LinearGroup (d-1)) := by
  have hWt : W ≠ ⊤ := by intro he; rw [he,finrank_top,Module.finrank_fin_fun] at hW; omega
  obtain ⟨f,hf,hWf⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hWt)
  have he : W = f.ker := Submodule.eq_of_le_of_finrank_eq hWf (by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    rw [Module.finrank_fin_fun] at hh
    omega)
  have hW0 : W ≠ ⊥ := by intro hz; rw [hz] at hW; simp at hW; omega
  obtain ⟨v,hv,hm⟩ := graph_hyperplaneRadical hd f hf
  have hp : (parabolic W).map (graphLinear d).toMonoidHom =
      parabolic (Submodule.span (ZMod 2) {v}) := by
    rw [← normalizer_radical hW0,map_equiv_normalizer_eq,he]
    change normalizer ((hyperplaneRadical d f).map (graphLinear d).toMonoidHom : Set (LinearGroup d)) = _
    rw [hm]
    exact normalizer_radical (mt Submodule.span_singleton_eq_bot.mp hv)
  have hc := Nat.card_congr ((graphLinear d).subgroupMap (parabolic W)).toEquiv
  change Nat.card (parabolic W) = Nat.card ((parabolic W).map (graphLinear d).toMonoidHom) at hc
  rw [hc,hp,
    PointStabilizerPerfect.parabolic_card _ (finrank_span_singleton hv),Module.finrank_fin_fun]

/-- The full point-parabolic order bounds a proper Sylow overgroup that it divides. -/
theorem proper_sylow_overgroup_card_le {d : ℕ} (hd : d = 4 ∨ d = 5)
    (S : Sylow 2 (LinearGroup d)) (B : Subgroup (LinearGroup d))
    (hSB : (S : Subgroup (LinearGroup d)) ≤ B) (hBt : B ≠ ⊤)
    (hdiv : 2^(d-1) * Nat.card (LinearGroup (d-1)) ∣ Nat.card B) :
    Nat.card B ≤ 2^(d-1) * Nat.card (LinearGroup (d-1)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  obtain ⟨b,cuts,_,he⟩ := exists_flag_of_sylow_le S B hSB
  have hne : cuts.Nonempty := by
    by_contra hh
    have hz := Set.not_nonempty_iff_eq_empty.mp hh
    apply hBt
    rw [he,hz]
    ext g
    simp [mem_cutStabilizer]
  obtain ⟨i,hi⟩ := hne
  let W := cutSpace b i
  have hBW : B ≤ parabolic W := by
    rw [he]
    intro g hg
    exact (mem_cutStabilizer b cuts g).mp hg i hi
  have hW := cutSpace_finrank b i
  have hW0 : W ≠ ⊥ := by intro hz; change Module.finrank (ZMod 2) W = _ at hW; rw [hz] at hW; simp at hW
  have hWt : W ≠ ⊤ := by
    intro hz
    change Module.finrank (ZMod 2) W = _ at hW
    rw [hz,finrank_top,Module.finrank_fin_fun] at hW
    have := i.isLt
    omega
  have hend : Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = k := by
    rcases hd with hd | hd
    · have hk : k = 3 := by omega
      subst k
      have hdvd := hdiv.trans (card_dvd_of_le hBW)
      have hi' := i.isLt
      fin_cases i
      · exact Or.inl hW
      · rw [FourParabolicAction.twoSpace_parabolic_card W (by simp) hW,linear_card] at hdvd
        norm_num [Fin.prod_univ_succ] at hdvd
      · exact Or.inr hW
    · have hk : k = 4 := by omega
      subst k
      apply (FiveFlagGeometry.GeometricFlags.invariant_subspaces_of_five_dvd B ?_).1 W hW0 hWt hBW
      apply dvd_trans (b := 2^(5-1) * Nat.card (LinearGroup (5-1))) ?_ hdiv
      rw [linear_card]
      norm_num [Fin.prod_univ_succ]
  have hc : Nat.card (parabolic W) = 2^k * Nat.card (LinearGroup k) := by
    rcases hend with h1 | hk
    · simpa using PointStabilizerPerfect.parabolic_card W h1
    · simpa using hyperplane_card hd W (by simpa using hk)
  simpa using (Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hBW)).trans_eq hc

private instance (d : ℕ) : Finite (LinearGroup d) :=
  Finite.of_injective (fun g : LinearGroup d => (g : Space d → Space d)) DFunLike.coe_injective

private theorem point_order_pos {d : ℕ} (hd : d = 4 ∨ d = 5) :
    1 < 2^(d-1) * Nat.card (LinearGroup (d-1)) := by
  rw [linear_card]
  rcases hd with rfl | rfl <;> norm_num [Fin.prod_univ_succ]

private theorem point_order_ne_full {d : ℕ} (hd : d = 4 ∨ d = 5) :
    Nat.card (LinearGroup d) ≠ 2^(d-1) * Nat.card (LinearGroup (d-1)) := by
  rw [linear_card,linear_card]
  rcases hd with rfl | rfl <;> norm_num [Fin.prod_univ_succ]

/-- A normalized section of full point-parabolic order has no kernel and contains the Sylow. -/
theorem section_injective {d : ℕ} (hd : d = 4 ∨ d = 5)
    (S : Sylow 2 (LinearGroup d)) (B : Subgroup (LinearGroup d))
    (hn : (S : Subgroup (LinearGroup d)) ≤ normalizer (B : Set (LinearGroup d)))
    {P : Type*} [Group P] (f : B →* P) (hf : Function.Surjective f)
    (hP : Nat.card P = 2^(d-1) * Nat.card (LinearGroup (d-1))) :
    Function.Injective f ∧ (S : Subgroup (LinearGroup d)) ≤ B := by
  have hpos : 1 < Nat.card P := hP.symm ▸ point_order_pos hd
  let : Finite P := Finite.of_surjective f hf
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) :=
    Atlas.psl_simple_high_rank d (by omega)
  let : IsSimpleGroup (LinearGroup d) := (projectiveEquivLinear (by omega : 0<d)).symm.isSimpleGroup
  have hBt : B ≠ ⊤ := by
    intro ht
    let e : B ≃* LinearGroup d := (MulEquiv.subgroupCongr ht).trans topEquiv
    let : IsSimpleGroup B := e.isSimpleGroup
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hk | hk
    · have hi := (MonoidHom.ker_eq_bot_iff f).mp hk
      have hc := Nat.card_congr (MulEquiv.ofBijective f ⟨hi,hf⟩).toEquiv
      rw [Nat.card_congr e.toEquiv,hP] at hc
      exact point_order_ne_full hd hc
    · have hz : ∀ x : P, x = 1 := by
        intro x
        obtain ⟨b,rfl⟩ := hf x
        change b ∈ f.ker
        rw [hk]
        exact mem_top b
      let : Subsingleton P := ⟨fun x y => (hz x).trans (hz y).symm⟩
      have hc : Nat.card P = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,⟨1⟩⟩
      omega
  have hB0 : B ≠ ⊥ := by
    intro hb
    have hle := Nat.card_le_card_of_surjective f hf
    rw [hb,card_bot] at hle
    omega
  have hJt : B ⊔ (S : Subgroup (LinearGroup d)) ≠ ⊤ := by
    intro ht
    have hN : B.Normal := normalizer_eq_top_iff.mp (top_unique (ht ▸ sup_le B.le_normalizer hn))
    exact (hN.eq_bot_or_eq_top).elim hB0 hBt
  have hdiv := hP ▸ card_dvd_of_surjective f hf
  have hle := proper_sylow_overgroup_card_le hd S (B ⊔ (S : Subgroup (LinearGroup d))) le_sup_right hJt
    (hdiv.trans (card_dvd_of_le (show B ≤ B ⊔ (S : Subgroup (LinearGroup d)) from le_sup_left)))
  have hcard : Nat.card (B ⊔ (S : Subgroup (LinearGroup d)) : Subgroup (LinearGroup d)) ≤ Nat.card B :=
    hle.trans (Nat.le_of_dvd Nat.card_pos hdiv)
  have he : B = B ⊔ (S : Subgroup (LinearGroup d)) := eq_of_le_of_card_ge le_sup_left hcard
  refine ⟨(hf.bijective_of_nat_card_le ?_).1,he.symm ▸ le_sup_right⟩
  rw [hP,he]
  exact hle

/-- Factorization through a normalized binary image forces equality of the original kernels. -/
theorem section_kernel_eq {A : Type*} [Group A] [Finite A]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (S : Sylow 2 (LinearGroup d))
    (g : A →* LinearGroup d) (hn : (S : Subgroup (LinearGroup d)) ≤ normalizer (g.range : Set (LinearGroup d)))
    {P : Type*} [Group P] (f : A →* P) (hf : Function.Surjective f)
    (hk : g.ker ≤ f.ker)
    (hP : Nat.card P = 2^(d-1) * Nat.card (LinearGroup (d-1))) :
    f.ker = g.ker ∧ (S : Subgroup (LinearGroup d)) ≤ g.range := by
  let e := QuotientGroup.quotientKerEquivRange g
  let b := (QuotientGroup.lift g.ker f hk).comp e.symm.toMonoidHom
  have hb : Function.Surjective b :=
    (QuotientGroup.lift_surjective_of_surjective g.ker f hf hk).comp e.symm.surjective
  obtain ⟨hi,hs⟩ := section_injective hd S g.range hn b hb hP
  refine ⟨le_antisymm ?_ hk,hs⟩
  intro x hx
  have he : b (g.rangeRestrict x) = f x := by
    change QuotientGroup.lift g.ker f hk (e.symm (e (QuotientGroup.mk' g.ker x))) = f x
    rw [e.symm_apply_apply]
    rfl
  have hz : g.rangeRestrict x = 1 := hi (he.trans (hx.trans b.map_one.symm))
  exact congrArg Subtype.val hz

end BinaryLinear.PointParabolicSection
