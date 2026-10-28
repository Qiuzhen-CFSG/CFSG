module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.CentralizerGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Basic
public import Theory.GroupTheory.NormalSymmetricThreeMarked

/-!
# The marked seed collapses a normal singleton S₃ factor

A normal S₃ with a moved binary plane realizes every invertible operator on
that plane. Its ambient centralizer therefore fixes the plane pointwise.
The actual Sylow-normalized, two-perfect Lᵥ* has order dividing 3 times a
power of two, so the normal-S₃ alternative puts it in the cubic residual
or in the factor's centralizer. The marked nonzero commutator of 13.6.11
rules out the latter possibility.

The marking reconstructs z in ⟨v⟩[z,Lᵥ]. Hence z lies in the join of the
central v-line and the normal moved plane. All of Uᵥ = ⟨z^{Gᵥ}⟩ lies in
that join. Every ambient star action agrees with an S₃ element on the
plane, and both fix v, so faithfulness makes the normal S₃ the whole star
group. The native applications can consequently use an actual global
maximum without any extension splitting or quotient-lifting hypothesis.

The needed cubic quotient |Lᵥ/O₂(Lᵥ)| = 3 is the earlier local fact on
p.926. `A5Module.FlagMarking.residualQuotient_card` proves it from the same
flag's action kernel; the parent NativeThree module supplies that consumer.
No characteristic-two theorem or later solvable exclusion is required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.926 and 929, especially the seed argument in 13.6.11–13 and B.5.6(3).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
variable {D M : Type*} [Group D] [Finite D] [AddCommGroup M] [Module (ZMod 2) M]
private theorem plane_covers (ρ : Representation (ZMod 2) D M)
    (hf : Function.Injective ρ) (H : Subgroup D) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp H.subtype)) = 2)
    (b : D) : ∃ h : H, Representation.toCoinvariantsKer ρ H h =
      Representation.toCoinvariantsKer ρ H b := by
  let W := Coinvariants.ker (ρ.comp H.subtype)
  let σ := Representation.toCoinvariantsKer ρ H
  have hs := BinaryPlaneNormalizer.symmetric_three_split
    (ρ.comp H.subtype) (hf.comp H.subtype_injective) e hd
  have hfaith : Function.Injective (σ.comp H.subtype) := by
    intro x y h
    apply H.subtype_injective
    apply hf
    ext t
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp
      (show t ∈ W ⊔ (Representation.invariants (ρ.comp H.subtype)) from hs.sup_eq_top ▸ Submodule.mem_top)
    have he := congrArg Subtype.val (LinearMap.congr_fun h (⟨w, hw⟩ : W))
    change ρ (x : D) w = ρ (y : D) w at he
    change ρ (x : D) (w + c) = ρ (y : D) (w + c)
    rw [map_add, map_add, he]
    exact congrArg (fun t => ρ (y : D) w + t) ((hc x).trans (hc y).symm)
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := W) (by
    change 0 < Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp H.subtype))
    omega)
  let basis := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let f : H →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom (σ.comp H.subtype))
  have hinj : Function.Injective f := by
    intro x y h
    exact hfaith (congrArg Units.val ((Matrix.GeneralLinearGroup.toLin' basis).symm.injective h))
  have hc : Nat.card H = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Fin.prod_univ_succ]
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hc⟩).surjective
  obtain ⟨h, hh⟩ := hsurj ((Matrix.GeneralLinearGroup.toLin' basis).symm (σ.asGroupHom b))
  have heq : σ h = σ b := congrArg Units.val
    ((Matrix.GeneralLinearGroup.toLin' basis).symm.injective hh)
  exact ⟨h, heq⟩

private theorem fixes_moved (ρ : Representation (ZMod 2) D M)
    (hf : Function.Injective ρ) (H : Subgroup D) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp H.subtype)) = 2)
    (b : D) (hb : b ∈ centralizer (H : Set D))
    (w : Coinvariants.ker (ρ.comp H.subtype)) : ρ b w = w := by
  let σ := Representation.toCoinvariantsKer ρ H
  have hs := BinaryPlaneNormalizer.symmetric_three_split
    (ρ.comp H.subtype) (hf.comp H.subtype_injective) e hd
  have hfaith : Function.Injective (σ.comp H.subtype) := by
    intro x y h
    apply H.subtype_injective
    apply hf
    ext t
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp
      (show t ∈ Coinvariants.ker (ρ.comp H.subtype) ⊔ (Representation.invariants (ρ.comp H.subtype))
        from hs.sup_eq_top ▸ Submodule.mem_top)
    have he := congrArg Subtype.val (LinearMap.congr_fun h ⟨w, hw⟩)
    change ρ (x : D) w = ρ (y : D) w at he
    change ρ (x : D) (w + c) = ρ (y : D) (w + c)
    rw [map_add, map_add, he]
    exact congrArg (fun t => ρ (y : D) w + t) ((hc x).trans (hc y).symm)
  obtain ⟨h, heq⟩ := plane_covers ρ hf H e hd b
  have hcentral : ∀ a : H, h * a = a * h := by
    intro a
    apply hfaith
    change σ ((h : D) * a) = σ ((a : D) * h)
    rw [map_mul, map_mul, heq, ← map_mul, ← map_mul, hb a a.property]
  have hperm : e h = 1 := by
    have hh : ∀ x : Equiv.Perm (Fin 3),
        (∀ y, x * y = y * x) → x = 1 := by decide +kernel
    apply hh
    intro y
    simpa only [map_mul, e.apply_symm_apply] using congrArg e (hcentral (e.symm y))
  have hh1 : h = 1 := e.injective (hperm.trans e.map_one.symm)
  have hσ : σ b = 1 := by rw [← heq, hh1]; exact σ.map_one
  exact congrArg Subtype.val (LinearMap.congr_fun hσ w)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem moved_coinvariants (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) :
    subspaceCommutator (starRepresentation z v) ⊤ H =
      Coinvariants.ker ((starRepresentation z v).comp H.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨g, hg, u, _, rfl⟩
    exact ⟨(⟨g, hg⟩, u), rfl⟩
  · rintro ⟨⟨g, u⟩, rfl⟩
    exact ⟨g, g.property, u, Submodule.mem_top, rfl⟩
private theorem moved_finrank (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) (hcard : Nat.card (movedSubgroup z v H) = 4) :
    Module.finrank (ZMod 2) (Coinvariants.ker ((starRepresentation z v).comp H.subtype)) = 2 := by
  have hc : Nat.card (Coinvariants.ker ((starRepresentation z v).comp H.subtype)) = 4 := by
    rw [← moved_coinvariants, ← ambientSpace_card, moved_ambientSpace, hcard]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc

private theorem centralizes_moved (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4)
    (B : Subgroup G) (hBG : B ≤ Gv v)
    (hc : starImage z v B ≤ centralizer (H : Set (Gstar z v))) :
    B ≤ centralizer (movedSubgroup z v H : Set G) := by
  intro b hb w hw
  let b' : Gv v := ⟨b, hBG hb⟩
  let w' : Uv z v := ⟨w, movedSubgroup_le_Uv z v H hw⟩
  have hW : Additive.ofMul w' ∈ Coinvariants.ker ((starRepresentation z v).comp H.subtype) := by
    rw [← moved_coinvariants]
    apply (mem_ambientSpace z v _ w').mp
    rwa [moved_ambientSpace]
  have hf := fixes_moved (starRepresentation z v) (starRepresentation_injective z v)
    H e (moved_finrank z v H hcard) (starMk z v b') (hc ⟨b', hb, rfl⟩) ⟨_, hW⟩
  have he := congrArg (fun u : Additive (Uv z v) => (u.toMul : G)) hf
  change ((starRepresentation z v (starMk z v b') (Additive.ofMul w')).toMul : G) = w at he
  rw [starRepresentation_mk_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem starLv_le (L T : Subgroup G) {V : Subgroup G} (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s))
    (H : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (hXH : X ≤ H) (hcard : Nat.card (movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) H) = 4) :
    starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)) ≤ H := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  obtain ⟨P, hP⟩ := FactorArgument.exists_starSylow T z v S hS
  have hn : (P : Subgroup (Gstar z v)) ≤ normalizer (starImage z v (Lv L v) : Set _) := by
    rw [hP]
    exact FactorArgument.starTv_normalizes_starLv L T z v hL
  rcases Theory.GroupTheory.NormalSymmetricThreeMarked.eq_residual_or_centralizes_of_card_dvd
    H e P (starImage z v (Lv L v)) (FactorArgument.starLv_twoPerfect L z v) hn
    (FactorArgument.starLv_card_dvd L z v hcubic) with he | hc
  · rw [he]
    exact map_subtype_le _
  · have hcent := centralizes_moved z v H e hcard (Lv L v) (Lv_le_Gv L v) hc
    have hne := (marked_Xz_commutators_ne_bot s T S hS hfix
      (XFamily_subset_Xz L T z v hX)).2
    apply False.elim
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (UX_le_moved L z v X).trans
    exact (commutator_mono le_rfl (map_mono (comap_mono hXH))).trans
      (le_centralizer_iff.mp hcent)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
variable {G : Type*} [Group G] [Finite G]
private theorem seed_span (L : Subgroup G) {V : Subgroup G} (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (H : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))) [H.Normal]
    (hLH : starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)) ≤ H) :
    Uv (A5Module.markedZ s) (A5Module.markedV s) ≤
      zpowers (A5Module.markedV s) ⊔ movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) H := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  have hpre : Lv L v ≤ starPreimage z v H := by
    intro a ha
    let a' : Gv v := ⟨a, Lv_le_Gv L v ha⟩
    exact ⟨a', hLH ⟨a', ha, rfl⟩, rfl⟩
  have hz : z ∈ zpowers v ⊔ movedSubgroup z v H :=
    (sup_le_sup_left (commutator_mono (zpowers_le.mpr (z_mem_Uv z v)) hpre) _)
      (marked_seed_mem_line_sup_commutator s)
  apply conjugateSpanBy_le (zpowers_le.mpr hz)
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup]
  have hv : (zpowers v).map (MulAut.conj g : G →* G) = zpowers v := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)
  have hw : (movedSubgroup z v H).map (MulAut.conj g : G →* G) = movedSubgroup z v H := by
    change (⁅Uv z v, starPreimage z v H⁆).map _ = _
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Gv_normalizes_Uv z v hg),
      mem_normalizer_iff_map_conj_eq.mp (starPreimage_normalized z v H hg)]
    rfl
  rw [hv, hw]
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem central_vector_fixed (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (hv : v ∈ Uv z v) (a : Gstar z v) :
    starRepresentation z v a (Additive.ofMul (⟨v, hv⟩ : Uv z v)) =
      Additive.ofMul (⟨v, hv⟩ : Uv z v) := by
  obtain ⟨g, rfl⟩ := starMk_surjective z v a
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [starRepresentation_mk_apply]
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)

private theorem top_of_seed_span (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (hv : v ∈ Uv z v) (H : Subgroup (Gstar z v)) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3)) (hcard : Nat.card (movedSubgroup z v H) = 4)
    (hgen : Uv z v ≤ zpowers v ⊔ movedSubgroup z v H) : H = ⊤ := by
  apply top_unique
  intro a _
  let ρ := starRepresentation z v
  obtain ⟨h, he⟩ := plane_covers ρ (starRepresentation_injective z v) H e
    (moved_finrank z v H hcard) a
  have heq : ρ a = ρ h := by
    let K := LinearMap.ker (ρ a - ρ h)
    have hline : zpowers v ≤ ambientSpace z v K := by
      apply zpowers_le.mpr
      apply (mem_ambientSpace z v K (⟨v, hv⟩ : Uv z v)).mpr
      change ρ a (Additive.ofMul (⟨v, hv⟩ : Uv z v)) -
        ρ h (Additive.ofMul (⟨v, hv⟩ : Uv z v)) = 0
      rw [central_vector_fixed, central_vector_fixed, sub_self]
    have hW : movedSubgroup z v H ≤ ambientSpace z v K := by
      intro w hw
      let w' : Uv z v := ⟨w, movedSubgroup_le_Uv z v H hw⟩
      have hw' : Additive.ofMul w' ∈ Coinvariants.ker (ρ.comp H.subtype) := by
        rw [← moved_coinvariants]
        apply (mem_ambientSpace z v _ w').mp
        rwa [moved_ambientSpace]
      have hh := congrArg Subtype.val (LinearMap.congr_fun he ⟨_, hw'⟩)
      apply (mem_ambientSpace z v K w').mpr
      exact sub_eq_zero.mpr hh.symm
    apply LinearMap.ext
    intro u
    have hu := (mem_ambientSpace z v K u.toMul).mp
      ((hgen.trans (sup_le hline hW)) u.toMul.property)
    exact sub_eq_zero.mp hu
  have ha : a = (h : Gstar z v) := starRepresentation_injective z v heq
  exact ha.symm ▸ h.property
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
variable {G : Type*} [Group G] [Finite G]
/-- A normal marked S₃ containing a source X-family member is the entire
star group when its moved space is a plane. The cubic quotient is the
p.926 local fact, proved for the actual marked flag; no Thompson equality,
maximum-subgroup lifting or nonnormality conclusion is assumed. -/
theorem marked_normal_s3_eq_top {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s))
    (H : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (hXH : X ≤ H) (hcard : Nat.card (movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) H) = 4) :
    H = ⊤ := by
  have hLH := starLv_le L T s S hS hfix hL hcubic hX H e hXH hcard
  exact top_of_seed_span _ _ (Vv_le_Uv L _ _ (A5Module.markedV_mem_Vv s)) H e hcard
    (seed_span L s H hLH)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse

end
