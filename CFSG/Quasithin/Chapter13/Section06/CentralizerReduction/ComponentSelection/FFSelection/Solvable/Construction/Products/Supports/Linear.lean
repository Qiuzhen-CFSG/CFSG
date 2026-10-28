module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Supports.Singletons
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.Representation.FixedQuotientCoprime

/-!
# Lifting the two native S₃ quotient planes

The fixed-free cubics belong to the normal subgroup A₃ × A₃. The two
complementary quotient summands imply that this subgroup fixes exactly the
global fixed space. Averaging therefore makes the original moved space
disjoint from that fixed space. This proves dimension two upstairs, the
literal direct sum, and idempotence of each factor commutator.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3), printed p.105, and 13.6.13, printed p.929. The averaging argument
adapts Chapter15/.../SolvableProduct/Rank.lean to the native Chapter B records.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
private theorem cube_mem_alt : ∀ x : Equiv.Perm (Fin 3), x ^ 3 = 1 →
    x ∈ alternatingGroup (Fin 3) := by
  change ∀ x : Equiv.Perm (Fin 3), x ^ 3 = 1 → Equiv.Perm.sign x = 1
  decide +kernel

private theorem normal_nine {D : Type*} [Group D]
    (e : D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :
    ∃ N : Subgroup D, N.Normal ∧ Nat.card N = 9 ∧ ∀ x : D, x ^ 3 = 1 → x ∈ N := by
  let K := (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))
  let N := K.comap e.toMonoidHom
  have hmap : N.map e.toMonoidHom = K :=
    map_comap_eq_self_of_surjective e.surjective K
  have hc : Nat.card N = 9 := by
    rw [Nat.card_congr (N.equivMapOfInjective e.toMonoidHom e.injective).toEquiv, hmap,
      Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.card_eq_fintype_card]
    decide
  refine ⟨N, inferInstance, hc, ?_⟩
  intro x hx
  have he : e x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  exact ⟨cube_mem_alt (e x).1 (congrArg Prod.fst he),
    cube_mem_alt (e x).2 (congrArg Prod.snd he)⟩

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private theorem split_fixed_left {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (U X : Subrepresentation σ)
    (hd : Disjoint U.toSubmodule X.toSubmodule)
    {u x : W} (hu : u ∈ U) (hx : x ∈ X) (g : D)
    (hf : σ g (u + x) = u + x) : σ g u = u := by
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp hd _ (U.toSubmodule.sub_mem (U.apply_mem_toSubmodule g hu) hu)
  have he : σ g u - u = x - σ g x := by
    apply eq_sub_iff_add_eq.mpr
    calc
      (σ g u - u) + σ g x = σ g (u + x) - u := by rw [map_add]; abel
      _ = x := by rw [hf]; abel
  rw [he]
  exact X.toSubmodule.sub_mem hx (X.apply_mem_toSubmodule g hx)

private theorem images_fixed_le (U X : Subrepresentation ρ)
    (hs : IsCompl ((fixed ρ).quotientImage U).toSubmodule
      ((fixed ρ).quotientImage X).toSubmodule)
    (N : Subgroup D) (r s : N)
    (hr : ∀ v : ((fixed ρ).quotientImage U).toSubmodule,
      ((fixed ρ).quotientImage U).toRepresentation (r : D) v = v → v = 0)
    (hx : ∀ v : ((fixed ρ).quotientImage X).toSubmodule,
      ((fixed ρ).quotientImage X).toRepresentation (s : D) v = v → v = 0) :
    invariants (ρ.comp N.subtype) ≤ ρ.invariants := by
  intro v hv
  let q := (fixed ρ).toSubmodule.mkQ
  have hm : q v ∈ ((fixed ρ).quotientImage U).toSubmodule ⊔
      ((fixed ρ).quotientImage X).toSubmodule := by rw [hs.sup_eq_top]; trivial
  obtain ⟨u, hu, x, hxmem, he⟩ := Submodule.mem_sup.mp hm
  have hf (g : N) : (reducedAction ρ) (g : D) (u + x) = u + x := by
    rw [he]
    change q (ρ g v) = q v
    rw [show ρ g v = v from hv g]
  have hu0 : u = 0 := by
    have hh := split_fixed_left (reducedAction ρ) _ _ hs.disjoint hu hxmem (r : D) (hf r)
    exact congrArg Subtype.val (hr ⟨u, hu⟩ (Subtype.ext hh))
  have hx0 : x = 0 := by
    have hh := split_fixed_left (reducedAction ρ) _ _ hs.disjoint.symm hxmem hu (s : D)
      (by simpa only [add_comm] using hf s)
    exact congrArg Subtype.val (hx ⟨x, hxmem⟩ (Subtype.ext hh))
  change v ∈ (fixed ρ).toSubmodule
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change q v = 0
  rw [← he, hu0, hx0, add_zero]


private theorem moved_eq_coinvariants (A : Subgroup D) :
    moved ρ A = Coinvariants.ker (ρ.comp A.subtype) := by
  unfold moved subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g, hg, w, _, rfl⟩
    exact ⟨(⟨g, hg⟩, w), rfl⟩
  · rintro ⟨⟨g, w⟩, rfl⟩
    exact ⟨g, g.property, w, Submodule.mem_top, rfl⟩

/-- Averaging lifts both natural quotient planes to the original module. -/
theorem twoFactor_lift (c : SourceTwoFactorCase ρ)
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3)) :
    Disjoint (moved ρ ⊤) ρ.invariants ∧
      Module.finrank (ZMod 2) (moved ρ c.first) = 2 ∧
      Module.finrank (ZMod 2) (moved ρ c.second) = 2 := by
  obtain ⟨hm₁, hd₁, r, hr, hrf⟩ := factor_quotient_plane ρ c.firstCase e₁
  obtain ⟨hm₂, hd₂, s, hs, hsf⟩ := factor_quotient_plane ρ c.secondCase e₂
  let e := c.product.equiv.symm.trans (e₁.prodCongr e₂)
  let : Finite D := Finite.of_equiv _ e.toEquiv.symm
  obtain ⟨N, hN, hcard, hcube⟩ := normal_nine e
  let : N.Normal := hN
  let : Fintype N := Fintype.ofFinite N
  have hrN : (r : D) ∈ N := hcube r (by exact congrArg Subtype.val hr)
  have hsN : (s : D) ∈ N := hcube s (by exact congrArg Subtype.val hs)
  have hf : invariants (ρ.comp N.subtype) ≤ ρ.invariants :=
    images_fixed_le ρ c.firstSpace c.secondSpace c.decomposition N
      ⟨r, hrN⟩ ⟨s, hsN⟩ hrf hsf
  have hc : (Fintype.card N : ZMod 2) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    decide
  refine ⟨?_, ?_, ?_⟩
  · rw [moved_eq_coinvariants]
    exact disjoint_moved_invariants_of_normal_coprime ρ N hc hf ⊤
  · have heq := finrank_moved_eq_quotient_image_of_normal_coprime ρ N hc hf c.first
    rw [← moved_eq_coinvariants, ← hm₁] at heq
    exact (congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W)
      hm₁.symm).trans (heq.trans hd₁)
  · have heq := finrank_moved_eq_quotient_image_of_normal_coprime ρ N hc hf c.second
    rw [← moved_eq_coinvariants, ← hm₂] at heq
    exact (congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W)
      hm₂.symm).trans (heq.trans hd₂)

private theorem moved_mono {A B : Subgroup D} (hAB : A ≤ B) :
    moved ρ A ≤ moved ρ B := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, v, hv, rfl⟩
  exact ⟨a, hAB ha, v, hv, rfl⟩

/-- Both literal moved spaces are disjoint, span the whole moved space, and
are their own commutators with their corresponding factors. -/
theorem twoFactor_spaces [Module.Finite (ZMod 2) V]
    (c : SourceTwoFactorCase ρ)
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3)) :
    Disjoint (moved ρ c.first) (moved ρ c.second) ∧
    moved ρ ⊤ = moved ρ c.first ⊔ moved ρ c.second ∧
    subspaceCommutator ρ (moved ρ c.first) c.first = moved ρ c.first ∧
    subspaceCommutator ρ (moved ρ c.second) c.second = moved ρ c.second := by
  obtain ⟨hd, _, _⟩ := twoFactor_lift ρ c e₁ e₂
  have hm₁ := (factor_quotient_plane ρ c.firstCase e₁).1
  have hm₂ := (factor_quotient_plane ρ c.secondCase e₂).1
  have hd₁ := hd.mono_left (moved_mono ρ (A := c.first) le_top)
  have hd₂ := hd.mono_left (moved_mono ρ (A := c.second) le_top)
  refine ⟨?_, ?_, (factor_plane_of_disjoint ρ c.firstCase e₁ hd₁).1,
    (factor_plane_of_disjoint ρ c.secondCase e₂ hd₂).1⟩
  · apply Submodule.disjoint_def.mpr
    intro u hu₁ hu₂
    have hq : ρ.invariants.mkQ u = 0 :=
      Submodule.disjoint_def.mp c.decomposition.disjoint _
        ⟨u, hm₁.symm ▸ hu₁, rfl⟩ ⟨u, hm₂.symm ▸ hu₂, rfl⟩
    exact Submodule.disjoint_def.mp hd₁ u hu₁ ((Submodule.Quotient.mk_eq_zero _).mp hq)
  · apply le_antisymm _ (sup_le (moved_mono ρ le_top) (moved_mono ρ le_top))
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, u, _, rfl⟩
    obtain ⟨a, b, rfl⟩ := c.product.exists_mul g
    have hb : ρ (b : D) u - u ∈ c.secondSpace.toSubmodule := by
      rw [hm₂]
      exact Submodule.subset_span ⟨b, b.property, u, Submodule.mem_top, rfl⟩
    have ha : ρ (a : D) u - u ∈ moved ρ c.first :=
      Submodule.subset_span ⟨a, a.property, u, Submodule.mem_top, rfl⟩
    have hab : ρ (a : D) (ρ (b : D) u - u) ∈ moved ρ c.second :=
      hm₂ ▸ c.secondSpace.apply_mem_toSubmodule a hb
    have he : ρ ((a : D) * (b : D)) u - u =
        (ρ (a : D) u - u) + ρ (a : D) (ρ (b : D) u - u) := by
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    rw [he]
    exact Submodule.add_mem_sup ha hab

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
