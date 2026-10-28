module
public import Theory.Representation.UniformBinaryPolar
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.GroupTheory.CenterlessSupplementCentralizer
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source

/-!
# Marked Borel orbit and linear automorphism bounds

The actual normal component and Sylow supplement generate their overgroup.
Its quotient map onto the marked Borel model identifies the orbit of a seed
fixed by the overlap with the doubly transitive point set. Invariant binary
polar coefficients then bound its degree. The centerless component also makes
the two-core quotient act faithfully, transferring the PSL₂ automorphism
rank bound without a separate action hypothesis.

Source: Aschbacher–Smith 14.2.16, printed pp.985–986.
-/

public section
namespace BinaryBorelOrbit
variable {A P Ω W : Type*} [Group A] [Group P] [MulAction P Ω]
variable [AddCommGroup W] [Module (ZMod 2) W]

/-- A vector fixed by the inverse image of a point stabilizer has a well-defined
orbit indexed by that transitive point set. No faithfulness or equality of
stabilizers is needed. -/
theorem exists_orbit_map (π : A →* P) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) A W) (o : Ω) (v : W)
    (htrans : ∀ x : Ω, ∃ g : P, g • o = x)
    (hfix : ∀ a : A, π a • o = o → ρ a v = v) :
    ∃ b : Ω → W, (∀ a, b (π a • o) = ρ a v) ∧
      (∀ a x, b (π a • x) = ρ a (b x)) := by
  classical
  have hex (x : Ω) : ∃ a : A, π a • o = x := by
    obtain ⟨g,hg⟩ := htrans x
    obtain ⟨a,rfl⟩ := hπ g
    exact ⟨a,hg⟩
  let c (x : Ω) := (hex x).choose
  have hc (x : Ω) : π (c x) • o = x := (hex x).choose_spec
  let b (x : Ω) := ρ (c x) v
  have same (a d : A) (had : π a • o = π d • o) : ρ a v = ρ d v := by
    have hs : π (d⁻¹*a) • o = o := by
      rw [map_mul,map_inv,mul_smul,had,inv_smul_smul]
    have hh := congrArg (ρ d) (hfix (d⁻¹*a) hs)
    simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel_left] using hh
  have hb (a : A) : b (π a • o) = ρ a v := same _ _ (hc _)
  refine ⟨b,hb,?_⟩
  intro a x
  calc
    b (π a • x) = b (π (a*c x) • o) := by rw [map_mul,mul_smul,hc]
    _ = ρ (a*c x) v := hb _
    _ = ρ a (b x) := by rw [map_mul]; rfl

/-- Invariance on a doubly transitive point orbit makes every distinct-pair
coefficient equal, even when the orbit map has linear relations. -/
theorem orbit_pairing_constant
    (π : A →* P) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) A W)
    (B : LinearMap.BilinForm (ZMod 2) W)
    (hinv : ∀ a x y, B (ρ a x) (ρ a y) = B x y)
    (htwo : MulAction.IsMultiplyPretransitive P Ω 2)
    (b : Ω → W) (hb : ∀ a x, b (π a • x) = ρ a (b x))
    {i j i' j' : Ω} (hij : i ≠ j) (hij' : i' ≠ j') :
    B (b i) (b j) = B (b i') (b j') := by
  obtain ⟨g,hi,hj⟩ := MulAction.is_two_pretransitive_iff.mp htwo hij hij'
  obtain ⟨a,rfl⟩ := hπ g
  rw [←hi,←hj,hb,hb,hinv]

end BinaryBorelOrbit

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G P Ω W : Type*} [Group G] [Group P] [MulAction P Ω]
variable [AddCommGroup W] [Module (ZMod 2) W]

theorem ModelBorelPair.spanning_orbit
    (M K S : Subgroup G) [K.Normal] (hgen : K ⊔ S = ⊤) (hSM : S ≤ M)
    (o : Ω) (hm : ModelBorelPair M K (MulAction.stabilizer P o))
    (htrans : ∀ x : Ω, ∃ g : P, g • o = x)
    (ρ : Representation (ZMod 2) G W) (v : W)
    (hfix : ∀ g ∈ M, ρ g v = v)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : G => ρ g v)) = ⊤) :
    ∃ (π : K →* P) (b : Ω → W), Function.Surjective π ∧
      (∀ k, b (π k • o) = ρ k.val v) ∧
      (∀ k x, b (π k • x) = ρ k.val (b x)) ∧
      Submodule.span (ZMod 2) (Set.range b) = ⊤ := by
  obtain ⟨e,he⟩ := hm
  let q := QuotientGroup.mk' (sourceKernel M)
  let f : K →* sourceImage M K := (q.comp K.subtype).codRestrict _
    (fun k => mem_map_of_mem q k.property)
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨k,hk,rfl⟩ := hx
    exact ⟨⟨k,hk⟩,rfl⟩
  let π := e.toMonoidHom.comp f
  have hπ : Function.Surjective π := e.surjective.comp hf
  let ρK : Representation (ZMod 2) K W := ρ.comp K.subtype
  have hfixK (k : K) (hk : π k • o = o) : ρK k v = v := by
    have hp : π k ∈ MulAction.stabilizer P o := hk
    rw [←he] at hp
    obtain ⟨a,ha,heq⟩ := hp
    have hak : a = f k := e.injective heq
    rw [hak] at ha
    change q k.val ∈ sourceImage M (M ⊓ K) at ha
    obtain ⟨m,hm,heq⟩ := ha
    have hmk : m⁻¹*k.val ∈ sourceKernel M := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (m⁻¹*k.val) = 1
      rw [map_mul,map_inv,heq,inv_mul_cancel]
    have hkm : k.val ∈ M := by
      have hh := M.mul_mem hm.1 (M.normalCore_le hmk)
      simpa only [mul_inv_cancel_left] using hh
    exact hfix k.val hkm
  obtain ⟨b,hb,hbe⟩ := BinaryBorelOrbit.exists_orbit_map π hπ ρK o v htrans hfixK
  refine ⟨π,b,hπ,hb,hbe,?_⟩
  apply top_unique
  rw [←hspan]
  apply Submodule.span_mono
  rintro _ ⟨g,rfl⟩
  have hg : g ∈ K ⊔ S := hgen ▸ mem_top g
  obtain ⟨k,hk,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hg
  refine ⟨π ⟨k,hk⟩ • o,?_⟩
  rw [hb]
  change ρ k v = ρ (k*s) v
  rw [map_mul,Module.End.mul_apply,hfix s (hSM hs)]
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels


public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G P Ω W : Type*} [Group G] [Group P] [MulAction P Ω]
variable [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem ModelBorelPair.orbit_degree_bound [Finite Ω]
    (M K S : Subgroup G) [K.Normal] (hgen : K ⊔ S = ⊤) (hSM : S ≤ M)
    (o : Ω) (hm : ModelBorelPair M K (MulAction.stabilizer P o))
    (htwo : MulAction.IsMultiplyPretransitive P Ω 2)
    (ρ : Representation (ZMod 2) G W) (v : W)
    (hfix : ∀ g ∈ M, ρ g v = v)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : G => ρ g v)) = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 0)
    (m : ℕ) (hmE : finrank (ZMod 2) (W ⧸ E) ≤ m) : Nat.card Ω ≤ 2*m+1 := by
  classical
  let : Fintype Ω := Fintype.ofFinite Ω
  let : MulAction.IsMultiplyPretransitive P Ω 2 := htwo
  let : MulAction.IsPretransitive P Ω := MulAction.isPretransitive_of_is_two_pretransitive
  have htrans (x : Ω) : ∃ g : P, g • o = x := MulAction.exists_smul_eq P o x
  obtain ⟨π,b,hπ,hb,hbe,hsp⟩ := hm.spanning_orbit M K S hgen hSM o htrans ρ v hfix hspan
  let eΩ : Fin (Fintype.card Ω) ≃ Ω := (Fintype.equivFin Ω).symm
  let w (i : Fin (Fintype.card Ω)) := b (eΩ i)
  let f := Fintype.linearCombination (ZMod 2) w
  have hspw : Submodule.span (ZMod 2) (Set.range w) = ⊤ := by
    apply top_unique
    rw [←hsp]
    apply Submodule.span_mono
    rintro _ ⟨x,rfl⟩
    obtain ⟨i,rfl⟩ := eΩ.surjective x
    exact ⟨i,rfl⟩
  have hf : Function.Surjective f :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination (ZMod 2) w).mp hspw
  have hcoeff (i : Fin (Fintype.card Ω)) : f (Pi.single i 1) = b (eΩ i) := by simp [f,w]
  have hp (i j i' j' : Fin (Fintype.card Ω)) (hij : i ≠ j) (hij' : i' ≠ j') :
      B (f (Pi.single i 1)) (f (Pi.single j 1)) =
        B (f (Pi.single i' 1)) (f (Pi.single j' 1)) := by
    simp only [hcoeff]
    exact BinaryBorelOrbit.orbit_pairing_constant π hπ (ρ.comp K.subtype) B
      (fun k => hinv k.val) htwo b hbe (eΩ.injective.ne hij) (eΩ.injective.ne hij')
  have hh := UniformBinaryPolar.invariant_orbit_degree_bound B hB hne f hf hp E hE m hmE
  simpa only [Nat.card_eq_fintype_card] using hh

/-- The actual marked PSL₂ Borel restricts the binary field to orders four
and eight when G.2.3 bounds the elementary image by the field degree. -/
theorem ModelBorelPair.linear_field_degree
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (M K S : Subgroup G) [K.Normal] (hgen : K ⊔ S = ⊤) (hSM : S ≤ M)
    (f : ℕ) (hf : 1 < f) (hF : Nat.card F = 2^f)
    (hm : ModelBorelPair M K (BenderSuzuki.Converse.PBorel F))
    (ρ : Representation (ZMod 2) G W) (v : W)
    (hfix : ∀ g ∈ M, ρ g v = v)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : G => ρ g v)) = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 0)
    (hmE : finrank (ZMod 2) (W ⧸ E) ≤ f+1) : f=2 ∨ f=3 := by
  have hb := hm.orbit_degree_bound M K S hgen hSM (BenderSuzuki.Converse.pInf F)
    (BenderSuzuki.Converse.psl2_two_pretransitive (F := F)) ρ v hfix hspan B hB hne hinv E hE (f+1) hmE
  have hc : Nat.card (BenderSuzuki.Converse.P1 F) = 2^f+1 := by
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp),hF]
  exact UniformBinaryPolar.linear_field_degree f hf (hc ▸ hb)
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

/-- The literal two-core quotient acts faithfully on its centerless normal
PSL₂ factor, so the automorphism two-rank bounds every elementary image. -/
theorem ModelBorelPair.linear_actor_two_rank
    (S : Sylow 2 H) (N K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (S : Subgroup H) = ⊤) (hcore : sourceKernel N = pCore 2 H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair N K (BenderSuzuki.Converse.PBorel F)) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ n := by
  obtain ⟨e,_⟩ := hm
  let q := QuotientGroup.mk' (pCore 2 H)
  let L := K.map q
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have he : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    have transport (J J' : Subgroup H) [J.Normal] [J'.Normal] (heq : J = J') :
        Nonempty (K.map (QuotientGroup.mk' J) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) →
        Nonempty (K.map (QuotientGroup.mk' J') ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      subst J'
      exact id
    exact transport (sourceKernel N) (pCore 2 H) hcore ⟨e⟩
  obtain ⟨eL⟩ := he
  have hLs : L ⊔ (S' : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change K.map q ⊔ (S : Subgroup H).map q = ⊤
    rw [←Subgroup.map_sup,hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  have hLZ : center L = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    let eSL := eL.trans (Theory.PSL2.sl2QuotientEquiv F).symm
    have hh : eSL k ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) :=
      (centerCongr eSL ⟨k,hk⟩).property
    rw [Theory.PSL2.sl2_center_eq_bot F,mem_bot] at hh
    exact mem_bot.mpr (eSL.injective (by simpa only [map_one] using hh))
  let C := centralizer (L : Set (H ⧸ pCore 2 H))
  have hCL : C ≤ S' := centralizer_le_sylow_of_centerless_supplement L S' hLs hLZ
  have hCP : IsPGroup 2 C := S'.isPGroup'.of_injective
    (inclusion hCL) (inclusion_injective hCL)
  have hCp : C ≤ pCore 2 (H ⧸ pCore 2 H) := le_sSup ⟨inferInstance,hCP⟩
  have hC : C = ⊥ := le_bot_iff.mp (hCp.trans_eq (pCore_quotient_pCore_eq_bot 2))
  let a : (H ⧸ pCore 2 H) →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal
  have ha : Function.Injective a := (MulAut.congr eL).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot L hC)
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 a ha).trans
    (Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hn hF)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
