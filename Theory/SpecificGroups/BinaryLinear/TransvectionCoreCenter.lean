module
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.PGroupCore
/-!
# The two-core center of a binary transvection centralizer

The centralizer of x ↦ x + f(x)w preserves the line spanned by w and the
hyperplane ker(f). Both radicals are normal two-subgroups of that literal
centralizer. Their ambient centralizers lie in the radicals themselves, so
the two-core center lies in their intersection. Evaluation on a vector b
with f(b)=1 injects this intersection into the binary line.

Source: the natural binary linear action. The original L₅(2) point-component
comparison in Aschbacher--Smith 10.2.9, printed pp.750--751, uses this bound.
-/

public section
open Subgroup
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem transvection_centralizer_fixes {w : V} {f : V →ₗ[ZMod 2] ZMod 2}
    (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0)
    {g : GL V} (hg : g ∈ (MulAut.conj (transvection w f hfw)).fixedSubgroup) :
    g w = w ∧ ∀ v, f (g v) = f v := by
  have he : transvection w f hfw * g = g * transvection w f hfw :=
    mul_inv_eq_iff_eq_mul.mp ((MulAut.mem_fixedSubgroup _ _).mp hg)
  have hc (v : V) : f (g v) • w = f v • g w := by
    have hh := congrArg (fun a : GL V => a v) he
    change g v + f (g v) • w = g (v + f v • w) at hh
    simpa only [map_add,map_smul,add_right_inj] using hh
  obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  have hgb := hc b
  rw [hb,one_smul] at hgb
  have hs : f (g b) ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at hgb
    exact hw (g.map_eq_zero_iff.mp hgb.symm)
  have h1 : f (g b) = 1 := (by decide : ∀ a : ZMod 2,a ≠ 0 → a=1) _ hs
  have hgw : g w = w := by simpa only [h1,one_smul] using hgb.symm
  refine ⟨hgw,fun v => ?_⟩
  have hh := hc v
  rw [hgw] at hh
  exact (smul_left_injective _ hw) hh

private theorem mem_transvection_centralizer {w : V} {f : V →ₗ[ZMod 2] ZMod 2}
    (hfw : f w = 0) {g : GL V} (hw : g w = w) (hf : ∀ v, f (g v) = f v) :
    g ∈ (MulAut.conj (transvection w f hfw)).fixedSubgroup := by
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  apply mul_inv_eq_iff_eq_mul.mpr
  ext v
  change g v + f (g v) • w = g (v + f v • w)
  rw [map_add,map_smul,hw,hf]

theorem transvection_core_center_card_le_two [Finite V]
    {w : V} {f : V →ₗ[ZMod 2] ZMod 2}
    (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0) :
    Nat.card (center (pCore 2 (MulAut.conj (transvection w f hfw)).fixedSubgroup)) ≤ 2 := by
  classical
  let C := (MulAut.conj (transvection w f hfw)).fixedSubgroup
  let L := Submodule.span (ZMod 2) {w}
  let H := f.ker
  have hLH : L ≤ H := Submodule.span_le.mpr (by
    rintro v (rfl : v=w)
    exact hfw)
  have hL0 : L ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hw
  have hHt : H ≠ ⊤ := by
    intro h
    apply hf
    ext v
    exact (show v ∈ H from h ▸ Submodule.mem_top)
  have hH0 : H ≠ ⊥ := ne_bot_of_le_ne_bot hL0 hLH
  have hLt : L ≠ ⊤ := ne_top_of_le_ne_top hHt hLH
  have hCL : C ≤ parabolic L := by
    intro g hg v
    have hgw := (transvection_centralizer_fixes hw hf hfw hg).1
    constructor
    · intro hv
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv
      exact Submodule.mem_span_singleton.mpr ⟨a,g.injective (by rw [map_smul,hgw]; exact ha)⟩
    · intro hv
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,hgw]
      exact L.smul_mem _ (Submodule.mem_span_singleton_self _)
  have hCH : C ≤ parabolic H := by
    intro g hg v
    change f (g v) = 0 ↔ f v = 0
    rw [(transvection_centralizer_fixes hw hf hfw hg).2]
  have hLC : radical L ≤ C := by
    intro g hg
    apply mem_transvection_centralizer hfw (hg.1 w (Submodule.mem_span_singleton_self _))
    intro v
    have hh : f (g v-v)=0 := hLH (hg.2 v)
    rwa [map_sub,sub_eq_zero] at hh
  have hHC : radical H ≤ C := by
    intro g hg
    apply mem_transvection_centralizer hfw (hg.1 w hfw)
    intro v
    have hh : f (g v-v)=0 := hg.2 v
    rwa [map_sub,sub_eq_zero] at hh
  have radical_le_core (W : Submodule (ZMod 2) V) (hWC : radical W ≤ C)
      (hCP : C ≤ parabolic W) : (radical W).subgroupOf C ≤ pCore 2 C := by
    have hn : ((radical W).subgroupOf C).Normal :=
      (normal_subgroupOf_iff_le_normalizer hWC).mpr
        (hCP.trans (parabolic_le_normalizer W))
    exact le_sSup ⟨hn,(radical_two W).comap_subtype⟩
  have center_mem (W : Submodule (ZMod 2) V) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
      (hWC : radical W ≤ C) (hCP : C ≤ parabolic W) (z : center (pCore 2 C)) :
      z.val.val.val ∈ radical W := by
    apply centralizer_radical_le hW0 hWt
    intro r hr
    exact congrArg (fun a : pCore 2 C => a.val.val) (mem_center_iff.mp z.property
      ⟨⟨r,hWC hr⟩,radical_le_core W hWC hCP hr⟩)
  obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  let coeff : center (pCore 2 C) → ZMod 2 := fun z => Classical.choose
    (Submodule.mem_span_singleton.mp ((center_mem L hL0 hLt hLC hCL z).2 b))
  have coeff_spec (z : center (pCore 2 C)) :
      coeff z • w = z.val.val.val b - b := Classical.choose_spec
    (Submodule.mem_span_singleton.mp ((center_mem L hL0 hLt hLC hCL z).2 b))
  have hinj : Function.Injective coeff := by
    intro x y hxy
    have hxb : x.val.val.val b = y.val.val.val b := by
      apply sub_left_inj.mp
      rw [←coeff_spec x,←coeff_spec y,hxy]
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v-f v • b ∈ H := by
      change f (v-f v • b)=0
      rw [map_sub,map_smul,hb,smul_eq_mul,mul_one,sub_self]
    have hx := (center_mem H hH0 hHt hHC hCH x).1 _ hv
    have hy := (center_mem H hH0 hHt hHC hCH y).1 _ hv
    rw [map_sub,map_smul,hxb] at hx
    rw [map_sub,map_smul] at hy
    exact sub_left_inj.mp (hx.trans hy.symm)
  simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective coeff hinj
end BinaryLinear
