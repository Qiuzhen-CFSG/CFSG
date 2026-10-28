module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionRadicals
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.FieldTheory.Finiteness

/-!
# The two regular point-radical orbits

A full center action realizes the pairing functional attached to any desired
outside vector. Nondegeneracy makes the remaining displacement lie on the
center line. If the radical restriction to the hyperplane is faithful, an
actor moving an outside vector along that line must be the identity.
Consequently radical elements and a binary choice give unique coordinates
on the whole complement. Counting those coordinates gives order 2^(d-2).
The faithful hyperplane action also proves the radical elementary abelian.

The same full action fuses w with w+v in the hyperplane away from the center
line. Irreducibility then gives the complete outside-pair orbit dichotomy.
These are the faithful-radical order and orbit assertions of
Aschbacher--Smith G.12.2 and G.12.6, printed pp.370--371. The full G.12
recognition theorem is a separate obligation. The terminal source applies
these results to both of its literal point radicals.
-/

public noncomputable section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {D : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
  {hB : B.IsAlt} {v : V}

omit [FiniteDimensional (ZMod 2) V] in
include hB in
private theorem swap (x y : V) : B x y = B y x := by
  rw [← hB.neg_eq x y]
  exact (show ∀ a : ZMod 2, -a=a from by decide) (B x y) |>.symm
omit [FiniteDimensional (ZMod 2) V] in
private theorem double (x : V) : x+x=0 := by
  simpa only [two_smul,zero_smul] using congrArg (fun c : ZMod 2 => c • x)
    (show (2 : ZMod 2)=0 from by decide)
omit [FiniteDimensional (ZMod 2) V] in
private theorem span_bit {z : V} (hz : z ∈ Submodule.span (ZMod 2) {v}) :
    z=0 ∨ z=v := by
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  rcases (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) c with rfl|rfl
  · exact Or.inl (zero_smul _ _)
  · exact Or.inr (one_smul _ _)

/-- The point radical reaches one member of each pair outside its hyperplane. -/
theorem GoodVector.radical_pair_cover (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B)
    {x y : V} (hx : B v x=1) (hy : B v y=1) :
    ∃ a ∈ pointRadical D B v, a x=y ∨ a (x+v)=y := by
  let φ : Module.Dual (ZMod 2) (B v).ker := (B (y-x)).comp (B v).ker.subtype
  have hφ : φ ⟨v,hB v⟩=0 := by
    change B (y-x) v=0
    rw [swap (hB := hB),map_sub,hx,hy,sub_self]
  obtain ⟨a,ha⟩ := hv.full φ hφ
  have hav : a.val v=v := a.property.2.1
  have havx : B v (a.val x)=1 := by
    have h := hD a.property.1 v x
    rw [hav] at h
    exact h.trans hx
  have hd : a.val x-y ∈ Submodule.span (ZMod 2) {v} := by
    rw [← B.orthogonal_orthogonal hnd hB.isRefl (Submodule.span (ZMod 2) {v}),
      LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    intro w hw
    rw [swap (hB := hB) w (a.val x-y)]
    have hh := hD a.property.1 x w
    have haw : a.val w = w+B (y-x) w • v := ha ⟨w,hw⟩
    rw [haw] at hh
    change B (a.val x) (w+B (y-x) w • v)=B x w at hh
    rw [map_add,map_smul,smul_eq_mul,swap (hB := hB) (a.val x) v,havx,
      mul_one,map_sub,LinearMap.sub_apply] at hh
    rw [map_sub,LinearMap.sub_apply]
    have ht : ∀ c : ZMod 2,c+c=0 := by decide
    linear_combination hh - ht (B y w) + ht (B x w)
  refine ⟨a,a.property,?_⟩
  rcases span_bit hd with hd|hd
  · exact Or.inl (sub_eq_zero.mp hd)
  · right
    rw [map_add,hav,sub_eq_iff_eq_add.mp hd]
    rw [add_right_comm,double,zero_add]

omit [FiniteDimensional (ZMod 2) V] in
include hB in
/-- An element of the point radical which moves an outside vector only along
the center line fixes the whole perpendicular hyperplane. -/
theorem pointRadical_fixes_hyperplane_of_axis_displacement
    (hD : D ≤ formStabilizer B) {x : V} (hx : B v x=1)
    {a : V ≃ₗ[ZMod 2] V} (ha : a∈pointRadical D B v)
    (hd : a x-x∈Submodule.span (ZMod 2) {v}) :
    ∀ w, B v w=0 → a w=w := by
  obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp hd
  have hax : a x=x+d • v := by rw [hd]; abel
  intro w hw
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (ha.2.2.2 w hw)
  have haw : a w=w+c • v := by rw [hc]; abel
  have he := hD ha.1 x w
  rw [hax,haw] at he
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    smul_eq_mul,hB v,hw,swap (hB := hB) x v,hx,mul_one,mul_zero,add_zero] at he
  have hc0 : c=0 := add_eq_left.mp he
  rw [haw,hc0,zero_smul,add_zero]

omit [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness on the hyperplane separates the two regular outside orbits. -/
theorem GoodVector.radical_pair_unique (hv : GoodVector D B hB v)
    (hD : D ≤ formStabilizer B)
    (hf : ∀ a∈pointRadical D B v, (∀ w,B v w=0 → a w=w) → a=1)
    {x : V} (hx : B v x=1)
    {a b : pointRadical D B v} {c d : ZMod 2}
    (he : a.val (x+c • v)=b.val (x+d • v)) : a=b ∧ c=d := by
  have hfix (z : pointRadical D B v) : z.val v=v := z.property.2.1
  have he' : (b⁻¹*a).val x-x=(d-c) • v := by
    have hh := congrArg b.val.symm he
    simp only [map_add,map_smul,LinearEquiv.symm_apply_apply,hfix] at hh
    have hbv : b.val.symm v=v :=
      (congrArg b.val.symm (hfix b)).symm.trans (b.val.symm_apply_apply v)
    rw [hbv] at hh
    change b.val.symm (a.val x)-x=(d-c) • v
    calc
      b.val.symm (a.val x)-x =
          (b.val.symm (a.val x)+c • v)-(x+c • v) := by abel
      _ = (x+d • v)-(x+c • v) := congrArg (fun z : V => z-(x+c • v)) hh
      _ = (d-c) • v := by rw [sub_smul]; abel
  have hab1 : (b⁻¹*a).val=1 := hf _ (b⁻¹*a).property
    (pointRadical_fixes_hyperplane_of_axis_displacement (hB := hB) hD hx
      (b⁻¹*a).property (he' ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
  have hab : a=b := by
    have hh : b⁻¹*a=1 := Subtype.ext hab1
    exact (inv_mul_eq_one.mp hh).symm
  refine ⟨hab,?_⟩
  have hcd := b.val.injective (hab ▸ he)
  have hs : (c-d) • v=0 := by rw [sub_smul,add_left_cancel hcd,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hv.nonzero)

/-- A faithful point radical gives unique coordinates on the complement of
its perpendicular hyperplane: one radical element and one binary choice. -/
theorem GoodVector.radical_pair_bijective (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B)
    (hf : ∀ a∈pointRadical D B v, (∀ w,B v w=0 → a w=w) → a=1)
    {x : V} (hx : B v x=1) :
    Function.Bijective (fun p : pointRadical D B v × ZMod 2 =>
      (⟨p.1.val (x+p.2 • v),by
        have h := hD p.1.property.1 v (x+p.2 • v)
        rw [p.1.property.2.1] at h
        simpa only [map_add,map_smul,hB v,smul_zero,add_zero,hx] using h⟩ :
        {y : V // B v y=1})) := by
  constructor
  · rintro ⟨a,c⟩ ⟨b,d⟩ he
    have hh := hv.radical_pair_unique hD hf hx (congrArg Subtype.val he)
    exact Prod.ext hh.1 hh.2
  · rintro ⟨y,hy⟩
    obtain ⟨a,ha,h⟩ := hv.radical_pair_cover hnd hD hx hy
    rcases h with h|h
    · exact ⟨(⟨a,ha⟩,0),Subtype.ext (by simpa only [zero_smul,add_zero] using h)⟩
    · exact ⟨(⟨a,ha⟩,1),Subtype.ext (by simpa only [one_smul] using h)⟩

/-- The two outside orbits are regular, with their original marked representatives. -/
theorem GoodVector.radical_pair_exists_unique (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B)
    (hf : ∀ a∈pointRadical D B v, (∀ w,B v w=0 → a w=w) → a=1)
    {x y : V} (hx : B v x=1) (hy : B v y=1) :
    ∃! p : pointRadical D B v × ZMod 2, p.1.val (x+p.2 • v)=y := by
  have hb := hv.radical_pair_bijective hnd hD hf hx
  obtain ⟨p,hp⟩ := hb.surjective ⟨y,hy⟩
  refine ⟨p,congrArg Subtype.val hp,?_⟩
  intro z hz
  exact hb.injective (Subtype.ext (hz.trans (congrArg Subtype.val hp).symm))

omit [FiniteDimensional (ZMod 2) V] in
/-- The faithful point radical is elementary abelian, as its entire
hyperplane action consists of transvections with the same center. -/
theorem GoodVector.elementary_pointRadical_of_faithful (hv : GoodVector D B hB v)
    (hf : ∀ a∈pointRadical D B v, (∀ w,B v w=0 → a w=w) → a=1) :
    IsElementaryAbelian 2 (pointRadical D B v) := by
  have hs (a : pointRadical D B v) : a^2=1 := by
    apply Subtype.ext
    apply hf _ (a^2).property
    intro w hw
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hv.displacement a ⟨w,hw⟩)
    have haw : a.val w=w+c • v := by rw [hc]; abel
    change a.val (a.val w)=w
    rw [haw,map_add,map_smul,a.property.2.1,haw,add_assoc,double,add_zero]
  exact {
    toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_iff_pow_eq_one.mpr (hs a)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

omit [FiniteDimensional (ZMod 2) V] in
/-- The source point radical fuses a hyperplane vector with its translate
by the center whenever that vector lies outside the center line. -/
theorem GoodVector.radical_sends_to_add_center (hv : GoodVector D B hB v)
    {w : V} (hw : B v w=0)
    (hn : w∉Submodule.span (ZMod 2) {v}) :
    ∃ a ∈ pointRadical D B v, a w=w+v := by
  have hwn : (⟨w,hw⟩ : (B v).ker)∉Submodule.span (ZMod 2) {⟨v,hB v⟩} := by
    intro hh
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
    exact hn (Submodule.mem_span_singleton.mpr ⟨c,congrArg Subtype.val hc⟩)
  obtain ⟨φ,hφw,hφ⟩ := (Submodule.span (ZMod 2) {(⟨v,hB v⟩ : (B v).ker)}).exists_le_ker_of_notMem hwn
  have hφv : φ ⟨v,hB v⟩=0 := hφ (Submodule.mem_span_singleton_self _)
  obtain ⟨a,ha⟩ := hv.full φ hφv
  have hc : φ ⟨w,hw⟩=1 :=
    ((show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) _).resolve_left hφw
  refine ⟨a,a.property,?_⟩
  have he : a.val w=w+φ ⟨w,hw⟩ • v := ha ⟨w,hw⟩
  rw [hc,one_smul] at he
  exact he

omit [FiniteDimensional (ZMod 2) V] in
/-- The orbit-membership part of G.12.6(2), with literal group witnesses. -/
theorem GoodVector.orbit_iff_add_center (hv : GoodVector D B hB v)
    {w : V} (hw : B v w=0)
    (hn : w∉Submodule.span (ZMod 2) {v}) :
    (∃ a∈D,a v=w) ↔ ∃ a∈D,a v=w+v := by
  obtain ⟨a,ha,haw⟩ := hv.radical_sends_to_add_center hw hn
  constructor
  · rintro ⟨g,hg,hgv⟩
    exact ⟨a*g,D.mul_mem ha.1 hg,by change a (g v)=w+v; rw [hgv,haw]⟩
  · rintro ⟨g,hg,hgv⟩
    refine ⟨a⁻¹*g,D.mul_mem (D.inv_mem ha.1) hg,?_⟩
    change a.symm (g v)=w
    rw [hgv,← haw,a.symm_apply_apply]

omit [FiniteDimensional (ZMod 2) V] in
/-- If the source center's orbit contains the hyperplane complement, it
contains every nonzero vector. This is G.12.4(1) using irreducibility. -/
theorem GoodVector.orbit_all_of_outside (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hirr : Irreducible D)
    (ho : ∀ x : V,B v x=1 → ∃ a∈D,a v=x) :
    ∀ x : V,x≠0 → ∃ a∈D,a v=x := by
  have hW : (B v).ker ≠ ⊤ := by
    intro ht
    exact hv.nonzero (hnd.1 v (fun x => ht.ge (Submodule.mem_top : x∈(⊤ : Submodule (ZMod 2) V))))
  intro x hx
  obtain ⟨a,ha,hax⟩ := hirr.exists_outside hW hx
  have hb : B v (a x)=1 :=
    ((show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) _).resolve_left hax
  obtain ⟨b,hb,hbv⟩ := ho (a x) hb
  exact ⟨a⁻¹*b,D.mul_mem (D.inv_mem ha) hb,by change a.symm (b v)=x; rw [hbv,a.symm_apply_apply]⟩

/-- G.12.6(3): unless the center orbit is all nonzero vectors, it contains
exactly one member of every outside pair. -/
theorem GoodVector.outside_orbit_dichotomy (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B) (hirr : Irreducible D)
    {x : V} (hx : B v x=1) :
    (∀ y : V,y≠0 → ∃ a∈D,a v=y) ∨
    ((∃ a∈D,a v=x) ↔ ¬ ∃ a∈D,a v=x+v) := by
  have hW : (B v).ker ≠ ⊤ := by
    intro ht
    exact hv.nonzero (hnd.1 v (fun x => ht.ge (Submodule.mem_top : x∈(⊤ : Submodule (ZMod 2) V))))
  obtain ⟨g,hg,hgv⟩ := hirr.exists_outside hW hv.nonzero
  have hg1 : B v (g v)=1 :=
    ((show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) _).resolve_left hgv
  have hsome : (∃ a∈D,a v=x) ∨ ∃ a∈D,a v=x+v := by
    obtain ⟨a,ha,h⟩ := hv.radical_pair_cover hnd hD hx hg1
    rcases h with h|h
    · exact Or.inl ⟨a⁻¹*g,D.mul_mem (D.inv_mem ha.1) hg,
        by change a.symm (g v)=x; rw [← h,a.symm_apply_apply]⟩
    · exact Or.inr ⟨a⁻¹*g,D.mul_mem (D.inv_mem ha.1) hg,
        by change a.symm (g v)=x+v; rw [← h,a.symm_apply_apply]⟩
  by_cases hboth : (∃ a∈D,a v=x) ∧ ∃ a∈D,a v=x+v
  · left
    apply hv.orbit_all_of_outside hnd hirr
    intro y hy
    obtain ⟨a,ha,h⟩ := hv.radical_pair_cover hnd hD hx hy
    rcases h with h|h
    · obtain ⟨b,hb,hbv⟩ := hboth.1
      exact ⟨a*b,D.mul_mem ha.1 hb,by change a (b v)=y; rw [hbv,h]⟩
    · obtain ⟨b,hb,hbv⟩ := hboth.2
      exact ⟨a*b,D.mul_mem ha.1 hb,by change a (b v)=y; rw [hbv,h]⟩
  · right
    exact ⟨fun ha hb => hboth ⟨ha,hb⟩,fun hn => hsome.resolve_right hn⟩

/-- The faithful radical has exactly the source order 2^(d-2). -/
theorem GoodVector.card_pointRadical_of_faithful (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B)
    (hf : ∀ a∈pointRadical D B v, (∀ w,B v w=0 → a w=w) → a=1)
    (hd : 2 ≤ finrank (ZMod 2) V) {x : V} (hx : B v x=1) :
    Nat.card (pointRadical D B v) = 2 ^ (finrank (ZMod 2) V-2) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let e : (B v).ker ≃ {y : V // B v y=1} := {
    toFun w := ⟨x+w,by
      have hw : B v w=0 := w.property
      rw [map_add,hx,hw,add_zero]⟩
    invFun y := ⟨y-x,by
      change B v (y.val-x)=0
      rw [map_sub,y.property,hx,sub_self]⟩
    left_inv := fun w => Subtype.ext (by change x+(w:V)-x=w; abel)
    right_inv := fun y => Subtype.ext (by change x+((y:V)-x)=y; abel) }
  have hc : Nat.card (pointRadical D B v)*2=Nat.card {y : V // B v y=1} := by
    simpa only [Nat.card_prod,Nat.card_zmod] using
      Nat.card_congr (Equiv.ofBijective _ (hv.radical_pair_bijective hnd hD hf hx))
  rw [← Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (B v).ker),Nat.card_zmod] at hc
  have hn : B v ≠ 0 := by
    intro hz
    have hh : B v x=0 := LinearMap.congr_fun hz x
    exact zero_ne_one (hh.symm.trans hx)
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have he : finrank (ZMod 2) (B v).ker=(finrank (ZMod 2) V-2)+1 := by omega
  rw [he,Nat.pow_succ] at hc
  omega
end CFSG.Quasithin.ChapterG.Section12
