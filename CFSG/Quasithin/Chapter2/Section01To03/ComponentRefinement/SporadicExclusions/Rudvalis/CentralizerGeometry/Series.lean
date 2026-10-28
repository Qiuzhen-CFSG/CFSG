module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.SubnormalBlocks
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.PowerCover
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients
public import Mathlib.Order.RelSeries
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Relative factor series for Rudvalis max4 component-orbit covers

Transport and concatenate finite relative normal series through actual
isomorphisms, normal subgroups and surjections. Iteration gives a series of a
finite direct power. Every factor is the literal quotient of consecutive
terms; normality is only relative to the next term.

The max4 series uses its two-core and the actual conjugation-action quotient
PSL₃(2), whose simplicity and order 168 are proved independently. Applying the
series constructors to a normal power cover retains the two-group kernels
both below and above the component-orbit base. The existing subnormal-block
exclusion consumes precisely these series in the final cover assembly.

Source: Aschbacher–Smith 2.3.9(7), printed p.526; GLS3 Table 5.3r and its
justification, printed pp.291–292. These constructors remain beside the
campaign-specific `LocalFactorSeries` interface.
-/

public section

noncomputable section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry
open Subgroup Theory.GroupTheory

private def Allowed (X : Type*) [Group X] : Prop :=
  IsPGroup 2 X ∨ (IsSimpleGroup X ∧ (Nat.card X = 168 ∨ Nat.card X = 6048))

private theorem allowed_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : Allowed X) : Allowed Y := by
  rcases h with hp | ⟨hs, hc⟩
  · exact Or.inl (hp.of_equiv e)
  · exact Or.inr ⟨(MulEquiv.isSimpleGroup_congr e).mp hs,
      (Nat.card_congr e.toEquiv).symm ▸ hc⟩

private structure Step {X : Type*} [Group X] (A B : Subgroup X) : Prop where
  le : A ≤ B
  normal : (A.subgroupOf B).Normal
  factor : letI := normal; Allowed (B ⧸ A.subgroupOf B)

private abbrev steps (X : Type*) [Group X] : SetRel (Subgroup X) (Subgroup X) :=
  {ab | Step ab.1 ab.2}

private theorem step_of_surjective {X Y : Type*} [Group X] [Group Y]
    (A B : Subgroup X) (hle : A ≤ B) (f : B →* Y)
    (hf : Function.Surjective f) (hk : f.ker = A.subgroupOf B) (hy : Allowed Y) :
    Step A B := by
  have hn : (A.subgroupOf B).Normal := hk ▸ inferInstance
  let := hn
  refine ⟨hle, hn, ?_⟩
  exact allowed_equiv
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm hy

private theorem step_map {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) {A B : Subgroup X} (h : Step A B) :
    Step (A.map f) (B.map f) := by
  let := h.normal
  let e := B.equivMapOfInjective f hf
  let q := (QuotientGroup.mk' (A.subgroupOf B)).comp e.symm.toMonoidHom
  apply step_of_surjective _ _ (map_mono h.le) q
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective) ?_ h.factor
  ext x
  change QuotientGroup.mk' (A.subgroupOf B) (e.symm x) = 1 ↔ (x : Y) ∈ A.map f
  refine (QuotientGroup.eq_one_iff (e.symm x)).trans ?_
  change ((e.symm x : B) : X) ∈ A ↔ (x : Y) ∈ A.map f
  have he : f ((e.symm x : B) : X) = (x : Y) :=
    congrArg Subtype.val (e.apply_symm_apply x)
  rw [← he, mem_map_iff_mem hf]

private theorem step_comap {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) {A B : Subgroup Y} (h : Step A B) :
    Step (A.comap f) (B.comap f) := by
  let := h.normal
  let r : B.comap f →* B := {
    toFun x := ⟨f x, x.property⟩
    map_one' := Subtype.ext f.map_one
    map_mul' _ _ := Subtype.ext (f.map_mul _ _) }
  have hr : Function.Surjective r := by
    intro b
    obtain ⟨x, hx⟩ := hf b
    exact ⟨⟨x, show f x ∈ B from hx.symm ▸ b.property⟩, Subtype.ext hx⟩
  let q := (QuotientGroup.mk' (A.subgroupOf B)).comp r
  apply step_of_surjective _ _ (comap_mono h.le) q
    ((QuotientGroup.mk'_surjective _).comp hr) ?_ h.factor
  ext x
  exact QuotientGroup.eq_one_iff (r x)

private theorem step_refl {X : Type*} [Group X] (A : Subgroup X) : Step A A := by
  have hn : (A.subgroupOf A).Normal := by rw [subgroupOf_self]; infer_instance
  let := hn
  refine ⟨le_rfl, hn, Or.inl ?_⟩
  have : Subsingleton (A ⧸ A.subgroupOf A) := by
    rw [subgroupOf_self]
    exact QuotientGroup.subsingleton_quotient_top
  exact IsPGroup.of_subsingleton 2 _

private def chain {X : Type*} [Group X] (s : LocalFactorSeries X) : RelSeries (steps X) where
  length := s.length
  toFun := s.term
  step i := ⟨s.ascending i, s.normal i, s.factor i⟩

private def from_chain {X : Type*} [Group X] (c : RelSeries (steps X))
    (hfirst : c.head = ⊥) (hlast : c.last = ⊤) : LocalFactorSeries X where
  length := c.length
  term := c
  first := hfirst
  last := hlast
  ascending i := (c.step i).le
  normal i := (c.step i).normal
  factor i := (c.step i).factor

/-- Transport an actual relative factor series through an isomorphism. -/
def series_equiv {X Y : Type*} [Group X] [Group Y]
    (s : LocalFactorSeries X) (e : X ≃* Y) : LocalFactorSeries Y := by
  let r : (steps X).Hom (steps Y) :=
    ⟨fun A => A.map e.toMonoidHom, fun h => step_map e.toMonoidHom e.injective h⟩
  apply from_chain ((chain s).map r)
  · change (s.term 0).map e.toMonoidHom = ⊥
    rw [s.first, Subgroup.map_bot]
  · change (s.term (Fin.last s.length)).map e.toMonoidHom = ⊤
    rw [s.last, map_top_of_surjective _ e.surjective]

private def singleton_series {X : Type*} [Group X] (h : Allowed X) : LocalFactorSeries X := by
  have hstep : Step (⊥ : Subgroup X) ⊤ := by
    apply step_of_surjective (⊥ : Subgroup X) (⊤ : Subgroup X) bot_le
      (topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom topEquiv.surjective
    · ext x
      change (x : X) = 1 ↔ (x : X) ∈ (⊥ : Subgroup X)
      exact mem_bot.symm
    · exact h
  let c : RelSeries (steps X) := {
    length := 1
    toFun := ![⊥, ⊤]
    step := by intro i; fin_cases i; exact hstep }
  exact from_chain c rfl rfl

/-- Concatenate the normal-subgroup series with the pulled-back quotient
series. Normality remains relative to consecutive actual terms. -/
def extension_series {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (s : LocalFactorSeries N) (t : LocalFactorSeries (X ⧸ N)) : LocalFactorSeries X := by
  let q := QuotientGroup.mk' N
  let r : (steps N).Hom (steps X) :=
    ⟨fun A => A.map N.subtype, fun h => step_map N.subtype N.subtype_injective h⟩
  let u : (steps (X ⧸ N)).Hom (steps X) :=
    ⟨fun A => A.comap q, fun h => step_comap q (QuotientGroup.mk'_surjective N) h⟩
  let a := (chain s).map r
  let b := (chain t).map u
  have ha : a.last = N := by
    change (s.term (Fin.last s.length)).map N.subtype = N
    rw [s.last, ← MonoidHom.range_eq_map, range_subtype]
  have hb : b.head = N := by
    change (t.term 0).comap q = N
    rw [t.first]
    exact QuotientGroup.ker_mk' N
  have hab : Step a.last b.head := by rw [ha, hb]; exact step_refl N
  apply from_chain (a.append b hab)
  · rw [RelSeries.head_append]
    change (s.term 0).map N.subtype = ⊥
    rw [s.first, Subgroup.map_bot]
  · rw [RelSeries.last_append]
    change (t.term (Fin.last t.length)).comap q = ⊤
    rw [t.last, comap_top]

/-- A surjection combines a series of its actual kernel with one of its target. -/
def surjection_series {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (s : LocalFactorSeries f.ker) (t : LocalFactorSeries Y) :
    LocalFactorSeries X :=
  extension_series f.ker s
    (series_equiv t (QuotientGroup.quotientKerEquivOfSurjective f hf).symm)

/-- Finite direct powers retain the allowed actual factors. -/
def power_series {X : Type*} [Group X] (s : LocalFactorSeries X) :
    (n : ℕ) → LocalFactorSeries (Fin n → X)
  | 0 => singleton_series (Or.inl (IsPGroup.of_subsingleton 2 _))
  | n + 1 => by
      let f : (Fin (n + 1) → X) →* (Fin n → X) := {
        toFun x := fun i => x i.succ
        map_one' := rfl
        map_mul' _ _ := rfl }
      have hf : Function.Surjective f := fun x => ⟨Fin.cons 1 x, rfl⟩
      let e : f.ker ≃* X := {
        toFun x := x.val 0
        invFun x := ⟨Fin.cons x (fun _ => 1), rfl⟩
        left_inv := by
          intro x
          apply Subtype.ext
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · exact (congrFun x.property j).symm
        right_inv _ := rfl
        map_mul' _ _ := rfl }
      exact surjection_series f hf (series_equiv s e.symm) (power_series s n)

/-- The full max4 local has a two-group kernel and its actual simple quotient
of order 168. No identification is inferred merely from a cardinality. -/
def max4_series : LocalFactorSeries Rudvalis.SylowOvergroups.max4 := by
  let e := Rudvalis.CoreQuotients.max4QuotientEquiv
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  have hs : IsSimpleGroup (Rudvalis.SylowOvergroups.max4 ⧸
      pCore 2 Rudvalis.SylowOvergroups.max4) :=
    (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  have hc : Nat.card (Rudvalis.SylowOvergroups.max4 ⧸
      pCore 2 Rudvalis.SylowOvergroups.max4) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  exact extension_series (pCore 2 Rudvalis.SylowOvergroups.max4)
    (singleton_series (Or.inl pCore_isPGroup))
    (singleton_series (Or.inr ⟨hs, Or.inl hc⟩))

/-- A normal power cover by the actual max4 local yields the required relative
normal series, retaining the two-group kernels both below and above the base. -/
def max4_cover_series {X : Type*} [Group X]
    (c : NormalPowerCover 2 X Rudvalis.SylowOvergroups.max4) : LocalFactorSeries X := by
  let := c.normal
  exact extension_series c.base
    (surjection_series c.projection c.surjective
      (singleton_series (Or.inl c.kernel_isPGroup)) (power_series max4_series c.copies))
    (singleton_series (Or.inl c.quotient_isPGroup))

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase.CentralizerGeometry

end
