module

public import CFSG.Quasithin.ChapterA.Section01
public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowQuotientPreimage
public import Theory.GroupAction.FourGroupCoreAction
public import Mathlib.Tactic

/-!
# Aschbacher--Smith A.1.7 and the remaining elementary lemmas

The conjugate-family definitions below use the literal action `x ↦ gxg⁻¹`.
This keeps the fusion statements independent of the several opposite-action
conventions used elsewhere in the project.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, printed pp. 21--23.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.ChapterA

universe u

variable {G : Type u} [Group G]

/-- The set of conjugates of `X`, with the ambient conjugator displayed. -/
def conjugateFamily (X : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ g : G, Y = X.map (MulAut.conj g).toMonoidHom}

/-- The members of the conjugate family which contain `x`. -/
def conjugateFamilyContaining (X : Subgroup G) (x : G) : Set (Subgroup G) :=
  {Y | Y ∈ conjugateFamily X ∧ x ∈ Y}

/-- The two sides of the fusion equality in A.1.7(1). -/
def fusionSet (X : Subgroup G) (x : G) : Set G :=
  {y | y ∈ X ∧ ∃ g : G, (MulAut.conj g) x = y}

def normalizerFusionSet (X : Subgroup G) (x : G) : Set G :=
  {y | ∃ n ∈ normalizer (X : Set G), (MulAut.conj n) x = y}

theorem mem_conjugateFamilyContaining_iff {X : Subgroup G} {x : G} {Y : Subgroup G} :
    Y ∈ conjugateFamilyContaining X x ↔
      (∃ g : G, Y = X.map (MulAut.conj g).toMonoidHom) ∧ x ∈ Y := Iff.rfl

private theorem map_conj_mul (X : Subgroup G) (a b : G) :
    X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  change (a * b) * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹
  group

private theorem map_conj_normalizer {X : Subgroup G} {n : G}
    (hn : n ∈ normalizer (X : Set G)) :
    X.map (MulAut.conj n).toMonoidHom = X := by
  exact mem_normalizer_iff_map_conj_eq.mp hn

private theorem map_conj_mem {X : Subgroup G} {g : G} {x : G}
    (hx : x ∈ X) : (MulAut.conj g) x ∈ X.map (MulAut.conj g).toMonoidHom := by
  exact mem_map_of_mem (MulAut.conj g).toMonoidHom hx

/-! ### A.1.7 -/

theorem lemma_A_1_7_1 (X : Subgroup G) (x : G) (hx : x ∈ X) :
    (fusionSet X x = normalizerFusionSet X x) ↔
      ∀ Y ∈ conjugateFamilyContaining X x,
        ∃ c ∈ centralizer ({x} : Set G),
          Y = X.map (MulAut.conj c).toMonoidHom := by
  constructor
  · intro h Y hY
    rcases hY with ⟨⟨g, rfl⟩, hxY⟩
    obtain ⟨y, hyX, hgy⟩ := (Subgroup.mem_map.mp hxY)
    have hconj : (MulAut.conj g) y = x := hgy
    have hyf : y ∈ fusionSet X x := by
      refine ⟨hyX, ?_⟩
      exact ⟨g⁻¹, by
        have he : g⁻¹ * x * g = y := by
          rw [← hconj]
          change g⁻¹ * (g * y * g⁻¹) * g = y
          group
        simpa [MulAut.conj_apply] using he⟩
    have hyf' : y ∈ normalizerFusionSet X x := h ▸ hyf
    change ∃ n ∈ normalizer (X : Set G), (MulAut.conj n) x = y at hyf'
    obtain ⟨n, hn, hnx⟩ := hyf'
    refine ⟨g * n, ?_, ?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      have hnx' : n * x = y * n := by
        calc
          n * x = (n * x * n⁻¹) * n := by group
          _ = y * n := by simpa [MulAut.conj_apply] using congrArg (fun z => z * n) hnx
      have hconj' : g * y = x * g := by
        calc
          g * y = (g * y * g⁻¹) * g := by group
          _ = x * g := by simpa [MulAut.conj_apply] using congrArg (fun z => z * g) hconj
      calc
        (g * n) * x = g * (n * x) := by simp [mul_assoc]
        _ = g * (y * n) := by rw [hnx']
        _ = (g * y) * n := by simp [mul_assoc]
        _ = (x * g) * n := by rw [hconj']
        _ = x * (g * n) := by simp [mul_assoc]
    · rw [map_conj_mul, map_conj_normalizer hn]
  · intro h
    ext y
    constructor
    · intro hy
      change y ∈ X ∧ ∃ g : G, (MulAut.conj g) x = y at hy
      rcases hy with ⟨hyX, ⟨g, rfl⟩⟩
      have hY : X.map (MulAut.conj g⁻¹).toMonoidHom ∈
          conjugateFamilyContaining X x := by
        refine ⟨⟨g⁻¹, rfl⟩, ?_⟩
        rw [mem_map_equiv]
        simpa using hyX
      obtain ⟨c, hc, hcg⟩ := h _ hY
      refine ⟨g * c, ?_, ?_⟩
      · apply mem_normalizer_iff_map_conj_eq.mpr
        calc
          X.map (MulAut.conj (g * c)).toMonoidHom =
              (X.map (MulAut.conj c).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
            map_conj_mul X g c
          _ = (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [hcg]
          _ = X := by
            rw [← map_conj_mul]
            ext z
            simp
      · have hcx : c * x = x * c :=
          mem_centralizer_singleton_iff.mp hc
        exact by
          calc
            g * c * x * (g * c)⁻¹ = g * (c * x) * c⁻¹ * g⁻¹ := by group
            _ = g * (x * c) * c⁻¹ * g⁻¹ := by rw [hcx]
            _ = g * x * g⁻¹ := by group
    · intro hy
      change ∃ g ∈ normalizer (X : Set G), (MulAut.conj g) x = y at hy
      rcases hy with ⟨g, hg, rfl⟩
      have hyX : (MulAut.conj g) x ∈ X := by
        rw [← map_conj_normalizer hg]
        exact map_conj_mem hx
      exact ⟨hyX, ⟨g, rfl⟩⟩

theorem lemma_A_1_7_2 (X : Subgroup G) (x : G) (hx : x ∈ X)
    (hfusion : fusionSet X x = normalizerFusionSet X x)
    (hcentral : centralizer ({x} : Set G) ≤ normalizer (X : Set G)) :
    ∀ Y ∈ conjugateFamilyContaining X x,
      Y = X := by
  intro Y hY
  obtain ⟨c, hc, hcg⟩ := (lemma_A_1_7_1 X x hx).mp hfusion Y hY
  rw [hcg, map_conj_normalizer (hcentral hc)]

theorem lemma_A_1_7_3 (X M : Subgroup G) (hTI :
    CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup X)
    (_hXM : X ≤ M) (x : G) (hx : x ∈ X) (hx1 : x ≠ 1)
    (hfusion : fusionSet X x = normalizerFusionSet X x)
    (_hcentral : centralizer ({x} : Set G) ≤ M) :
    ∀ Y ∈ conjugateFamilyContaining X x, Y = X := by
  apply lemma_A_1_7_2 X x hx hfusion
  exact (hTI.centralizer_le_normalizer hx hx1)

/-! ### A.1.14: full action and relative normal closure

`FourGroupCorePair` has exactly the printed four-group, two distinct
involution, and two point-core commutator hypotheses. The kernel formula,
quotient product and quasithin rank assertion are separate obligations;
the following action assertion is only the first part of (1).
-/

/-- The full automorphism action asserted in A.1.14(1). -/
theorem lemma_A_1_14_action [Finite G] {V : Subgroup G} {v₁ v₂ : G}
    (h : FourGroupCorePair V v₁ v₂) : Function.Surjective h.action :=
  h.action_surjective

/-- A.1.14(2), with normal closure taken inside N_G(V). -/
theorem lemma_A_1_14_2 [Finite G] {V : Subgroup G} {v₁ v₂ : G}
    (h : FourGroupCorePair V v₁ v₂) :
    (normalClosure ((FourGroupCorePair.core v₁).subgroupOf
      (normalizer (V : Set G)) : Set (normalizer (V : Set G)))).map
        (normalizer (V : Set G)).subtype = FourGroupCorePair.generated v₁ v₂ ∧
    ((FourGroupCorePair.generated v₁ v₂).subgroupOf
      (normalizer (V : Set G))).Normal :=
  ⟨h.normalClosure_core₁, h.generated_normal⟩

/-- The normalizer factorization used in the proof of A.1.14(3). -/
theorem lemma_A_1_14_normalizer [Finite G] {V : Subgroup G} {v₁ v₂ : G}
    (h : FourGroupCorePair V v₁ v₂) :
    normalizer (V : Set G) =
      FourGroupCorePair.generated v₁ v₂ ⊔ centralizer (V : Set G) :=
  h.normalizer_eq_sup_centralizer

/-! ### A.1.16(2) -/

theorem lemma_A_1_16_2 [Finite G] (Y D : Subgroup G) [Y.Normal]
    (hYD : Y ≤ D) (C : Sylow 2 G)
    (P : Sylow 2 (D.map (QuotientGroup.mk' Y)))
    (hP : (P : Subgroup (D.map (QuotientGroup.mk' Y))) =
      ((C : Subgroup G).map (QuotientGroup.mk' Y)).subgroupOf
        (D.map (QuotientGroup.mk' Y))) :
    ∃ S : Sylow 2 D,
      (S : Subgroup D).map D.subtype = (C : Subgroup G) ⊓ D := by
  let q := QuotientGroup.mk' Y
  let I := D.map q
  obtain ⟨S, hS⟩ := Sylow.exists_subgroupOf_eq_comap C q I P hP
  have hL : I.comap q = D := by
    change (D.map q).comap q = D
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hYD]
  let e : (I.comap q) ≃* D :=
    { toFun := fun z => ⟨z.1, hL ▸ z.2⟩
      invFun := fun z => ⟨z.1, hL.symm ▸ z.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl
      map_mul' := by intro a b; rfl }
  let SD : Sylow 2 D := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨SD, ?_⟩
  have hcomp : D.subtype.comp e.toMonoidHom = (I.comap q).subtype := by
    ext z
    rfl
  have hSDcoe : (SD : Subgroup D) =
      (S : Subgroup (I.comap q)).map e.toMonoidHom := by
    exact Sylow.coe_mapSurjective e.surjective S
  calc
    (SD : Subgroup D).map D.subtype =
        ((S : Subgroup (I.comap q)).map e.toMonoidHom).map D.subtype := by
          rw [hSDcoe]
    _ = (S : Subgroup (I.comap q)).map (I.comap q).subtype := by
          rw [Subgroup.map_map, hcomp]
    _ = ((C : Subgroup G).subgroupOf (I.comap q)).map (I.comap q).subtype := by rw [hS]
    _ = (C : Subgroup G) ⊓ (I.comap q) := Subgroup.subgroupOf_map_subtype _ _
    _ = (C : Subgroup G) ⊓ D := by rw [hL]

end CFSG.Quasithin.ChapterA

