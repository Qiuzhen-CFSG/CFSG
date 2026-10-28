module

public import Theory.GroupTheory.ChiefFactorDirectPower
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Coordinate components of the minimal-normal direct power

An actual direct-power equivalence gives explicit component inclusions and
isomorphisms onto their ranges. These ranges are normal in the minimal normal
subgroup, simple when the factor is simple, pairwise disjoint and commuting,
and generate the whole subgroup. The coordinate formula retains the precise
embedding; no ambient normality of an individual component is asserted.

Source: the direct-product step on p.1149 of Aschbacher–Smith,
combined manuscript (1 March 2004), proof of 15.3.58.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
namespace Components
variable {K S : Type*} [Group K] [Group S] {n : ℕ}

/-- Include one coordinate factor in the actual minimal normal subgroup. -/
def componentEmbedding (e : K ≃* (Fin n → S)) (i : Fin n) : S →* K :=
  e.symm.toMonoidHom.comp (MonoidHom.mulSingle (fun _ : Fin n => S) i)

/-- The inclusion has exactly the specified nonidentity coordinate. -/
theorem componentEmbedding_coordinates (e : K ≃* (Fin n → S)) (i : Fin n) (s : S) :
    e (componentEmbedding e i s) = Pi.mulSingle i s := e.apply_symm_apply _

/-- Each coordinate inclusion is an embedding. -/
theorem componentEmbedding_injective (e : K ≃* (Fin n → S)) (i : Fin n) :
    Function.Injective (componentEmbedding e i) := by
  intro a b h
  have hh := congrArg (fun x => e x i) h
  simpa only [componentEmbedding_coordinates, Pi.mulSingle_eq_same] using hh

/-- The component range is explicitly isomorphic to the chosen simple factor. -/
noncomputable def componentEquiv (e : K ≃* (Fin n → S)) (i : Fin n) :
    S ≃* (componentEmbedding e i).range :=
  MonoidHom.ofInjective (componentEmbedding_injective e i)

/-- A coordinate component is normal in the direct product. -/
theorem component_normal (e : K ≃* (Fin n → S)) (i : Fin n) :
    (componentEmbedding e i).range.Normal := by
  constructor
  intro x hx g
  obtain ⟨s, rfl⟩ := hx
  refine ⟨(e g i) * s * (e g i)⁻¹, ?_⟩
  apply e.injective
  simp only [componentEmbedding_coordinates, map_mul, map_inv]
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Pi.mulSingle_eq_of_ne hj]

/-- Each embedded component inherits simplicity from the chosen factor. -/
theorem component_simple [IsSimpleGroup S] (e : K ≃* (Fin n → S)) (i : Fin n) :
    IsSimpleGroup (componentEmbedding e i).range := (componentEquiv e i).symm.isSimpleGroup

/-- Distinct coordinate components commute elementwise. -/
theorem component_commute (e : K ≃* (Fin n → S)) {i j : Fin n} (hij : i ≠ j)
    (a b : S) : Commute (componentEmbedding e i a) (componentEmbedding e j b) := by
  exact (Pi.mulSingle_commute hij a b).map e.symm.toMonoidHom

/-- Distinct coordinate components have trivial intersection. -/
theorem component_disjoint (e : K ≃* (Fin n → S)) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (componentEmbedding e i).range (componentEmbedding e j).range := by
  apply Subgroup.disjoint_def.mpr
  rintro x ⟨a, rfl⟩ ⟨b, h⟩
  have ha : a = 1 := by
    have he := congrArg (fun x => e x i) h
    simpa only [componentEmbedding_coordinates, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne hij] using he.symm
  rw [ha, map_one]

/-- The range retains the nonabelian group structure of the factor. -/
theorem component_nonabelian (e : K ≃* (Fin n → S)) (hna : ¬ IsMulCommutative S)
    (i : Fin n) : ¬ IsMulCommutative (componentEmbedding e i).range := by
  intro hc
  let := hc
  apply hna
  refine ⟨⟨fun a b => ?_⟩⟩
  apply (componentEquiv e i).injective
  simp only [map_mul]
  exact (IsMulCommutative.is_comm (M := (componentEmbedding e i).range)).comm _ _

/-- The actual component subgroups generate the whole direct product. -/
theorem iSup_component_eq_top (e : K ≃* (Fin n → S)) :
    (⨆ i, (componentEmbedding e i).range) = ⊤ := by
  have hc : Pairwise fun i j => ∀ a b, Commute (componentEmbedding e i a)
      (componentEmbedding e j b) := fun _ _ hij => component_commute e hij
  have he : MonoidHom.noncommPiCoprod (componentEmbedding e) hc = e.symm.toMonoidHom := by
    apply MonoidHom.pi_ext
    intro i s
    exact MonoidHom.noncommPiCoprod_mulSingle (componentEmbedding e) (hcomm := hc) i s
  rw [← MonoidHom.noncommPiCoprod_range (componentEmbedding e) (hcomm := hc), he]
  exact MonoidHom.range_eq_top.mpr e.symm.surjective

end Components
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
