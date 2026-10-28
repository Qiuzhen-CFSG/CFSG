module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ParabolicPair
public import Theory.GroupTheory.CComponent.LocalImageEquality
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Canonical lifts of the two field-four parabolic residuals

Take the solvable residual of each literal parabolic-residual preimage.
These are C-components over the original marked Sylow and exhaust its
proper local components when the kernel lies in that Sylow. Fixing one
member of the pair therefore fixes the other. A two-group kernel gives
the actual SL₂(4) quotient of each lift.

The pair generates the whole perfect cover: its image generates PSL₃(4),
and the kernel normalizes both canonical lifts. Hence their join is normal
with solvable quotient, so perfectness removes that quotient. This retains
the original kernel rather than proving generation only downstairs.
OtherResidual supplies the ambient K₀ consumer.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.762, and the C-component calculus A.3.3, pp.41--43.
-/


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterA.Section03 CFSG.Quasithin.Chapter1.Section02
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {A : Type*} [Group A] [Finite A]

def rootLift (f : A →* PSL(3,F)) (b : Bool) : Subgroup A :=
  (solvableResidual ((rootLocal F b).comap f)).map ((rootLocal F b).comap f).subtype

omit [Finite F] [CharP F 2] [Finite A] in
theorem rootLift_le (f : A →* PSL(3,F)) (b : Bool) :
    rootLift f b ≤ (rootLocal F b).comap f := map_subtype_le _

omit [Finite F] [CharP F 2] [Finite A] in
/-- The original quotient kernel normalizes each canonical residual lift. -/
theorem ker_normalizes_rootLift (f : A →* PSL(3,F)) (b : Bool) :
    f.ker ≤ normalizer (rootLift f b : Set A) := by
  have hk : f.ker ≤ (rootLocal F b).comap f := by
    intro x hx
    change f x ∈ rootLocal F b
    rw [show f x = 1 from hx]
    exact (rootLocal F b).one_mem
  exact (hk.trans ((rootLocal F b).comap f).le_normalizer).trans
    (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

omit [CharP F 2] in
theorem rootLift_map (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) (b : Bool) : (rootLift f b).map f = rootLocal F b := by
  let := rootLocal_perfect F hF b
  simpa only [rootLift,solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype]
    using map_solvableResidual_comap f hf (rootLocal F b)

theorem rootLift_component (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) [Group.IsSolvable f.ker] (b : Bool) :
    ((rootLift f b).subgroupOf ((rootLocal F b).comap f)).IsCComponent := by
  let P := (rootLocal F b).comap f
  let q := f.subgroupComap (rootLocal F b)
  let : Group.IsSolvable q.ker := by
    have he : q.ker = f.ker.subgroupOf P := by ext x; exact Subtype.ext_iff
    rw [he]
    exact Group.isSolvable_of_isSolvable_injective
      (f := P.subtype.subgroupComap f.ker) (fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : A)) h)))
  have hc := residual_isCComponent_of_surjective q
    (f.subgroupComap_surjective_of_surjective (rootLocal F b) hf) (by
      let := rootLocal_perfect F hF b
      simpa only [solvableResidual_eq_top] using rootLocal_top_component F hF b)
  change (((solvableResidual P).map P.subtype).comap P.subtype).IsCComponent
  rw [comap_map_eq_self_of_injective P.subtype_injective]
  exact hc

/-- The actual solvable-residual preimages are local components over the original Sylow. -/
theorem rootLift_mem_local (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (P : Subgroup A) (hP : P.map f = unipotent F) (b : Bool) :
    rootLift f b ∈ localCComponents P := by
  have hPL : P ≤ (rootLocal F b).comap f :=
    map_le_iff_le_comap.mp (hP ▸ unipotent_le_rootLocal F b)
  exact (rootLift_component hF f hf b).subgroupOf_of_le le_sup_left
    (sup_le (rootLift_le f b) hPL)

/-- The two canonical lifts exhaust proper local components when the kernel lies in the Sylow. -/
theorem local_eq_rootLift (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (P : Subgroup A) (hP : P.map f = unipotent F) (hk : f.ker ≤ P)
    (htop : (⊤ : Subgroup A).IsCComponent)
    {B : Subgroup A} (hB : B ∈ localCComponents P) (hne : B ≠ ⊤) :
    ∃ b : Bool, B = rootLift f b := by
  have him : B.map f ∈ localCComponents (unipotent F) :=
    hP ▸ localCComponents_map_of_solvable_ker hB f
  have hip : B.map f ≠ ⊤ := by
    intro he
    apply hne
    apply local_cComponent_eq_of_map_eq hB htop le_top f hk
    simpa only [map_top_of_surjective f hf] using he
  obtain ⟨b,hb⟩ := standard_local_cases F hF him hip
  refine ⟨b,?_⟩
  have hBP : B ≤ (rootLocal F b).comap f := map_le_iff_le_comap.mp hb.le
  have hRB : rootLift f b ≤ B ⊔ P := by
    have hh := le_comap_map f (rootLift f b)
    rw [rootLift_map hF f hf b,←hb,comap_map_eq] at hh
    exact hh.trans (sup_le_sup_left hk B)
  have hBR : B ≤ rootLift f b := by
    let := hB.perfect
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ P from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
    exact le_map_solvableResidual_of_isPerfect _ _ hBP
  have hRP := (rootLift_component hF f hf b).subgroupOf_of_le hRB
    (sup_le hBP (map_le_iff_le_comap.mp (hP ▸ unipotent_le_rootLocal F b)))
  have he := hB.eq_of_le hRP (comap_mono hBR)
  simpa only [map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hRB] using
    congrArg (map (B ⊔ P).subtype) he

omit [CharP F 2] in
theorem rootLift_ne_top (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) (b : Bool) : rootLift f b ≠ ⊤ := by
  intro he
  have hh := rootLift_map hF f hf b
  rw [he,map_top_of_surjective f hf] at hh
  exact rootLocal_ne_top F b hh.symm

omit [CharP F 2] in
theorem rootLift_injective (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) : Function.Injective (rootLift f) := by
  intro b d he
  apply rootLocal_injective F
  simpa only [rootLift_map hF f hf] using congrArg (map f) he

/-- The other residual has the literal rank-one quotient through the same two-kernel map. -/
def rootLiftQuotient (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (b : Bool) :
    (rootLift f b ⧸ pCore 2 (rootLift f b)) ≃* SL(2,F) := by
  let C := rootLift f b
  have hker : IsPGroup 2 (f.subgroupMap C).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := (f.subgroupMap C).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective C) hker
  let d := MulEquiv.subgroupCongr (rootLift_map hF f hf b)
  exact e.trans ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans (rootLocalQuotient F b))

omit [CharP F 2] in
/-- The two lifts generate a perfect cover, including its original solvable kernel. -/
theorem rootLift_sup (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) [Group.IsSolvable f.ker] [Group.IsPerfect A]
    (b : Bool) : rootLift f b ⊔ rootLift f (!b) = ⊤ := by
  let J := rootLift f b ⊔ rootLift f (!b)
  have him : J.map f = ⊤ := by
    rw [Subgroup.map_sup,rootLift_map hF f hf,rootLift_map hF f hf,rootLocal_sup]
  have hgen : J ⊔ f.ker = ⊤ := by
    simpa only [comap_map_eq,comap_top] using congrArg (comap f) him
  have hn (d : Bool) : f.ker ≤ normalizer (rootLift f d : Set A) := by
    have hk : f.ker ≤ (rootLocal F d).comap f := by
      intro x hx
      change f x ∈ rootLocal F d
      rw [show f x = 1 from hx]
      exact (rootLocal F d).one_mem
    exact (hk.trans ((rootLocal F d).comap f).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hnJ : f.ker ≤ normalizer (J : Set A) :=
    (le_inf (hn b) (hn (!b))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : J.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (hgen ▸ sup_le J.le_normalizer hnJ))
  have hr := (inferInstance : J.Normal).isSubnormal.solvableResidual_le_of_sup_eq_top
    f.ker hgen
  exact top_le_iff.mp (by simpa only [solvableResidual_eq_top] using hr)

/-- Fixing one member of the lifted pair forces fixation of the other. -/
theorem other_rootLift_fixed (hF : Nat.card F = 4) (f : A →* PSL(3,F))
    (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (P : Subgroup A) (hP : P.map f = unipotent F) (hk : f.ker ≤ P)
    (htop : (⊤ : Subgroup A).IsCComponent)
    (a : MulAut A) (ha : P.map a.toMonoidHom = P) (b : Bool)
    (hb : (rootLift f b).map a.toMonoidHom = rootLift f b) :
    (rootLift f (!b)).map a.toMonoidHom = rootLift f (!b) := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl := localCComponents_map_of_solvable_ker (rootLift_mem_local hF f hf P hP (!b)) a.toMonoidHom
  rw [ha] at hl
  have hn : (rootLift f (!b)).map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply rootLift_ne_top hF f hf (!b)
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    simpa only [map_top_of_surjective a.toMonoidHom a.surjective] using ht
  obtain ⟨d,hd⟩ := local_eq_rootLift hF f hf P hP hk htop hl hn
  have hdb : d ≠ b := by
    intro he
    have hh := (Subgroup.map_injective (f := a.toMonoidHom) a.injective) ((hd.trans (congrArg (rootLift f) he)).trans hb.symm)
    have hh' := rootLift_injective hF f hf hh
    cases b <;> simp at hh'
  have hd' : d = !b := by cases b <;> cases d <;> simp_all
  exact hd'.symm ▸ hd

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
