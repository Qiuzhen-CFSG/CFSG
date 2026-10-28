module
public import Theory.Representation.NormalComponentConstituents.Homogeneous
public import CFSG.Quasithin.ChapterG.Section10.Components.Exchanged
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType

/-!
# The exchanged pair separates the original component orbit

Every nonzero subspace invariant under H and X contains the original marked
point. The two exchanged constituents contain that point in their sum. If
another irreducible type lay outside their X-orbit, its orbit sum would contain
the same point while belonging to disjoint isotypic components. Thus only the
two exchanged types occur. Faithfulness of the ambient representation then
makes their pair of actions separate all of H, before any properness or
spanning conclusion. This is the separation step needed in the noncentral
kernel branch, not an assertion that H is faithful on either summand.

Source: Aschbacher--Smith G.10.15, printed p.362.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace Representation.BinaryOffender

private theorem simple_pair_disjoint_sum
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A C : Submodule R M) [IsSimpleModule R A] [IsSimpleModule R C]
    {ι : Type*} (B : ι → Submodule R M) (hB : ∀ i, IsSimpleModule R (B i))
    (hneA : ∀ i, ¬ Nonempty (A ≃ₗ[R] B i))
    (hneC : ∀ i, ¬ Nonempty (C ≃ₗ[R] B i)) :
    Disjoint (A ⊔ C) (⨆ i, B i) := by
  classical
  let Q := isotypicComponents R M
  let a : Q := ⟨isotypicComponent R M A, A, inferInstance, rfl⟩
  let c : Q := ⟨isotypicComponent R M C, C, inferInstance, rfl⟩
  let S : Set Q := {a,c}
  let T : Set Q := Sᶜ
  have hi : iSupIndep (fun q : Q => (q : Submodule R M)) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)
  apply (hi.disjoint_biSup_biSup' disjoint_compl_right (Set.toFinite S)).mono
  · apply sup_le
    · exact A.le_isotypicComponent.trans (le_iSup_of_le a (le_iSup_of_le (by simp [S]) le_rfl))
    · exact C.le_isotypicComponent.trans (le_iSup_of_le c (le_iSup_of_le (by simp [S]) le_rfl))
  · apply iSup_le
    intro i
    have := hB i
    let b : Q := ⟨isotypicComponent R M (B i), B i, inferInstance, rfl⟩
    have hne (D : Submodule R M) [IsSimpleModule R D]
        (hD : ¬Nonempty (D ≃ₗ[R] B i)) : isotypicComponent R M D ≠ b.val := by
      intro he
      apply hD
      apply isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M (B i)) D
      change D ≤ b.val
      rw [←he]
      exact D.le_isotypicComponent
    have hb : b ∈ T := by
      change b ∉ S
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun he => hne A (hneA i) (congrArg Subtype.val he).symm,
        fun he => hne C (hneC i) (congrArg Subtype.val he).symm⟩
    exact (B i).le_isotypicComponent.trans (le_biSup (fun q : Q => (q : Submodule R M)) hb)

open Homogeneous

private theorem TypeAction.sameModule_pair_of_common_point
    {E V P : Type*} [Group E] [AddCommGroup V] [Module (ZMod 2) V]
    [Group P] {σ : Representation (ZMod 2) E V}
    (c : TypeAction σ P) (I C : Subrepresentation σ)
    (hI : IsIrreducible I.toRepresentation) (hC : IsIrreducible C.toRepresentation)
    (v : V) (hv0 : v ≠ 0) (hv : v ∈ I.toSubmodule ⊔ C.toSubmodule)
    (hstable : ∀ y : P, (c.conjugate y I = I ∨ c.conjugate y I = C) ∧
      (c.conjugate y C = I ∨ c.conjugate y C = C))
    (hpoint : ∀ N : Subrepresentation σ,
      (∀ y : P, c.conjugate y N = N) → N ≠ ⊥ → v ∈ N.toSubmodule)
    (J : Subrepresentation σ) (hJ : IsIrreducible J.toRepresentation) :
    SameModule I J ∨ SameModule C J := by
  classical
  by_contra! hn
  have hnot (D : Subrepresentation σ) (hD : D = I ∨ D = C) :
      ¬SameModule D J := by rcases hD with rfl|rfl <;> tauto
  have hne (D : Subrepresentation σ) (hD : D=I ∨ D=C) (y : P) :
      ¬SameModule D (c.conjugate y J) := by
    intro he
    have hh := (c.same y⁻¹ D (c.conjugate y J)).mp he
    rw [c.inv_conjugate] at hh
    apply hnot (c.conjugate y⁻¹ D) _ hh
    rcases hD with rfl|rfl
    · exact (hstable y⁻¹).1
    · exact (hstable y⁻¹).2
  let N := c.span J
  have hvN : v ∈ N.toSubmodule := hpoint N (fun y => c.conjugate_span y J) (by
    intro hz
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
      (bot_unique ((c.le_span J).trans hz.le)))
  have := simple_asSubmodule I hI
  have := simple_asSubmodule C hC
  have hd := simple_pair_disjoint_sum I.asSubmodule C.asSubmodule
    (fun y : P => (c.conjugate y J).asSubmodule)
    (fun y => simple_asSubmodule _ (c.conjugate_irreducible J hJ y))
    (fun y he => hne I (Or.inl rfl) y ((sameModule_iff_linearEquiv _ _).mpr he))
    (fun y he => hne C (Or.inr rfl) y ((sameModule_iff_linearEquiv _ _).mpr he))
  let e : Subrepresentation σ ≃o Submodule (ZMod 2)[E] (asModule σ) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have he : N.asSubmodule = ⨆ y : P, (c.conjugate y J).asSubmodule :=
    e.map_iSup (fun y : P => c.conjugate y J)
  have hvpair : (asModuleEquiv σ).symm v ∈ I.asSubmodule ⊔ C.asSubmodule := by
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hv
    exact Submodule.mem_sup.mpr ⟨(asModuleEquiv σ).symm a,ha,(asModuleEquiv σ).symm b,hb,by
      simpa only [map_add] using congrArg (asModuleEquiv σ).symm hab⟩
  have hvN' : (asModuleEquiv σ).symm v ∈ ⨆ y : P, (c.conjugate y J).asSubmodule :=
    he ▸ hvN
  exact hv0 (congrArg (asModuleEquiv σ)
    (Submodule.disjoint_def.mp hd _ hvpair hvN'))

private theorem faithful_pair_of_sameModule
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (H : Subgroup G) [H.Normal]
    (I C : Subrepresentation (ρ.comp H.subtype))
    (hI : IsIrreducible I.toRepresentation)
    (htypes : ∀ J : Subrepresentation (ρ.comp H.subtype),
      IsIrreducible J.toRepresentation → SameModule I J ∨ SameModule C J) :
    ∀ a : H, I.toRepresentation a = 1 → C.toRepresentation a = 1 → a = 1 := by
  intro a haI haC
  have hfix (J : Subrepresentation (ρ.comp H.subtype))
      (hJ : IsIrreducible J.toRepresentation) (w : V) (hw : w ∈ J.toSubmodule) :
      ρ (a : G) w = w := by
    have he (D : Subrepresentation (ρ.comp H.subtype)) (heq : D.toRepresentation a = 1)
        (hDJ : SameModule D J) : ρ (a : G) w = w := by
      obtain ⟨e,he⟩ := hDJ
      obtain ⟨u,hu⟩ := e.surjective (⟨w,hw⟩ : J.toSubmodule)
      have hu' : D.toRepresentation a u = u := congrArg (fun f => f u) heq
      have hh : e u = J.toRepresentation a (e u) :=
        (congrArg e hu').symm.trans (he a u)
      rw [hu] at hh
      exact (congrArg Subtype.val hh).symm
    rcases htypes J hJ with h | h
    · exact he I haI h
    · exact he C haC h
  have hs : (⨆ g : G, (conjugateSubrepresentation ρ H I g).toSubmodule) = ⊤ := by
    rw [← toSubmodule_iSup]
    exact congrArg (fun J : Subrepresentation (ρ.comp H.subtype) => J.toSubmodule)
      (iSup_conjugateSubrepresentations_eq_top ρ H hi I hI)
  have hk : (⊤ : Submodule (ZMod 2) V) ≤ (ρ (a : G) - LinearMap.id).ker := by
    rw [←hs]
    refine iSup_le fun g => ?_
    have hJ : IsIrreducible (conjugateSubrepresentation ρ H I g).toRepresentation := by
      apply (Subrepresentation.irreducible_iff_isAtom _).mpr
      simpa only [conjugateSubrepresentationOrderIso_apply,inv_inv] using
        ((conjugateSubrepresentationOrderIso ρ H g⁻¹).isAtom_iff I).mpr
          ((Subrepresentation.irreducible_iff_isAtom I).mp hI)
    intro w hw
    exact sub_eq_zero.mpr (hfix _ hJ w hw)
  apply Subtype.ext
  apply hf
  ext w
  simpa only [Subgroup.coe_one,map_one,Module.End.one_apply,LinearMap.id_apply] using
    sub_eq_zero.mp (hk Submodule.mem_top)

end Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
open Representation.BinaryOffender.Homogeneous Theory.GroupTheory
open scoped IsMulCommutative
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The original two exchanged actions jointly separate the whole normal orbit. -/
theorem exchanged_pair_separates (hn : ¬Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I) (hv : v ∉ I) :
    ∃ x : X, I.map (ρ x) ≠ I ∧
      let H := componentOrbit L ⊤
      letI : H.Normal := componentOrbit_top_normal L
      let R := invariantSubspace ρ H I hI.invariant
      let C := conjugateSubrepresentationOrderIso ρ H (x:G) R
      ∀ a : H, R.toRepresentation a = 1 → C.toRepresentation a = 1 → a = 1 := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let R := invariantSubspace ρ H I hI.invariant
  obtain ⟨x,hx,hop,hdis,hindex,i,hi0,hvi,hiW,hcenter⟩ :=
    h.exchanged_constituent_geometry hn hL hm S hnX hind hI hv
  let c := subgroupTypeAction ρ H X
  let C := c.conjugate x R
  have hR : IsIrreducible R.toRepresentation :=
    hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H
  have hC := c.conjugate_irreducible R hR x
  have hc (z : X) : (c.conjugate z R).toSubmodule = I.map (ρ z) :=
    conjugateSubrepresentationOrderIso_toSubmodule ρ H z R
  have hstable (y : X) : (c.conjugate y R = R ∨ c.conjugate y R = C) ∧
      (c.conjugate y C = R ∨ c.conjugate y C = C) := by
    have hfirst (z : X) : c.conjugate z R = R ∨ c.conjugate z R = C := by
      have hh := h.independent_orbit_eq_self_or_moving I
        (by have := hI.isIrrPlus.finrank_gt_two ρ H; omega)
        (hI.independent_orbit_of_fixedSpace_eq_bot ρ
          (fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
            (h.irreducible_of_not_solvable hn) H hL.componentOrbit_top_ne_bot)) x hx z
      rcases hh with hh|hh
      · exact Or.inl (Subrepresentation.toSubmodule_injective ((hc z).trans hh))
      · exact Or.inr (Subrepresentation.toSubmodule_injective ((hc z).trans (hh.trans (hc x).symm)))
    refine ⟨hfirst y,?_⟩
    have he : c.conjugate y C = c.conjugate x (c.conjugate y R) := by
      change c.conjugate y (c.conjugate x R) = _
      rw [←c.mul,←c.mul,mul_comm y x]
    rw [he]
    rcases hfirst y with hy|hy
    · exact Or.inr (congrArg (c.conjugate x) hy)
    · left
      rw [hy]
      change c.conjugate x (c.conjugate x R) = R
      have hx2 : x*x=1 := by
        apply Subtype.ext
        simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:G) x.property
      rw [←c.mul,hx2,c.one]
  have htypes (J : Subrepresentation (ρ.comp H.subtype))
      (hJ : IsIrreducible J.toRepresentation) : SameModule R J ∨ SameModule C J := by
    apply TypeAction.sameModule_pair_of_common_point c R C hR hC v h.point_ne_zero
      (show v ∈ R.toSubmodule ⊔ C.toSubmodule from
        hvi ▸ Submodule.add_mem_sup i.property.1 (by
          rw [show C.toSubmodule = I.map (ρ x) from hc x]
          exact Submodule.mem_map_of_mem i.property.1))
      hstable _ J hJ
    intro N hN hN0
    apply h.point_mem_normal_component_subspace hn hL hm S hnX hind N.toSubmodule
      (le_subspaceStabilizer ρ N.toSubmodule (fun a ha u hu => N.apply_mem_toSubmodule ⟨a,ha⟩ hu))
    · intro y hy
      apply (subspace_map_eq_iff ρ N.toSubmodule y).mp
      simpa only [c,subgroupTypeAction,normalTypeAction,
        conjugateSubrepresentationOrderIso_toSubmodule] using
        congrArg Subrepresentation.toSubmodule (hN ⟨y,hy⟩)
    · exact fun he => hN0 (Subrepresentation.toSubmodule_injective he)
  exact ⟨x,hx,faithful_pair_of_sameModule ρ h.faithful
    (h.irreducible_of_not_solvable hn) H R C hR htypes⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
