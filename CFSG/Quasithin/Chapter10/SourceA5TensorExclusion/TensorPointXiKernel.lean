module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointResidual
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import Theory.GroupTheory.CComponent.SolvablePerfectKernel
public import Theory.GroupTheory.PResidual.PerfectLift

/-!
# The actual radical factor centralizes the reduced center orbit

Let I be the containing C-component at a nonsingular tensor point, and put
H = I C_T(v). If I and the diagonal point residual have the same nontrivial
image in H/C_H(W), every odd radical factor Ξ_p(I) centralizes W.

The literal diagonal residual is perfect: its A₅ quotient has a two-group
kernel and the residual is two-perfect. Restrict the original quotient map
to I and corestrict to its image. The diagonal residual covers that image.
C-component minimality makes the action kernel solvable, so the general
simple-two-core-cover lemma kills the image of the normal solvable
two-perfect subgroup Ξ_p(I). Membership in the actual centralizer quotient
kernel then gives centralization of the original ambient image of W.

The preceding point-movement theorem supplies nontriviality of the image;
no replacement action or normalization of the diagonal residual by I is
assumed. Source: Aschbacher–Smith 9.4.1, printed pp.735–736.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
open Chapter1 ChapterB.InternalThompsonAction

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual diagonal residual is perfect, using its two-perfectness
and the literal A₅ quotient with two-group kernel. -/
theorem tensorPointResidual_isPerfect (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    Group.IsPerfect (m.tensorPointResidual v) := by
  let f := (m.tensorPointResidualA5Equiv v hv).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 (m.tensorPointResidual v)))
  have hf : Function.Surjective f := (m.tensorPointResidualA5Equiv v hv).surjective.comp
    (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  apply (m.tensorPointResidual_isPPerfect v).isPerfect_of_surjective_pGroup_kernel f hf
  dsimp only [f]
  rw [MonoidHom.ker_comp_of_injective _ _ (m.tensorPointResidualA5Equiv v hv).injective,
    QuotientGroup.ker_mk']
  exact pCore_isPGroup

/-- Equality of the original component and diagonal-residual action images
places each odd radical factor in the original center-orbit centralizer. -/
theorem tensorPoint_XiP_le_centralizer_of_image_eq
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hBI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (W : Subgroup (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) : Subgroup G))
    [W.Normal]
    (heq : (I.subgroupOf (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W) =
      ((m.tensorPointResidual v).subgroupOf
        (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W))
    (hnonzero : ((m.tensorPointResidual v).subgroupOf
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W) ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    XiP p I ≤ centralizer (W.map
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))).subtype : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  let H := I ⊔ R
  let K := I.subgroupOf H
  let q := actionMk W
  let A := K.map q
  have hA : A ≠ ⊥ := by
    change K.map q ≠ ⊥
    rw [heq]
    exact hnonzero
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  let i : I →* H := inclusion (show I ≤ H from le_sup_left)
  let f : I →* A := (q.comp i).codRestrict A
    (fun x => mem_map_of_mem q (show i x ∈ K from x.property))
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨k, hk, hka⟩ := ha
    refine ⟨⟨k, hk⟩, ?_⟩
    exact Subtype.ext hka
  have htop : (⊤ : Subgroup I).IsCComponent := by
    have h := hI.subgroupOf le_rfl
    rw [subgroupOf_self] at h
    let j := subgroupOfEquivOfLe hIX
    have hm := h.map_equiv j
    rwa [map_top_of_surjective j.toMonoidHom j.surjective] at hm
  let B := (m.tensorPointResidual v).subgroupOf I
  let eB := subgroupOfEquivOfLe hBI
  let : Group.IsPerfect (m.tensorPointResidual v) := m.tensorPointResidual_isPerfect v hv
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  let qB := eB.toMonoidHom.pCoreQuotientEquiv (p := 2) eB.surjective
    (by rw [eB.toMonoidHom.ker_eq_bot eB.injective]; exact IsPGroup.of_bot)
  let e5 := qB.trans (m.tensorPointResidualA5Equiv v hv)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e5.isSimpleGroup
  have hB : B.map f = ⊤ := by
    apply top_unique
    intro a _
    have ha : (a : ActionQuotient W) ∈
        ((m.tensorPointResidual v).subgroupOf H).map q := heq ▸ a.property
    obtain ⟨b, hb, hba⟩ := ha
    refine ⟨⟨b, hBI hb⟩, hb, ?_⟩
    exact Subtype.ext hba
  let X := (XiP p I).subgroupOf I
  let eX := subgroupOfEquivOfLe (XiP_le p I)
  let : Group.IsSolvable (XiP p I) := RadicalNormalizers.XiP_solvable p ho I
  let : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := eX.symm.toMonoidHom) eX.symm.surjective
  let : X.Normal := inferInstance
  have hXP : IsPPerfect 2 X := (XiP_isPPerfect p I).of_surjective
    eX.symm.toMonoidHom eX.symm.surjective
  have hkernel := solvable_twoPerfect_le_kernel_of_simple_twoCore_cover htop f hf B hB X hXP
  intro x hx
  have hxI : x ∈ I := XiP_le p I hx
  have hk : f ⟨x, hxI⟩ = 1 := hkernel hx
  have hq : q (i ⟨x, hxI⟩) = 1 := congrArg Subtype.val hk
  have hc : i ⟨x, hxI⟩ ∈ centralizer (W : Set H) :=
    (QuotientGroup.eq_one_iff _).mp hq
  intro w hw
  obtain ⟨w, hw, rfl⟩ := hw
  exact congrArg H.subtype (hc w hw)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
